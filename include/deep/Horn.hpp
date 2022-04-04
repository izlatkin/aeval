#ifndef HORN__HPP__
#define HORN__HPP__

#include "fstream"
#include "ae/AeValSolver.hpp"
#include "ae/NumUtils.hpp"

using namespace std;
using namespace boost;

namespace ufo
{
  inline bool rewriteHelperConsts(Expr& body, Expr v1, Expr v2)
  {
    if (isOpX<MPZ>(v1))
    {
      body = mk<AND>(body, mk<EQ>(v1, v2));
      return true;
    }
    else if (isOpX<TRUE>(v1))
    {
      body = mk<AND>(body, v2);
      return true;
    }
    else if (isOpX<FALSE>(v1))
    {
      body = mk<AND>(body, mk<NEG>(v2));
      return true;
    }
    return false;
  }

  struct HornRuleExt
  {
    ExprVector srcVars;
    ExprVector dstVars;
    ExprVector locVars;

    Expr body;
    Expr head;

    // for TG:
    ExprVector bodies;
    vector<int> covered;

    Expr srcRelation;
    Expr dstRelation;

    bool isFact;
    bool isQuery;
    bool isInductive;

    void assignVarsAndRewrite (ExprVector& _srcVars, ExprVector& invVarsSrc,
                               ExprVector& _dstVars, ExprVector& invVarsDst, ExprSet& lin)
    {
      for (int i = 0; i < _srcVars.size(); i++)
      {
        srcVars.push_back(invVarsSrc[i]);
        lin.insert(mk<EQ>(_srcVars[i], srcVars[i]));
      }

      for (int i = 0; i < _dstVars.size(); i++)
      {
        dstVars.push_back(invVarsDst[i]);
        lin.insert(mk<EQ>(_dstVars[i], dstVars[i]));
      }
    }

    void shrinkLocVars()
    {
      for (auto it = locVars.begin(); it != locVars.end();)
        if (contains(body, *it)) ++it;
        else it = locVars.erase(it);
    }

    Expr getBody(bool last)
    {
      if (!last || bodies.size() <= 1) return body;

      ExprSet notCovered;
      for (int i = 0; i < bodies.size(); i++)
        if (find(covered.begin(), covered.end(), i) == covered.end())
          notCovered.insert(bodies[i]);
      return disjoin(notCovered, body->getFactory());
    }
  };

  class CHCs
  {
    private:
    set<int> indeces;
    string varname = "_FH_";
    SMTUtils u;

    public:

    ExprFactory &m_efac;
    EZ3 &m_z3;

    Expr failDecl;
    vector<HornRuleExt> chcs, chcsOrig, chcsTmp;
    vector<HornRuleExt*> wtoCHCs;
    ExprVector loopheads;
    ExprSet decls, declsTmp;
    map<Expr, ExprVector> invVars, invVarsPrime;
    map<Expr, vector<int>> outgs;
    map<Expr, bool> hasArrays;
    map<Expr, vector<int>> iterators;
    bool hasAnyArrays;
    int debug;
    set<int> chcsToCheck1, chcsToCheck2, toEraseChcs, redChcs;
    int glob_ind = 0;
    mmtree deps;
    bool cycleSearchDone = false;
    map<Expr, vector<vector<int>>> cycles, prefixes;
    vector<vector<int>> acyclic;
    map<Expr, vector<vector<int>>>::iterator cyclesIt;

    CHCs(ExprFactory &efac, EZ3 &z3, int d = false) :
      u(efac), m_efac(efac), m_z3(z3), hasAnyArrays(false), debug(d) {};

    bool isFapp (Expr e)
    {
      if (isOpX<FAPP>(e))
        if (e->arity() > 0)
          if (isOpX<FDECL>(e->left()))
            if (e->left()->arity() >= 2)
              return true;
      return false;
    }

    bool splitBody (HornRuleExt& hr, ExprVector& srcVars, ExprSet& lin)
    {
      getConj (simplifyBool(hr.body), lin);
      for (auto c = lin.begin(); c != lin.end(); )
      {
        Expr cnj = *c;
        if (isOpX<FAPP>(cnj) && isOpX<FDECL>(cnj->left()) &&
            find(decls.begin(), decls.end(), cnj->left()) != decls.end())
        {
          Expr rel = cnj->left();
          if (hr.srcRelation != NULL)
          {
            errs () << "Nonlinear CHC is currently unsupported: ["
                    << *hr.srcRelation << " /\\ " << *rel->left() << " -> "
                    << *hr.dstRelation << "]\n";
            return false;
          }
          hr.srcRelation = rel->left();
          for (auto it = cnj->args_begin()+1, end = cnj->args_end(); it != end; ++it)
            srcVars.push_back(*it);
          c = lin.erase(c);
        }
        else ++c;
      }
      return true;
    }

    void addDecl (Expr a)
    {
      if (invVars[a->left()].size() == 0)
      {
        decls.insert(a);
        for (int i = 1; i < a->arity()-1; i++)
        {
          Expr new_name = mkTerm<string> (varname + to_string(i - 1), m_efac);
          Expr arg = a->arg(i);
          if (!isOpX<INT_TY> (arg) && !isOpX<REAL_TY> (arg) && !isOpX<BOOL_TY> (arg) && !isOpX<ARRAY_TY> (arg))
          {
            errs() << "Argument #" << i << " of " << a << " is not supported\n";
            exit(1);
          }
          Expr var = fapp (constDecl (new_name, a->arg(i)));
          new_name = mkTerm<string> (lexical_cast<string>(var) + "'", m_efac);
          invVars[a->left()].push_back(var);
          invVarsPrime[a->left()].push_back(cloneVar(var, new_name));
        }
      }
    }

    bool normalize (Expr& r, HornRuleExt& hr)
    {
      r = regularizeQF(r);

      // TODO: support more syntactic replacements
      while (isOpX<FORALL>(r))
      {
        for (int i = 0; i < r->arity() - 1; i++)
        {
          hr.locVars.push_back(bind::fapp(r->arg(i)));
        }
        r = r->last();
      }

      if (isOpX<NEG>(r) && isOpX<EXISTS>(r->first()))
      {
        for (int i = 0; i < r->first()->arity() - 1; i++)
          hr.locVars.push_back(bind::fapp(r->first()->arg(i)));

        r = mk<IMPL>(r->first()->last(), mk<FALSE>(m_efac));
      }

      if (isOpX<NEG>(r))
      {
        r = mk<IMPL>(r->first(), mk<FALSE>(m_efac));
      }
      else if (isOpX<OR>(r) && r->arity() == 2 && isOpX<NEG>(r->left()) && hasUninterp(r->left()))
      {
        r = mk<IMPL>(r->left()->left(), r->right());
      }
      else if (isOpX<OR>(r) && r->arity() == 2 && isOpX<NEG>(r->right()) && hasUninterp(r->right()))
      {
        r = mk<IMPL>(r->right()->left(), r->left());
      }

      if (isOpX<IMPL>(r) && !isFapp(r->right()) && !isOpX<FALSE>(r->right()))
      {
        if (isOpX<TRUE>(r->right()))
        {
          return false;
        }
        r = mk<IMPL>(mk<AND>(r->left(), mk<NEG>(r->right())), mk<FALSE>(m_efac));
      }

      if (!isOpX<IMPL>(r)) r = mk<IMPL>(mk<TRUE>(m_efac), r);

      return true;
    }

    bool parse(string smt, int doElim = 2, bool doArithm = true)
    {
      if (debug > 0) outs () << "\nPARSING" << "\n=======\n";
      std::unique_ptr<ufo::ZFixedPoint <EZ3> > m_fp;
      m_fp.reset (new ZFixedPoint<EZ3> (m_z3));
      ZFixedPoint<EZ3> &fp = *m_fp;
      fp.loadFPfromFile(smt);
      chcs.reserve(fp.m_rules.size());

      for (auto &r: fp.m_rules)
      {
        hasAnyArrays |= containsOp<ARRAY_TY>(r);
        chcs.push_back(HornRuleExt());
        HornRuleExt& hr = chcs.back();

        if (!normalize(r, hr))
        {
          chcs.pop_back();
          continue;
        }

        hr.body = r->left();
        hr.head = r->right();
        if (isOpX<FAPP>(hr.head))
        {
          if (hr.head->left()->arity() == 2 &&
              (find(fp.m_queries.begin(), fp.m_queries.end(), r->right()) !=
               fp.m_queries.end()))
            addFailDecl(hr.head->left()->left());
          else
            addDecl(hr.head->left());
          hr.dstRelation = hr.head->left()->left();
        }
        else
        {
          if (!isOpX<FALSE>(hr.head)) hr.body = mk<AND>(hr.body, mk<NEG>(hr.head));
          addFailDecl(mk<FALSE>(m_efac));
          hr.head = mk<FALSE>(m_efac);
          hr.dstRelation = mk<FALSE>(m_efac);
        }
      }

      if (debug > 0) outs () << "Reserved space for " << chcs.size() << " CHCs and " << decls.size() << " declarations\n";

      bool allGood = true;
      // the second loop is needed because we want to distunguish
      // uninterpreted functions used as variables from relations to be synthesized
      for (auto it = chcs.begin(); it != chcs.end();)
      {
        auto & hr = *it;
        ExprVector origSrcSymbs;
        ExprSet lin;
        if (!splitBody(hr, origSrcSymbs, lin))
        {
          it = chcs.erase(it);
          allGood = false;
          continue;
        }
        if (hr.srcRelation == NULL)
        {
          if (hasUninterp(hr.body))
          {
            errs () << "Unsupported format\n";
            errs () << "   " << *hr.body << "\n";
            exit (1);
          }
          hr.srcRelation = mk<TRUE>(m_efac);
        }

        hr.isFact = isOpX<TRUE>(hr.srcRelation);
        hr.isQuery = (hr.dstRelation == failDecl);
        hr.isInductive = (hr.srcRelation == hr.dstRelation);

        ExprVector origDstSymbs;
        if (!hr.isQuery)
        {
          for (auto it = hr.head->args_begin()+1, end = hr.head->args_end(); it != end; ++it)
            origDstSymbs.push_back(*it);
          hr.head = hr.head->left();
        }

        hr.assignVarsAndRewrite (origSrcSymbs, invVars[hr.srcRelation],
                                 origDstSymbs, invVarsPrime[hr.dstRelation], lin);

        hr.body = conjoin(lin, m_efac);
        chcsOrig.push_back(hr); // reserve copy
        if (doElim >= 1 && !hr.isQuery)
        {
          hr.body = eliminateQuantifiers(hr.body, hr.locVars, doArithm);
          hr.body = u.removeITE(hr.body);
          hr.shrinkLocVars();
        }
        ++it;
      }

      if (debug > 0) outs () << "After parsing: " << chcs.size() << " CHCs and " << decls.size() << " declarations\n";
      if (!allGood) exit(0);

      if (doElim >= 2)
      {
        int sz = chcs.size();
        for (int c = 0; c < chcs.size(); c++)
        {
          chcsToCheck1.insert(c);
          chcsToCheck2.insert(c);
        }
        if (!eliminateDecls()) return false;

        chcsTmp = chcs;
        // eliminating all at once, otherwise elements at chcsToCheck* need updates
        for (auto it = toEraseChcs.rbegin(); it != toEraseChcs.rend(); ++it)
        {
          chcs.erase(chcs.begin() + *it);
        }
        toEraseChcs.clear();
      }
      for (int i = 0; i < chcs.size(); i++)
        outgs[chcs[i].srcRelation].push_back(i);

      if (doElim)
        findCycles();

      if (debug >= 2)
        for (auto & d : decls){
          outs () << "outgs from " << *d->left() << ":\n";
          for (auto & o : outgs[d->left()])
            outs () << "     (" << o << ")  -> " << *chcs[o].dstRelation << "\n"; }

      if (debug >= 2)
      {
        outs () << (doElim ? "  Simplified " : "  Parsed ") << "CHCs:\n";
        print(debug >= 3, true);
      }
      return true;
    }

    void reParse(bool lb = false, bool cycl = true)
    {
      chcs = chcsOrig;
      for (auto it = redChcs.rbegin(); it != redChcs.rend(); ++it)
        if (*it < chcs.size())
          chcs.erase(chcs.begin() + *it);

      decls.insert(declsTmp.begin(), declsTmp.end());

      // actually, add more CHCs
      int sz = chcs.size();
      vector<int> toErase;
      for (int i = 0; i < sz; i++)
      {
        // if (chcs[i].isQuery) continue;
        ExprVector vars2keep;
        u.flatten(chcs[i].body, chcs[i].bodies, false, vars2keep, [](Expr a, ExprVector& b){return a;});
        if (!lb && chcs[i].bodies.size() > 1)
        {
          toErase.push_back(i);
          for (auto & p : chcs[i].bodies)
          {
            auto n = chcs[i];
            n.body = p;
            n.bodies.clear();
            chcs.push_back(n);
          }
          chcs[i].bodies.clear();
        }
      }

      if (cycl)
      {
        for (auto it = toErase.rbegin(); it != toErase.rend(); ++it)
          chcs.erase(chcs.begin() + *it);

        if (debug > 0) outs () << "Contextualized: " << chcs.size()
                            << " CHCs and " << decls.size() << " declarations\n";
        outgs.clear();
        prefixes.clear();
        cycles.clear();

        for (int i = 0; i < chcs.size(); i++)
          outgs[chcs[i].srcRelation].push_back(i);

        findCycles();  // maybe expensive, to optimize

        if (debug >= 2)
          for (auto & d : decls){
            outs () << "outgs from " << *d->left() << ":\n";
            for (auto & o : outgs[d->left()])
              outs () << "     (" << o << ")  -> " << *chcs[o].dstRelation << "\n"; }

        // print(debug >= 3, true);
      }
    }

    void propagateInvs(ExprMap& cands)
    {
      for (auto & i : redChcs)
      {
        set<int> r;
        closure(i, deps, r);
        for (auto j : r) redChcs.insert(j);
      }

      while (!declsTmp.empty())
      {
        int sz = declsTmp.size();
        for (auto d = declsTmp.begin(); d != declsTmp.end(); )
        {
          bool found = true;
          ExprSet invs;
          for (int i = 0; i < chcsTmp.size(); i++)
          {
            auto c = &chcsTmp[i];
            if (c->dstRelation != (*d)->left()) continue;
            if (find(redChcs.begin(), redChcs.end(), i) != redChcs.end())  continue;
            if (c->isFact) invs.insert(c->body);
            else if (cands[c->srcRelation] != NULL)
              invs.insert(mk<AND>(cands[c->srcRelation], c->body));
            else
              found = false;
          }
          if (found)
          {
            Expr inv = keepQuantifiers(disjoin(invs, m_efac), invVarsPrime[(*d)->left()]);
            inv = weakenForHardVars(inv, invVarsPrime[(*d)->left()]);
            cands[(*d)->left()] = replaceAll(inv, invVarsPrime[(*d)->left()], invVars[(*d)->left()]);

            decls.insert(*d);
            d = declsTmp.erase(d);
          }
          else ++d;
        }
        if (sz == declsTmp.size())
        {
//          outs () << "cannot derive; remaining decls ";
//          pprint(declsTmp,2);
          for (auto d : declsTmp) cands[d->left()] = mk<TRUE>(m_efac);
          return;
        }
      }
    }

    bool eliminateTrivTrueOrFalse()
    {
      return true; // disabled for testgen
      set<int> toEraseChcsTmp;
      for (int i = 0; i < chcs.size(); i++)
      {
        if (find(toEraseChcs.begin(), toEraseChcs.end(), i) != toEraseChcs.end()) continue;
        if (find(toEraseChcsTmp.begin(), toEraseChcsTmp.end(), i) != toEraseChcsTmp.end()) continue;

        auto c = &chcs[i];
        if (c->isQuery && !c->isFact)
        {
          auto f = find(chcsToCheck1.begin(), chcsToCheck1.end(), i);
          if (f != chcsToCheck1.end())
          {
            if (u.isTrue(c->body))
            {
              // thus, c->srcRelation should be false
              for (int j = 0; j < chcs.size(); j++)
              {
                if (find(toEraseChcs.begin(), toEraseChcs.end(), j) != toEraseChcs.end()) continue;
                if (find(toEraseChcsTmp.begin(), toEraseChcsTmp.end(), j) != toEraseChcsTmp.end()) continue;

                HornRuleExt* s = &chcs[j];
                if (s->srcRelation == c->srcRelation)
                {
                  // search for vacuous cases where s == inv -> inv2   and   c == inv /\ true -> false
                  // then, inv can only be false, thus s does not give any constraint
                  toEraseChcsTmp.insert(j);  // could erase here, but ther will be a mess with pointers
                }
                else if (s->dstRelation == c->srcRelation)
                {
                  s->isQuery = true;
                  s->dstRelation = failDecl;
                  s->locVars.insert(s->locVars.end(), s->dstVars.begin(), s->dstVars.end());
                  s->dstVars.clear();
                  chcsToCheck1.insert(j);
                  chcsToCheck2.insert(j);
                }
              }
              decls.erase(c->srcRelation);
              declsTmp.insert(c->srcRelation);
            }
            chcsToCheck1.erase(f);
          }
        }
        else if (c->isQuery && c->isFact)
          if (u.isSat(c->body))
          {
            outs () << "Counterexample found (during preprocessing)\n";
            return false;
          }
      }

      if (toEraseChcsTmp.empty()) return true;

      for (auto it = toEraseChcsTmp.rbegin(); it != toEraseChcsTmp.rend(); ++it)
      {
        if (debug >= 2) outs () << "  Eliminating vacuous CHC: " << chcs[*it].srcRelation << " -> " << chcs[*it].dstRelation << "\n";
        if (debug >= 3) outs () << "    its body is true: " << chcs[*it].body << "\n";
        toEraseChcs.insert(*it);
      }

      return eliminateTrivTrueOrFalse();     // recursive call
    }

    bool eliminateDecls()
    {
      int preElim = decls.size();
      if (debug > 0) outs () << "Reducing the number of CHCs: " << (chcs.size() - toEraseChcs.size()) <<
                      "; and the number of declarations: " << decls.size() << "...\n";
      if (debug >= 3)
      {
        outs () << "  Current CHC topology:\n";
        print(false);
      }

      if (!eliminateTrivTrueOrFalse()) return false;        // first, remove relations which are trivially false
                                                            // and find any trivially unsatisfiable queries
      Expr declToRemove = NULL;
      vector<int> srcMax, dstMax;
      set<int> toEraseChcsTmp;

      for (auto d = decls.begin(); d != decls.end();)
      {
        vector<int> src, dst;
        for (int i = 0; i < chcs.size(); i++)
        {
          if (find(toEraseChcs.begin(), toEraseChcs.end(), i) != toEraseChcs.end()) continue;
          if (find(toEraseChcsTmp.begin(), toEraseChcsTmp.end(), i) != toEraseChcsTmp.end()) continue;

          if (chcs[i].srcRelation == (*d)->left()) src.push_back(i);
          if (chcs[i].dstRelation == (*d)->left()) dst.push_back(i);
        }

        if ((src.size() > 0 && dst.size() > 0) &&
            emptyIntersect(src, dst))
        {
          if (declToRemove != NULL)
            if (declToRemove->arity() > (*d)->arity())
              { ++d; continue; }
          if (declToRemove != NULL)
            if (declToRemove->arity() == (*d)->arity() &&
                src.size() * dst.size() > srcMax.size() * dstMax.size())
              { ++d; continue; }

          srcMax = src;
          dstMax = dst;
          declToRemove = *d;
        }

        if (src.size() == 0) // found dangling CHCs
        {
          toEraseChcsTmp.insert(dst.begin(), dst.end());
          declsTmp.insert(*d);
          d = decls.erase(d);
        }
        else ++d;
      }

      // first, it will remove dangling CHCs since it's cheaper
      if (declToRemove != NULL && toEraseChcsTmp.empty())
      {
        for (int i : srcMax)
          for (int j : dstMax)
            concatenateCHCs(i, j);

        toEraseChcsTmp.insert(srcMax.begin(), srcMax.end());
        toEraseChcsTmp.insert(dstMax.begin(), dstMax.end());
        decls.erase(declToRemove);
        declsTmp.insert(declToRemove);
      }

      for (auto a = toEraseChcsTmp.rbegin(); a != toEraseChcsTmp.rend(); ++a)
      {
        if (debug >= 2) outs () << "  Eliminating CHC: " << chcs[*a].srcRelation << " -> " << chcs[*a].dstRelation << "\n";
        toEraseChcs.insert(*a);
      }

      removeTautologies();            // get rid of CHCs that don't add any _new_ constraints
      if (preElim > decls.size())
        return eliminateDecls();
      else
      {
        // currently disabled
//        if (!hasAnyArrays) slice();   // remove unrelated constraints and shrink arities of predicates

        int preComb = (chcs.size() - toEraseChcs.size());
        combineCHCs();
        if (preComb > (chcs.size() - toEraseChcs.size()))
          return eliminateDecls();
      }
      return true;
    }

    void concatenateCHCs(int i, int j)
    {
      for (int k : {i, j}) deps[chcs.size()].insert(k);
      chcs.push_back(HornRuleExt());
      HornRuleExt* s = &chcs[i];
      HornRuleExt* d = &chcs[j];
      HornRuleExt* n = &chcs.back();
      if (debug >= 2)
      {
        outs () << "  Concatenating two CHCs: "
                << d->srcRelation << " -> " << d->dstRelation << " and "
                << s->srcRelation << " -> " << s->dstRelation << "\n";
      }
      n->srcRelation = d->srcRelation;
      n->dstRelation = s->dstRelation;
      n->srcVars = d->srcVars;
      n->dstVars = d->dstVars;

      ExprVector newVars;
      for (int i = 0; i < d->dstVars.size(); i++)
      {
        Expr new_name = mkTerm<string> ("__bnd_var_" + to_string(glob_ind++), m_efac);
        newVars.push_back(cloneVar(d->dstVars[i], new_name));
      }
      Expr mergedBody = replaceAll(s->body, s->srcVars, newVars);
      n->dstVars.insert(n->dstVars.end(), d->locVars.begin(), d->locVars.end());
      for (int i = 0; i < d->locVars.size(); i++)
      {
        Expr new_name = mkTerm<string> ("__loc_var_" + to_string(glob_ind++), m_efac);
        newVars.push_back(cloneVar(d->locVars[i], new_name));
      }
      mergedBody = mk<AND>(replaceAll(d->body, n->dstVars, newVars), mergedBody);
      n->locVars = newVars;
      n->locVars.insert(n->locVars.end(), s->locVars.begin(), s->locVars.end());
      n->body = simpleQE(mergedBody, n->locVars);
      n->shrinkLocVars();
      n->dstVars = s->dstVars;
      n->isInductive = n->srcRelation == n->dstRelation;
      n->isFact = isOpX<TRUE>(n->srcRelation);
      n->isQuery = n->dstRelation == failDecl;

      chcsToCheck1.insert(chcs.size()-1);
      chcsToCheck2.insert(chcs.size()-1);
    }

    void removeTautologies()
    {
      for (int i = 0; i < chcs.size(); i++)
      {
        if (find(toEraseChcs.begin(), toEraseChcs.end(), i) != toEraseChcs.end()) continue;

        auto h = &chcs[i];
        auto f = find(chcsToCheck2.begin(), chcsToCheck2.end(), i);
        if (f != chcsToCheck2.end())
        {
          if (u.isFalse(h->body))
          {
            if (debug >= 2) outs () << "  Eliminating CHC: " << h->srcRelation << " -> " << h->dstRelation << "\n";
            if (debug >= 3) outs () << "    its body is false: " << h->body << "\n";
            toEraseChcs.insert(i);
            continue;
          }
          chcsToCheck2.erase(f);
        }

        bool found = false;
        if (h->isInductive)
        {
          found = true;
          for (int j = 0; j < h->srcVars.size(); j++)
          {
            if (u.isSat(h->body, mkNeg(mk<EQ>(h->srcVars[j], h->dstVars[j]))))
            {
              found = false;
              break;
            }
          }
        }
        if (found)
        {
          if (debug >= 2) outs () << "  Eliminating CHC: " << h->srcRelation << " -> " << h->dstRelation << "\n";
          if (debug >= 3) outs () << "    inductive but does not change vars: " << h->body << "\n";
          toEraseChcs.insert(i);
          redChcs.insert(i);
        }
        else ++h;
      }
    }

    void combineCHCs()
    {
      for (int i = 0; i < chcs.size(); i++)
      {
        if (find(toEraseChcs.begin(), toEraseChcs.end(), i) != toEraseChcs.end()) continue;

        set<int> toComb = {i};
        HornRuleExt& s = chcs[i];
        for (int j = i + 1; j < chcs.size(); j++)
        {
          if (find(toEraseChcs.begin(), toEraseChcs.end(), j) != toEraseChcs.end()) continue;

          HornRuleExt& d = chcs[j];
          if (s.srcRelation == d.srcRelation && s.dstRelation == d.dstRelation)
          {
            for (int k = 0; k < s.srcVars.size(); k++) assert (s.srcVars[k] == d.srcVars[k]);
            for (int k = 0; k < s.dstVars.size(); k++) assert (s.dstVars[k] == d.dstVars[k]);
            toComb.insert(j);
          }
        }
        if (toComb.size() > 1)
        {
          if (debug >= 2)
          {
            outs () << "    Disjoing bodies of " << toComb.size() << " CHCs: "
                    << s.srcRelation << " -> " << s.dstRelation << "\n";
          }
          ExprVector all;
          for (auto it = toComb.rbegin(); it != toComb.rend(); ++it)
          {
            all.push_back(chcs[*it].body);
            if (*it != i)
            {
              toEraseChcs.insert(*it);
              deps[i].insert(*it);
            }
          }
          s.body = distribDisjoin(all, m_efac);
          chcsToCheck1.insert(i);
          chcsToCheck2.insert(i);
          return combineCHCs();
        }
      }
    }

    // (recursive) multi-stage slicing begins here
    set<int> chcsToVisit;
    map<Expr, ExprSet> varsSlice;

    void updateTodo(Expr decl, int num)
    {
      for (int i = 0; i < chcs.size(); i++)
      {
        if (find(toEraseChcs.begin(), toEraseChcs.end(), i) != toEraseChcs.end()) continue;

        if (i != num &&
            !chcs[i].isQuery &&
            (chcs[i].srcRelation == decl || chcs[i].dstRelation == decl))
              chcsToVisit.insert(i);
      }
    }

    void slice()
    {
      chcsToVisit.clear();
      varsSlice.clear();
      // first, compute sets of dependent variables
      for (int i = 0; i < chcs.size(); i++)
      {
        if (find(toEraseChcs.begin(), toEraseChcs.end(), i) != toEraseChcs.end()) continue;

        if (chcs[i].isQuery)
        {
          chcs[i].body = keepQuantifiers(chcs[i].body, chcs[i].srcVars);
          Expr decl = chcs[i].srcRelation;
          filter (chcs[i].body, bind::IsConst(),
            std::inserter (varsSlice[decl], varsSlice[decl].begin ()));
          updateTodo(chcs[i].srcRelation, i);
        }
      }
      while (!chcsToVisit.empty()) slice(*chcsToVisit.begin());

      // now, prepare for variable elimination
      for (auto & d : varsSlice)
      {
//        if (invVars[d.first].size() > d.second.size())
//          outs () << "sliced for " << *d.first << ": " << invVars[d.first].size()
//                  << " -> "    << d.second.size() << "\n";
        ExprSet varsPrime;
        for (auto & v : d.second)
        {
          Expr pr = replaceAll(v, invVars[d.first], invVarsPrime[d.first]);
          varsPrime.insert(pr);
        }

        keepOnly(invVars[d.first], d.second);
        keepOnly(invVarsPrime[d.first], varsPrime);
      }

      // finally, update bodies and variable vectors
      for (int i = 0; i < chcs.size(); i++)
      {
        if (find(toEraseChcs.begin(), toEraseChcs.end(), i) != toEraseChcs.end()) continue;
        auto & c = chcs[i];

        if (u.isFalse(c.body) || u.isTrue(c.body)) continue;

        ExprSet bd;
        getConj(c.body, bd);
        for (auto b = bd.begin(); b != bd.end();)
        {
          if (emptyIntersect(*b, invVars[c.srcRelation]) &&
              emptyIntersect(*b, invVarsPrime[c.dstRelation]))
            b = bd.erase(b);
          else ++b;
        }
        if (!c.isFact) c.srcVars = invVars[c.srcRelation];
        if (!c.isQuery) c.dstVars = invVarsPrime[c.dstRelation];
        c.body = conjoin(bd, m_efac);
      }
    }

    void slice(int num)
    {
      HornRuleExt* hr = &chcs[num];
      assert (!hr->isQuery);
      ExprSet srcCore, dstCore, srcDep, dstDep, varDeps, cnjs;

      if (qeUnsupported(hr->body))
      {
        varDeps.insert(hr->srcVars.begin(), hr->srcVars.end());
        varDeps.insert(hr->locVars.begin(), hr->locVars.end());
        varDeps.insert(hr->dstVars.begin(), hr->dstVars.end());
      }
      else
      {
        varDeps = varsSlice[hr->srcRelation];
        filter (getPrecondition(hr), bind::IsConst(),     // all src vars from the preconditions are dependent
                      std::inserter (varDeps, varDeps.begin ()));

        for (auto & v : varsSlice[hr->dstRelation])
          varDeps.insert(replaceAll(v, invVars[hr->dstRelation], hr->dstVars));

        srcCore = varsSlice[hr->dstRelation];
        dstCore = varDeps;

        getConj(hr->body, cnjs);
        while(true)
        {
          int vars_sz = varDeps.size();
          for (auto & c : cnjs)
          {
            ExprSet varsCnj;
            filter (c, bind::IsConst(),
                          std::inserter (varsCnj, varsCnj.begin ()));
            if (!emptyIntersect(varDeps, varsCnj))
              varDeps.insert(varsCnj.begin(), varsCnj.end());
          }
          if (hr->isInductive)
          {
            for (auto & v : varDeps)
            {
              varDeps.insert(replaceAll(v, hr->dstVars, hr->srcVars));
              varDeps.insert(replaceAll(v, hr->srcVars, hr->dstVars));
            }
          }
          if (vars_sz == varDeps.size()) break;
        }
      }

      bool updateSrc = false;
      bool updateDst = false;
      if (!hr->isFact)
      {
        ExprSet& srcVars = varsSlice[hr->srcRelation];
        for (auto v = varDeps.begin(); v != varDeps.end();)
        {
          if (find(hr->srcVars.begin(), hr->srcVars.end(), *v) != hr->srcVars.end())
          {
            if (find(srcVars.begin(), srcVars.end(), *v) == srcVars.end())
            {
              updateSrc = true;
              srcVars.insert(*v);
            }
            v = varDeps.erase(v);
          }
          else ++v;
        }
      }

      srcDep = varsSlice[hr->srcRelation];
      dstDep = varDeps;

      if (!hr->isQuery)
      {
        ExprSet& dstVars = varsSlice[hr->dstRelation];
        for (auto v = varDeps.begin(); v != varDeps.end();)
        {
          if (find(hr->dstVars.begin(), hr->dstVars.end(), *v) != hr->dstVars.end())
          {
            Expr vp = replaceAll(*v, hr->dstVars, invVars[hr->dstRelation]);
            if (find(dstVars.begin(), dstVars.end(), vp) == dstVars.end())
            {
              updateDst = true;
              dstVars.insert(vp);
            }
            v = varDeps.erase(v);
          }
          else ++v;
        }
      }

      if (!varDeps.empty())
        hr->body = eliminateQuantifiers(hr->body, varDeps, false);

      if (updateSrc) updateTodo(hr->srcRelation, num);
      if (updateDst) updateTodo(hr->dstRelation, num);
      chcsToVisit.erase(num);
    }

    void getAllTraces (Expr src, Expr dst, int len, vector<int> trace,
                  vector<vector<int>>& traces, bool once = false)
    {
      if (len == 1)
      {
        for (auto a : outgs[src])
        {
          if (chcs[a].dstRelation == dst)
          {
            if (once && find(trace.begin(), trace.end(), a) != trace.end())
              continue;
            vector<int> newtrace = trace;
            newtrace.push_back(a);
            traces.push_back(newtrace);
          }
        }
      }
      else
      {
        for (auto a : outgs[src])
        {
          if (once && find(trace.begin(), trace.end(), a) != trace.end())
            continue;
          vector<int> newtrace = trace;
          newtrace.push_back(a);
          getAllTraces(chcs[a].dstRelation, dst, len-1, newtrace, traces, once);
        }
      }
    }

    bool isRelVisited(vector<int>& trace, ExprVector& av, Expr rel)
    {
      for (auto t : trace)
        if (chcs[t].dstRelation == rel)
          return true;
      return find(av.begin(), av.end(), rel) != av.end();
    }

    void getAllAcyclicTraces (Expr src, Expr dst, int len, vector<int> trace,
                  vector<vector<int>>& traces, ExprVector& av)
    {
      if (len == 1)
      {
        for (auto a : outgs[src])
        {
          if (chcs[a].dstRelation == dst)
          {
            vector<int> newtrace = trace;
            newtrace.push_back(a);
            traces.push_back(newtrace);
          }
        }
      }
      else
      {
        for (auto a : outgs[src])
        {
          if (chcs[a].dstRelation == dst ||
              isRelVisited(trace, av, chcs[a].dstRelation))
            continue;
          vector<int> newtrace = trace;
          newtrace.push_back(a);
          getAllAcyclicTraces(chcs[a].dstRelation, dst, len-1, newtrace, traces, av);
        }
      }
    }

    void findCycles()
    {
      ExprVector av;
      ExprVector endRels = {failDecl};
      for (auto & d : decls)
      {
        if (outgs[d->left()].empty())
          endRels.push_back(d->left());

        // heuristics for SeaHorn-encoding:
        if (lexical_cast<string>(d).find(".exit.") !=std::string::npos)
          endRels.push_back(d->left());
      }

      for (auto & r : endRels)
        findCycles(mk<TRUE>(m_efac), r, av);

      outs () << "global traces num: " << acyclic.size() << "\n";
      for (auto & a : cycles)
        outs () << "  traces num for: " << a.first << ": " << a.second.size() << "\n";

      cycleSearchDone = true;
      cyclesIt = cycles.begin();
    }

    bool findCycles(Expr src, Expr dst, ExprVector& avoid)
    {
      if (debug >= 2) outs () << "\nfindCycles:  " << src << " => " << dst << "\n";
      vector<vector<int>> nonCycleTraces;
      ExprVector highLevelRels;
      for (int i = 1; i < chcs.size(); i++)
      {
        if (debug >= 2)
        {
          outs () << ".";
          outs().flush();
        }
        getAllAcyclicTraces(src, dst, i, vector<int>(), nonCycleTraces, avoid);
      }

      bool tracesFound = nonCycleTraces.size() > 0;
      map <Expr, vector<vector<int>>> prefs;
      for (auto & d : nonCycleTraces)
      {
        vector<int> tmp;
        for (auto & chcNum : d)
        {
          if (chcs[chcNum].isQuery) break;      // last iter anyway
          Expr& r = chcs[chcNum].dstRelation;
          tmp.push_back(chcNum);
          if (find(avoid.begin(), avoid.end(), r) == avoid.end())
          {
            prefs[r].push_back(tmp);
            unique_push_back(r, highLevelRels);
          }
        }
      }

      if (tracesFound)
      {
        if (src == dst)
        {
          if (debug)
            outs () << "traces num for " << src << ": " << nonCycleTraces.size() << "\n";
          cycles[src].insert(cycles[src].end(), nonCycleTraces.begin(), nonCycleTraces.end());
        }
        else
        {
          acyclic.insert(acyclic.end(), nonCycleTraces.begin(), nonCycleTraces.end());
        }
      }
      else
      {
        assert(src == dst);
      }

      ExprVector avoid2 = avoid;
      for (auto & d : highLevelRels)
      {
        avoid2.push_back(d);
        bool nestedCycle = findCycles(d, d, avoid2);
        if (nestedCycle)
        {
          prefixes[d] = prefs[d]; // to debug
        }
      }

      // WTO sorting is here now:
      if (tracesFound)
      {
        if (src == dst)
        {
          unique_push_back(src, loopheads);      // could there be duplicates?
          if (debug) outs () << "  loophead found: " << src << "\n";
        }
        else if (debug) outs () << "  global:\n";
      }

      for (auto c : nonCycleTraces)
      {
        if (debug > 5)
        {
          outs () << "    trace: " << chcs[c[0]].srcRelation;
          for (auto h : c)
            outs () << " -> " << chcs[h].dstRelation << " ";
          outs () << "\n";
        }
        else if (debug)
        {
          outs () << "traces num for " << chcs[c[0]].srcRelation << ": "
                  << c.size() << "\n";
        }

        for (auto h : c)
          unique_push_back(&chcs[h], wtoCHCs);
      }

      return tracesFound;
    }

    vector<int> getPrefix(Expr rel) // get only first one; to extend
    {
      assert(!cycles[rel].empty());
      assert(!prefixes[rel].empty());
      vector<int> pref = prefixes[rel][0];
      assert(!pref.empty());
      if (chcs[pref[0]].isFact)
        return pref;
      vector<int> ppref = getPrefix(chcs[pref[0]].srcRelation);
      ppref.insert(ppref.end(), pref.begin(), pref.end());
      return ppref;
    }

    bool hasCycles()
    {
      if (cycleSearchDone) return cycles.size() > 0;
      findCycles();

      // assert (cycles.size() == prefixes.size());
      /*
      if (debug >= 3)
        for (int i = 0; i < cycles.size(); i++)
        {
          auto & c = prefixes[i];
          outs () << "      pref: ";
          for (auto & chcNum : c) outs () << *chcs[chcNum].srcRelation << " -> ";
          outs () << "    [";
          for (auto & chcNum : c) outs () << chcNum << " -> ";
          outs () << "]  ";
          auto & d = cycles[i];
          outs () << "\n      cycle: ";
          for (auto & chcNum : d) outs () << *chcs[chcNum].srcRelation << " -> ";
          outs () << "    [";
          for (auto & chcNum : d) outs () << chcNum << " -> ";
          outs () << "]\n\n";
        }
      */
      return (cycles.size() > 0);
    }

    Expr getNextCycle()
    {
      Expr rel = cyclesIt->first;
      cyclesIt++;
      if (cyclesIt == cycles.end()) cyclesIt = cycles.begin();
      return rel;
    }

    void addFailDecl(Expr decl)
    {
      if (failDecl == NULL)
      {
        failDecl = decl;
      }
      else
      {
        if (failDecl != decl)
        {
          errs () << "Multiple queries are unsupported\n";
          exit (1);
        }
      }
    }

    Expr getPrecondition (HornRuleExt* hr)
    {
      Expr tmp = keepQuantifiers(hr->body, hr->srcVars);
      return weakenForHardVars(tmp, hr->srcVars);
    }

    void print (bool full = false, bool dump_cfg = false)
    {
      std::ofstream enc_chc;
      if (dump_cfg)
      {
        enc_chc.open("chc.dot");
        enc_chc <<("digraph print {\n");
      }
      for (int i = 0; i < chcs.size(); i++)
      {
        if (find(toEraseChcs.begin(), toEraseChcs.end(), i) != toEraseChcs.end())
          continue;
        auto & hr = chcs[i];
        if (full)
        {
          if (hr.isFact) outs() << "  INIT:\n";
          else if (hr.isInductive) outs() << "  TR:\n";
          else if (hr.isQuery) outs() << "  BAD:\n";
          else outs() << "  CHC:\n";
        }

        outs () << "    " << * hr.srcRelation;
        if (full && hr.srcVars.size() > 0)
        {
          outs () << " (";
          pprint(hr.srcVars);
          outs () << ")";
        }
        else outs () << "[#" << hr.srcVars.size() << "]";
        outs () << " -> " << * hr.dstRelation;

        if (full && hr.dstVars.size() > 0)
        {
          outs () << " (";
          pprint(hr.dstVars);
          outs () << ")";
        }
        else outs () << "[#" << hr.dstVars.size() << "]";
        if (full)
        {
          outs() << "\n    body: \n";
          if (treeSize(hr.body) < 1000)
            pprint(hr.body, 4);
          else outs () << " < . . . . too large . . . . >\n";
        }
        else outs() << "\n";
        if (dump_cfg)
        {
          enc_chc << " \"" << hr.srcRelation;
          enc_chc << "\" -> ";
          enc_chc << "\"" << hr.dstRelation;
          enc_chc << "\"\n";
        }
      }
      if (dump_cfg)
      {
        enc_chc <<("}");
        enc_chc.close();
        // this needs a graphiz package installed:
        // system("dot -Tpdf -o chc.pdf chc.dot");
      }
    }
  };
}


#endif
