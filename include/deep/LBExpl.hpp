#ifndef LBEXPL__HPP__
#define LBEXPL__HPP__

#include "BndExpl.hpp"

using namespace std;
using namespace boost;
namespace ufo
{
  class LBExpl : public BndExpl
  {
    protected:
    //

    public:

    LBExpl (CHCs& r, int l, bool d = false) : BndExpl(r, l, d) {}

    bool checkCovered(int tr, int c, int &tot)
    {
      auto & chc = ruleManager.chcs[c];
      if (chc.bodies.size() <= 1)
      {
        tot++;
        return true;
      }

      for (int i = 0; i < chc.bodies.size(); i++)
      {
        Expr b = chc.bodies[i];
        if (find(chc.covered.begin(), chc.covered.end(), i) == chc.covered.end())
        {
          if (!chc.isQuery)
            b = replaceAll(b, chc.dstVars, bindVars[tr]);
          if (!chc.isFact)
            b = replaceAll(b, chc.srcVars, bindVars[tr-1]);

          b = replaceAll(b, chc.locVars, bindLocVars[tr]);
          if (bool(u.eval(b)))
          {
            bodiesCnjs.push_back(chc.bodies[i]);
            chc.covered.push_back(i);
            tot++;
          }
        }
      }
      return chc.covered.size() == chc.bodies.size();
    }

    set<int> todoCHCs;
    void fillTodos()
    {
      // get points of control-flow divergence
      for (auto & d : ruleManager.decls)
        if (ruleManager.outgs[d->left()].size() > 1)
          for (auto & o : ruleManager.outgs[d->left()])
            todoCHCs.insert(o);

      // add bodies with disjs
      for (int i = 0; i < ruleManager.chcs.size(); i++)
        if (ruleManager.chcs[i].bodies.size() > 1)
        {
          // outs () << "    Hyper egde detected: " << i << "\n";
          todoCHCs.insert(i);
        }

      // if the code is straight, just add queries
      if (todoCHCs.empty())
        for (int i = 0; i < ruleManager.chcs.size(); i++)
          if (ruleManager.chcs[i].isQuery)
            todoCHCs.insert(i);
    }

    int getNumUnvis(vector<int> &g)
    {
      int n = 0;
      for (auto i : g)
        if (find(todoCHCs.begin(), todoCHCs.end(), i) != todoCHCs.end())
          n++;
      return n;
    }

    void unroll(vector<int> &o, vector<vector<int>> &n)
    {
      for (Expr l : ruleManager.loopheads)
      {
        for (int i = o.size() - 1; i >= 0; i--)
        {
          if (ruleManager.chcs[o[i]].dstRelation == l)
          {
            for (auto & a : ruleManager.cycles[l])
            {
              if (emptCycls[a])
              {
                if (emptCyclsVisited[a]) continue;
                else emptCyclsVisited[a] = true;   // unroll only once
              }
              vector<int> nn = o;
              nn.insert(nn.begin()+i+1, a.begin(), a.end());
              if (getNumUnvis(nn) == 0) continue;
              unique_push_back(nn, n);
            }
            break; // experiment: exit early, unroll only at the end
          }
        }
      }
    }

    void pruneLast(vector<int> &a)
    {
      while (!a.empty())
      {
        if (find(todoCHCs.begin(), todoCHCs.end(), a.back()) == todoCHCs.end() &&
            find(ruleManager.loopheads.begin(), ruleManager.loopheads.end(),
                 ruleManager.chcs[a.back()].dstRelation) == ruleManager.loopheads.end())
          a.pop_back();
        else break;
      }
    }

    int weight(int i)
    {
      if (find(todoCHCs.begin(), todoCHCs.end(), i) == todoCHCs.end())
        return 0;
      return 1;
      // TODO:  if (chc.bodies.size() > 1) return....
      // TODO: num of conjuncts
    }

    void print(vector<int> &g)
    {
      outs () << "  ";
      for (auto f : g)
        outs () << "  " << ruleManager.chcs[f].dstRelation << "("
                        << ruleManager.chcs[f].covered.size() << "/"
                        << ruleManager.chcs[f].bodies.size() << ")" << " -> ";
      outs () << "\n";
    }

    bool getNext(vector<vector<int>> & cntr, vector<vector<int>>::iterator & n)
    {
      int curMax = 0;
      for (auto it = cntr.begin(); it != cntr.end();)
      {
        int cur = 0;
        auto & g = *it;

        if (already_unsat(g))
        {
          it = cntr.erase(it);
          continue;
        }
        for (auto i : g) cur += weight(i);
        if (cur > curMax)
        {
          n = it;
          curMax = cur;
        }
        ++it;
      }
      return curMax > 0;
    }

    void success(vector<int>& g, vector<vector<int>> & cntr, vector<vector<int>> & prio1,
                                 vector<vector<int>> & prio2)
    {
      int rem = todoCHCs.size();
      int tot = 0;
      for (int i = 0; i < g.size(); i++)
        if (find(todoCHCs.begin(), todoCHCs.end(), g[i]) != todoCHCs.end())
          if (checkCovered(i, g[i], tot))
            todoCHCs.erase(g[i]);
      if (rem == todoCHCs.size())
      {
        pruneLast(g);
        unique_push_back(g, prio2);
      }
      else
      {
        outs () << "Rem TODOs: " << todoCHCs.size()
                << "    (sz = " << g.size() << ")" << "\n";
        auto f = find(cntr.begin(), cntr.end(), g);
        if (f != cntr.end()) cntr.erase(f);
        pruneLast(g);
        unique_push_back(g, prio1);
      }

      if (tot > 0)
        if (getTest(false)) printTest();
    }

    Expr addDisjContr (vector<int> & g)
    {
      ExprVector blocked;
      for (int s = 0; s < g.size(); s++)
      {
        auto & chc = ruleManager.chcs[g[s]];
        if (chc.bodiesSz > 1)
        {
          ExprVector varsToDisable;
          for (int i = chc.locVars.size() - chc.bodiesSz, j = 0;
                   i < chc.locVars.size(); i++, j++)
            if (find(chc.covered.begin(), chc.covered.end(), j) !=
                                          chc.covered.end())
              varsToDisable.push_back(mk<NEG>(bindLocVars[s][i]));

          if (!varsToDisable.empty())
            blocked.push_back(conjoin(varsToDisable, m_efac));
        }
      }
      if (blocked.empty()) return NULL;
      return disjoin(blocked, m_efac);
    }

    void oneRound(vector<vector<int>> & cntr, vector<vector<int>> & prio1,
                  vector<vector<int>>& prio2, vector<vector<int>>& prio3)
    {
      int sz;
      while (true)
      {
        vector<vector<int>>::iterator git;
        if (!getNext(cntr, git)) break;
        vector<int> g = *git;

        ExprVector ssa;
        getSSA(g, ssa);
        Expr tmp = addDisjContr(g);
        bool added = tmp != NULL;
        if (added) ssa.push_back(tmp);;

        auto res = u.isSatIncrem(ssa, sz);
        if (true == res)
        {
          success(g, cntr, prio1, prio2);
        }
        else if (false == res)
        {
          cntr.erase(git);
          if (sz > 0)
          {
            if (ruleManager.chcs[g.back()].isQuery)
            {
              auto h = g;
              h.resize(g.size()-1);
              if (true == u.reSolve(added ? 2 : 1))
                success(h, cntr, prio1, prio2);
            }
            if (!added)
              if (ruleManager.chcs[g[sz-1]].bodies.size() <= 1 ||
                  ruleManager.chcs[g[sz-1]].covered.size() == 0)
              {
                g.resize(sz);
                unsat_prefs.insert(g);
              }

            pruneLast(g);
            unique_push_back(g, prio3);
          }
        }
        else
        {
          if (debug) assert(0 && "indeterminate");
        }
      }

      vector<vector<int>> tmp;
      for (auto & a : cntr)
      {
        pruneLast(a);
        unique_push_back(a, tmp);
      }
      cntr = tmp;
    }

    void exploreRec(vector<vector<int>> & traces, int lvl, string name, int batch = 20)
    {
      int it = 0;
      while (it < traces.size())
      {
        outs () << "entering lvl: " << lvl << ", \"" << name << "\", batch " << it << "\n";
        vector<vector<int>> traces_prt;

        if (lvl == 0)
        {
          traces_prt = traces;
          it = traces.size();
        }
        else
          for (int j = 0; j < batch && it < traces.size(); it++, j++)
            unroll(traces[it], traces_prt);

        outs () << "considering " << traces_prt.size() << " traces\n";

        vector<vector<int>> traces_prio, traces_unsat_cond, traces_unsat;
        oneRound(traces_prt, traces_prio, traces_unsat_cond, traces_unsat);

        // rec.calls :
        exploreRec(traces_prio, lvl + 1, "prio sats");
        exploreRec(traces_prt, lvl + 1, "next");
        exploreRec(traces_unsat_cond, lvl + 1, "unsats cond");
        exploreRec(traces_unsat, lvl + 1, "unsats");

        outs () << "exiting lvl: " << lvl << "\n";
      }
    }

    map<vector<int>, bool> emptCycls, emptCyclsVisited;
    void findUselessPaths()
    {
      outs () << "total for global: " << ruleManager.acyclic.size() << "\n";
      for (auto it = ruleManager.acyclic.begin(); it != ruleManager.acyclic.end(); )
      {
        auto & t = *it;
        int i = 0;
        int j = 0;
        bool unsat = false;
        while (j < t.size() && !unsat)
        {
          bool lhfound = false;
          for (Expr l : ruleManager.loopheads)
          {
            if (ruleManager.chcs[t[j]].dstRelation == l || j == t.size() - 1)
            {
              vector<int> tmp;
              for (int k = i; k <= j; k++) tmp.push_back(t[k]);
              ExprVector ssa;
              getSSA(tmp, ssa);
              int sz;
              if (false == u.isSatIncrem(ssa, sz)) unsat = true;
              lhfound = true;
              break;
            }
          }
          if (lhfound) i = j + 1;
          j++;
        }
        if (unsat) it = ruleManager.acyclic.erase(it);
        else ++it;
      }

      outs () << "upd for global: " << ruleManager.acyclic.size() << "\n";

      for (auto & a : ruleManager.cycles)
      {
        outs () << "total for " << a.first << ": " << a.second.size() << "\n";
        for (auto it = a.second.begin(); it != a.second.end(); )
        {
          auto & t = *it;
          ExprVector ssa;
          getSSA(t, ssa);
          auto & v1 = ruleManager.chcs[t[0]].srcVars;
          auto & v2 = bindVars.back();
          assert(v1.size() == v2.size());
          ExprVector tmp;
          for (int i = 0; i < v1.size(); i++)
            tmp.push_back(mk<EQ>(v1[i], v2[i]));
          ssa.push_back(mk<NEG>(conjoin(tmp, m_efac)));

          int sz;
          auto res = u.isSatIncrem(ssa, sz);
          if (res == false)
          {
            if (sz == ssa.size()) emptCycls[t] = true;
            else
            {
              it = a.second.erase(it);
              continue;
            }
          }
          it++;
        }
        outs () << "upd for " << a.first << ": " << a.second.size() << "\n";
      }
    }

    void exploreTracesMaxLb()
    {
      outs () << "LB-MAX\n";
      findUselessPaths();

      fillTodos();
      outs () << "Total TODOs: " << todoCHCs.size() << "\n";
      exploreRec(ruleManager.acyclic, 0, "init");
    }

    // original version; similar to TACAS'22
    void exploreTracesLBTG(int cur_bnd, int bnd)
    {
      outs () << "exploreTracesLBTG\n";
      fillTodos();

      while (cur_bnd <= bnd && !todoCHCs.empty())
      {
        outs () << "new iter with cur_bnd = "<< cur_bnd <<"\n";
        set<int> toErCHCs;
        for (auto & a : todoCHCs)
        {
          if (find(toErCHCs.begin(), toErCHCs.end(), a) != toErCHCs.end())
            continue;
          vector<vector<int>> traces;
          getAllTracesTG(mk<TRUE>(m_efac), a, cur_bnd, vector<int>(), traces);
          outs () << "  exploring traces (" << traces.size() << ") of length "
                  << cur_bnd << ";       # of todos = "
                  << (todoCHCs.size() - toErCHCs.size()) << "\n";

          int tot = 0;
          bool toBreak = false;
          for (int trNum = 0; trNum < traces.size() && !todoCHCs.empty() && !toBreak; )
          {
            auto & t = traces[trNum];
            set<int> apps;
            for (int i = 0; i < t.size(); i++)
              if (find(todoCHCs.begin(), todoCHCs.end(), t[i]) != todoCHCs.end() &&
                  find(toErCHCs.begin(), toErCHCs.end(), t[i]) == toErCHCs.end())
                apps.insert(i);
            if (apps.empty())
            {
              trNum++;
              continue;  // should not happen
            }
            tot++;

            auto & hr = ruleManager.chcs[t.back()];
            Expr lms = invs[hr.srcRelation];
            if (lms != NULL && (bool)u.isFalse(mk<AND>(lms, hr.body)))
            {
              outs () << "\n    unreachable: " << t.back() << "\n";
              toErCHCs.insert(t.back());
              unreach_chcs.insert(t.back());
              unsat_prefs.insert(t);
              trNum++;
              continue;
            }

            if (bool(u.isSat(toExpr(t))))
            {
              bodiesCnjs.clear();
              int tot = 0;
              for (auto & b : apps)
                if (checkCovered(b, t[b], tot))
                {
                  toErCHCs.insert(t[b]);
                  if (b == t.size() - 1)
                    toBreak = true;
                }
              if (tot > 0)
                if (getTest()) printTest();
            }
            else
            {
              if (ruleManager.chcs[t.back()].bodies.size() <= 1 ||
                  ruleManager.chcs[t.back()].covered.size() == 0)
                unsat_prefs.insert(t);
              trNum++;
            }
          }
          outs () << "    -> actually explored:  " << tot << ", |unsat prefs| = " << unsat_prefs.size() << "\n";
        }
        for (auto a : toErCHCs) todoCHCs.erase(a);
        cur_bnd++;
      }
      outs () << "Done with LBTG\n";
    }
  };
}

#endif
