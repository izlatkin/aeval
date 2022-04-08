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
      // outs () << "   >>  cover: " << tr << ", " << c << ", " << chc.covered.size() << "/" << chc.bodies.size() << "\n";

      for (int i = 0; i < chc.bodies.size(); i++)
      {
        Expr b = chc.bodies[i];
        if (find(chc.covered.begin(), chc.covered.end(), i) == chc.covered.end())
        {
          if (!chc.isQuery)
          {
            b = replaceAll(b, chc.dstVars, bindVars[tr]);
            for (auto v : bindVars[tr])
              b = replaceAll(b, v, u.getModel(v));
          }
          if (!chc.isFact)
          {
            b = replaceAll(b, chc.srcVars, bindVars[tr-1]);
            for (auto v : bindVars[tr-1])
              b = replaceAll(b, v, u.getModel(v));
          }

          b = replaceAll(b, chc.locVars, bindLocVars[tr]);
          for (auto v : bindLocVars[tr])
            b = replaceAll(b, v, u.getModel(v));

          SMTUtils u2(m_efac);
          if (u2.isSat(b))
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
                 ruleManager.chcs[a.back()].srcRelation) == ruleManager.loopheads.end())
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

    vector<vector<int>> consideredThisRound;
    bool getNext(vector<vector<int>> & cntr, vector<int> &n)
    {
      int curMax = 0;
      for (int i = cntr.size() - 1; i >= 0; i --)
      {
        int cur = 0;
        auto & g = cntr[i];

        if (find(consideredThisRound.begin(), consideredThisRound.end(), g) !=
                 consideredThisRound.end()) continue;

        if (already_unsat(g))
        {
          cntr.erase(find(cntr.begin(), cntr.end(), g));
          continue;
        }
        for (auto i : g) cur += weight(i);
        if (cur > curMax)
        {
          n = g;
          curMax = cur;
        }
      }
      consideredThisRound.push_back(n);
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
        auto f = find(cntr.begin(), cntr.end(), g);
        if (f != cntr.end()) cntr.erase(f);
        pruneLast(g);
        unique_push_back(g, prio2);
      }
      else
      {
        outs () << "Rem TODOs: " << todoCHCs.size() << "    (sz = " << g.size() << ")" << "\n";
        outs ().flush();
        pruneLast(g);
        unique_push_back(g, prio1);
      }

      if (tot > 0)
        if (getTest(false)) printTest();
    }

    void oneRound(vector<vector<int>> & cntr, vector<vector<int>> & prio1,
                  vector<vector<int>>& prio2, vector<vector<int>>& prio3)
    {
      int sz;
      outs() << "cntr sz = " << cntr.size() << "\n";
      consideredThisRound.clear();
      while (true)
      {
        vector<int> g;
        if (!getNext(cntr, g)) break;

        ExprVector ssa;
        getSSA(g, ssa);
        auto res = u.isSatIncrem(ssa, sz);
        if (true == res)
        {
          success(g, cntr, prio1, prio2);
        }
        else if (false == res)
        {
          cntr.erase(find(cntr.begin(), cntr.end(), g));

          if (sz > 0)
          {
            if (ruleManager.chcs[g[sz-1]].isQuery)
            {
              auto h = g;
              h.resize(sz-1);
              ssa.resize(sz-1);
              u.isSat(ssa);            // need to re-solve. to optimize
              success(h, cntr, prio1, prio2);
            }
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

    void exploreRec(vector<vector<int>> & traces, int lvl, string name, int batch = 50)
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
    void findEmptyLoops()
    {
      for (auto & a : ruleManager.cycles)
      {
        for(auto t : a.second)
        {
          auto e = toExpr(t);
          auto & v1 = ruleManager.chcs[t[0]].srcVars;
          auto & v2 = bindVars.back();
          assert(v1.size() == v2.size());
          ExprVector tmp;
          for (int i = 0; i < v1.size(); i++)
            tmp.push_back(mk<EQ>(v1[i], v2[i]));
          if (u.implies(e, conjoin(tmp, m_efac)))
            emptCycls[t] = true;
        }
      }
    }

    void exploreTracesMaxLb()
    {
      outs () << "LB-MAX\n";
      findEmptyLoops();

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
