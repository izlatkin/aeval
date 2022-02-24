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

    bool checkCovered(int tr, int c)
    {
      auto & chc = ruleManager.chcs[c];
      if (chc.bodies.size() <= 1) return true;

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
          if (u2.isSat(b)) chc.covered.push_back(i);
        }
      }

      return chc.covered.size() == chc.bodies.size();
    }

    void exploreTracesLBTG(int cur_bnd, int bnd)
    {
      outs () << "exploreTracesLBTG\n";
      set<int> todoCHCs;

      // get points of control-flow divergence
      for (auto & d : ruleManager.decls)
        if (ruleManager.outgs[d->left()].size() > 1)
          for (auto & o : ruleManager.outgs[d->left()])
            todoCHCs.insert(o);

      // add bodies with disjs
      for (int i = 0; i < ruleManager.chcs.size(); i++)
        if (ruleManager.chcs[i].bodies.size() > 1)
        {
          outs () << "    Hyper egde detected: " << i << "\n";
          todoCHCs.insert(i);
        }

      // if the code is straight, just add queries
      if (todoCHCs.empty())
        for (int i = 0; i < ruleManager.chcs.size(); i++)
          if (ruleManager.chcs[i].isQuery)
            todoCHCs.insert(i);

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

            kVers.clear();
            if (bool(!u.isSat(toExpr(t))))
            {
              if (ruleManager.chcs[t.back()].bodies.size() <= 1)
                unsat_prefs.insert(t);
              trNum++;
            }
            else
            {
              for (auto & b : apps)
                if (checkCovered(b, t[b]))
                {
                  toErCHCs.insert(t[b]);
                  if (b == t.size() - 1)
                    toBreak = true;
                }

              if (getTest(false))
                printTest();
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
