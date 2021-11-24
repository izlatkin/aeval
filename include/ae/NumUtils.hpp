#ifndef NUMUTILS__HPP__
#define NUMUTILS__HPP__
#include <assert.h>

using namespace std;

namespace ufo
{
  typedef map<int,set<int>> mmtree;

  void closure(int n, mmtree& t, set<int>& r)
  {
    for (auto a : t[n])
    {
      r.insert(a);
      closure(a, t, r);
    }
  }
}
#endif
