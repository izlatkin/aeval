#include "deep/RndLearnerV3.hpp"

using namespace ufo;
using namespace std;

bool getBoolValue(const char * opt, bool defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc; i++)
  {
    if (strcmp(argv[i], opt) == 0) return true;
  }
  return defValue;
}

char * getStrValue(const char * opt, char * defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      return argv[i+1];
    }
  }
  return defValue;
}

int getIntValue(const char * opt, int defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      char* p;
      int num = strtol(argv[i+1], &p, 10);
      if (*p) return 1;      // if used w/o arg, return boolean
      else return num;
    }
  }
  return defValue;
}
void getStrValues(const char * opt, vector<string> & values, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      values.push_back(string(argv[i+1]));
    }
  }
}

static inline void getNums(set<int>& nums, char * str)
{
  if (str == NULL) return;
  int len = strlen(str);
  char* pch = strchr(str, ',');
  int pos1 = 0;
  int pos2 = 0;
  while (pch != NULL)
  {
    pos2 = pch - str;
    char* substr = (char*)malloc(pos2 - pos1);
    strncpy(substr, str + pos1, pos2 - pos1);
    nums.insert(atoi(substr));
    pch = strchr(pch + 1, ',');
    pos1 = pos2 + 1;
  }
  if (pos1 == len) return;
  char* substr = (char*)malloc(len - pos1);
  strncpy(substr, str + pos1, len - pos1);
  nums.insert(atoi(substr));
}

const char *OPT_HELP = "--help";
const char *OPT_V1 = "--v1";
const char *OPT_V2 = "--v2";
const char *OPT_V3 = "--v3";
const char *OPT_MAX_ATTEMPTS = "--attempts";
const char *OPT_TO = "--to";
const char *OPT_K_IND = "--kind";
const char *OPT_ITP = "--itp";
const char *OPT_BATCH = "--batch";
const char *OPT_RETRY = "--retry";
const char *OPT_ELIM = "--skip-elim";
const char *OPT_ARITHM = "--skip-arithm";
const char *OPT_SEED = "--inv-mode";
const char *OPT_GET_FREQS = "--freqs";
const char *OPT_ADD_EPSILON = "--eps";
const char *OPT_AGG_PRUNING = "--aggp";
const char *OPT_DATA_LEARNING = "--data";
const char *OPT_PROP = "--prop";
const char *OPT_DISJ = "--disj";
const char *OPT_D1 = "--all-mbp";
const char *OPT_D2 = "--phase-prop";
const char *OPT_D3 = "--phase-data";
const char *OPT_D4 = "--stren-mbp";
const char *OPT_MBP = "--eqs-mbp";
const char *OPT_DEBUG = "--debug";

int main (int argc, char ** argv)
{
  set<int> nums;
  getNums(nums, getStrValue("--keys", NULL, argc, argv));
  bool to_skip = getBoolValue("--no-term", false, argc, argv);
  int lookahead = getIntValue("--lookahead", 0, argc, argv);
  
  // All other attrs are inherited from FreqHorn:
  int max_attempts = getIntValue(OPT_MAX_ATTEMPTS, 10, argc, argv);
  int to = getIntValue(OPT_TO, 1000, argc, argv);
  bool kinduction = getBoolValue(OPT_K_IND, false, argc, argv);
  bool densecode = getBoolValue(OPT_GET_FREQS, false, argc, argv);
  bool addepsilon = getBoolValue(OPT_ADD_EPSILON, false, argc, argv);
  bool aggressivepruning = getBoolValue(OPT_AGG_PRUNING, false, argc, argv);
  int itp = getIntValue(OPT_ITP, 0, argc, argv);
  int batch = getIntValue(OPT_BATCH, 3, argc, argv);
  int retry = getIntValue(OPT_RETRY, 3, argc, argv);
  bool do_elim = !getBoolValue(OPT_ELIM, false, argc, argv);
  bool do_arithm = !getBoolValue(OPT_ARITHM, false, argc, argv);
  int invMode = getIntValue(OPT_SEED, 0, argc, argv);
  int do_prop = getIntValue(OPT_PROP, 0, argc, argv);
  int do_disj = getBoolValue(OPT_DISJ, false, argc, argv);
  bool do_dl = getBoolValue(OPT_DATA_LEARNING, false, argc, argv);
  int mbp_eqs = getIntValue(OPT_MBP, 0, argc, argv);
  bool d_m = getBoolValue(OPT_D1, false, argc, argv);
  bool d_p = getBoolValue(OPT_D2, false, argc, argv);
  bool d_d = getBoolValue(OPT_D3, false, argc, argv);
  bool d_s = getBoolValue(OPT_D4, false, argc, argv);
  int debug = getIntValue(OPT_DEBUG, 0, argc, argv);

  if (do_disj && (!d_p && !d_d))
  {
    errs() << "WARNING: either \"" << OPT_D2 << "\" or \"" << OPT_D3 << "\" should be enabled\n"
           << "enabling \"" << OPT_D3 << "\"\n";
    d_d = true;
  }

  if (d_m || d_p || d_d || d_s) do_disj = true;
  if (do_disj) do_dl = true;

  testgen(string(argv[argc-1]), nums, max_attempts, to, densecode, aggressivepruning,
                     do_dl, do_elim, do_disj, do_prop, d_m, d_p, d_d, d_s, to_skip, invMode, lookahead, debug);
  return 0;
}
