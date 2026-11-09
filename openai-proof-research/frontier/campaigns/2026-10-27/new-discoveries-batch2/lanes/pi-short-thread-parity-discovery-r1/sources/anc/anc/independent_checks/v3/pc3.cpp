// Piece / tree analyser.
//  ./pc piece MAXINT MAXLEAF [twinfree]  : each input tree is regarded as a piece (leaves F, others N);
//        keep those whose internal threads have <= MAXINT edges and leaf threads <= MAXLEAF edges;
//        print stats per vertex count and every piece with g != |E| mod 2.
//  ./pc tree MAXT : each input tree T; keep those all of whose piece-threads have <= MAXT edges;
//        print stats and every T with g != m mod 2 (flagging true parity-conjecture violations).
#include "core.hpp"
#include <iostream>
#include <sstream>
#include <map>
#include <array>
#include "gen.hpp"

// threads of a tree component: returns pairs (length, isInternal)
static void threadsOf(const Forest& c, std::vector<std::pair<int,bool>>& out) {
  out.clear();
  int n = c.n; std::vector<std::vector<int>> adj(n);
  for (auto& p : c.e) { adj[p.first].push_back(p.second); adj[p.second].push_back(p.first); }
  for (int a = 0; a < n; a++) {
    if (adj[a].size() == 2 || adj[a].empty()) continue;
    for (int b : adj[a]) {
      int prev = a, cur = b, len = 1;
      while (adj[cur].size() == 2) { int nx = adj[cur][0] == prev ? adj[cur][1] : adj[cur][0]; prev = cur; cur = nx; len++; }
      if (cur < a) continue;           // count each thread once (from smaller end)
      if (cur == a) continue;
      bool internal = adj[a].size() >= 3 && adj[cur].size() >= 3;
      out.push_back({len, internal});
    }
  }
}

static std::string rc2(int v, int p, const std::vector<std::vector<int>>& adj) {
  std::vector<std::string> ch; for (int u : adj[v]) if (u != p) ch.push_back(rc2(u, v, adj));
  std::sort(ch.begin(), ch.end()); std::string s = "("; for (auto& x : ch) s += x; return s + ")";
}
static bool hasTwins(const Forest& c) {
  int n = c.n; std::vector<std::vector<int>> adj(n);
  for (auto& p : c.e) { adj[p.first].push_back(p.second); adj[p.second].push_back(p.first); }
  for (int v = 0; v < n; v++) {
    if (adj[v].size() < 2) continue;
    std::vector<std::string> codes; for (int u : adj[v]) codes.push_back(rc2(u, v, adj));
    std::sort(codes.begin(), codes.end());
    for (size_t i = 1; i < codes.size(); i++) if (codes[i] == codes[i - 1]) return true;
  }
  return false;
}


int main(int argc, char** argv) {
  setvbuf(stdout, NULL, _IOLBF, 0);
  if (getenv("OPT")) { USE_OPP = USE_REV = true; }
  std::string mode = argv[1];
  std::map<int, std::array<long long, 6>> stat;
  if (mode == "piece") {
    int maxInt = atoi(argv[2]), maxLeaf = atoi(argv[3]), nlo = atoi(argv[4]), nhi = atoi(argv[5]);
    bool tfOnly = argc > 6 && std::string(argv[6]) == "tf"; int onlyL = argc > 7 ? atoi(argv[7]) : -1; bool countOnly = argc > 8 && std::string(argv[8]) == "count";
    for (int n = nlo; n <= nhi; n++) {
      forEachTree(n, [&](int n, const std::vector<std::pair<int,int>>& E) {
        Forest P; P.n = n; P.e = E; int m = E.size();
        std::vector<int> deg(n, 0); for (auto& p : P.e) { deg[p.first]++; deg[p.second]++; }
        for (int i = 0; i < n; i++) P.st[i] = deg[i] == 1 ? SF : SN;
        std::vector<std::pair<int,bool>> th; threadsOf(P, th);
        for (auto& t : th) if (t.first > (t.second ? maxInt : maxLeaf)) return;
        int L = 0; for (int i = 0; i < n; i++) if (deg[i] == 1) L++;
        if (onlyL >= 0 && L != onlyL) return;
        bool tw = hasTwins(P);
        auto& s = stat[n]; s[0]++; if (!tw) s[2]++;
        if (tfOnly && tw) return;
        if (countOnly) return;
        int g = grundyForest(P);
        bool bad = g != (m & 1);
        if (bad) { s[1]++; if (!tw) s[3]++; }
        if (bad) {
          printf("BADPIECE n=%d E=%d leaves=%d g=%d twins=%d treeVerticesMin=%d edges:", n, m, L, g, (int)tw, n + L);
          for (auto& p : P.e) printf(" %d-%d", p.first, p.second); printf("\n");
        }
      });
      auto& s = stat[n];
      printf("n=%d pieces=%lld bad=%lld twinfree=%lld twinfree_bad=%lld memo=%zu\n", n, s[0], s[1], s[2], s[3], MEMO.cnt);
    }
  } else {
    int maxT = atoi(argv[2]), nlo = atoi(argv[3]), nhi = atoi(argv[4]);
    for (int n = nlo; n <= nhi; n++) {
      forEachTree(n, [&](int n, const std::vector<std::pair<int,int>>& E) {
        Forest f = treeToForest(n, E);
        std::vector<Forest> comps; normalize(f, comps);
        std::vector<std::pair<int,bool>> th;
        auto& s = stat[n]; s[4]++;
        for (auto& c : comps) { threadsOf(c, th); for (auto& t : th) if (t.first > maxT) return; }
        int g = 0; for (auto& c : comps) g ^= grundyComp(c);
        int mm = f.e.size();
        bool bad = g != (mm & 1);
        bool cex = (g == 0) != (mm % 2 == 0);
        s[0]++; if (bad) s[1]++; if (cex) s[2]++;
        if (bad) { printf("BADTREE n=%d m=%d g=%d parity_conjecture_violated=%d edges:", n, mm, g, (int)cex); for (auto& p : E) printf(" %d-%d", p.first, p.second); printf("\n"); }
      });
      auto& s = stat[n];
      printf("n=%d alltrees=%lld threads<=%d:%lld g!=m%%2:%lld conjecture_violations=%lld memo=%zu\n", n, s[4], maxT, s[0], s[1], s[2], MEMO.cnt);
    }
  }
}
