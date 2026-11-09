// Raw-rules solver on an actual tree: a move orients an unmarked edge; it is legal iff afterwards
// neither endpoint is a sink or a source (all its edges marked and all pointing in / all out).
// Every edge (including pendant ones) is tried in both orientations; pendant edges are asserted
// never to be legal (that is the only use of "pendant": to index the memo by the other edges).
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <vector>
int n, m;
std::vector<int> U, V;            // edge endpoints
std::vector<std::vector<int>> inc; // incident edges
std::vector<int> idx;             // position of edge in base-3 index, or -1 for pendant
std::vector<uint64_t> pw;
int M;                            // number of non-pendant edges
std::vector<uint8_t> memo;        // 255 = unknown
int st[64];                       // 0 unmarked, 1 U->V, 2 V->U
long long pendantTries = 0, pendantLegal = 0;
bool okVertex(int x) {
  int in = 0, out = 0, un = 0;
  for (int k : inc[x]) {
    if (st[k] == 0) { un++; continue; }
    int head = (st[k] == 1) ? V[k] : U[k];
    if (head == x) in++; else out++;
  }
  return !(un == 0 && (in == 0 || out == 0));
}
uint64_t code() { uint64_t c = 0; for (int k = 0; k < m; k++) if (idx[k] >= 0) c += st[k] * pw[idx[k]]; return c; }
int g() {
  uint64_t c = code();
  if (memo[c] != 255) return memo[c];
  uint64_t seen = 0;
  for (int k = 0; k < m; k++) {
    if (st[k]) continue;
    for (int o = 1; o <= 2; o++) {
      st[k] = o;
      bool legal = okVertex(U[k]) && okVertex(V[k]);
      if (idx[k] < 0) { pendantTries++; if (legal) { pendantLegal++; fprintf(stderr, "pendant legal!\n"); exit(1);} }
      else if (legal) { int x = g(); seen |= 1ULL << x; }
      st[k] = 0;
    }
  }
  int mex = 0; while (seen >> mex & 1) mex++;
  memo[c] = mex;
  return mex;
}
int main() {
  if (scanf("%d %d", &n, &m) != 2) return 1;
  U.resize(m); V.resize(m); inc.assign(n, {}); idx.assign(m, -1);
  std::vector<int> deg(n, 0);
  for (int k = 0; k < m; k++) { scanf("%d %d", &U[k], &V[k]); inc[U[k]].push_back(k); inc[V[k]].push_back(k); deg[U[k]]++; deg[V[k]]++; }
  M = 0;
  for (int k = 0; k < m; k++) if (deg[U[k]] > 1 && deg[V[k]] > 1) idx[k] = M++;
  pw.assign(M + 1, 1); for (int i = 1; i <= M; i++) pw[i] = pw[i - 1] * 3;
  memo.assign(pw[M], 255);
  int r = g();
  long long states = 0; for (auto x : memo) if (x != 255) states++;
  printf("vertices=%d edges=%d m=%d grundy=%d reachable_states=%lld pendant_tries=%lld pendant_legal=%lld\n", n, m, M, r, states, pendantTries, pendantLegal);
}
