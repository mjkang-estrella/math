// Exhaustive test of Theorem thm:clean, of the statement of Lemma lem:main, and of the literal
// strategy in the proof of lem:main, on all clean / almost clean status-labelled trees whose
// underlying trees are read from stdin ("n m u1 v1 ... " per line).
#include "core.hpp"
#include <iostream>
#include <sstream>
#include <set>
#include <map>

static const char* SC = "niof";

// --- class C membership for a normal-form connected component ---
static int nLeafFlag = 0;
static bool inC(const Forest& c) {
  int E = c.e.size();
  int deg[MAXV] = {0};
  for (auto& p : c.e) { deg[p.first]++; deg[p.second]++; }
  for (int x = 0; x < c.n; x++) if (deg[x] == 1 && c.st[x] == SN) { nLeafFlag++; return false; }
  if (E <= 1) return true;
  bool allFree = true;
  for (int x = 0; x < c.n; x++) if (deg[x] == 1 && c.st[x] != SF) allFree = false;
  std::vector<std::pair<int,int>> chain;
  for (auto& p : c.e) if (deg[p.first] == 2 && deg[p.second] == 2) chain.push_back(p);
  if (allFree && chain.empty()) return true;
  for (int w = 0; w < c.n; w++) {
    if (c.st[w] != SI && c.st[w] != SO) continue;
    bool ok = true;
    for (int x = 0; x < c.n && ok; x++) if (x != w && deg[x] == 1 && c.st[x] != SF) ok = false;
    for (auto& p : chain) if (p.first != w && p.second != w) ok = false;
    if (ok && deg[w] == 1) {
      for (auto& p : c.e) if (p.first == w || p.second == w) { int y = p.first ^ p.second ^ w; if (deg[y] < 3) ok = false; }
    }
    if (ok) return true;
  }
  return false;
}

static Forest oppReduce(const Forest& c) {
  Forest f = c;
  int deg[MAXV] = {0}; int nb[MAXV];
  for (auto& p : c.e) { deg[p.first]++; deg[p.second]++; nb[p.first] = p.second; nb[p.second] = p.first; }
  for (int z = 0; z < c.n; z++) if (deg[z] == 1 && (c.st[z] == SI || c.st[z] == SO)) {
    int v = nb[z];
    if ((c.st[v] == SI || c.st[v] == SO) && c.st[v] != c.st[z]) f.st[v] = SF;
  }
  return f;
}

// is forest (unnormalized) a C-sum (allowing Lemma oppblocked)? returns #edges after normalization in *E
static bool isCsum(const Forest& f, int* E) {
  std::vector<Forest> comps; normalize(f, comps);
  int tot = 0; bool ok = true;
  for (auto& c : comps) {
    tot += c.e.size();
    if (inC(c)) continue;
    std::vector<Forest> sub; normalize(oppReduce(c), sub);
    for (auto& s : sub) if (!inC(s)) ok = false;
  }
  *E = tot;
  return ok;
}

// --- helpers on X ---
struct X_ {
  Forest f; int n; std::vector<std::vector<int>> adj; std::vector<int> deg;
  void init(const Forest& F) { f = F; n = F.n; adj.assign(n, {}); deg.assign(n, 0);
    for (auto& p : F.e) { adj[p.first].push_back(p.second); adj[p.second].push_back(p.first); deg[p.first]++; deg[p.second]++; } }
  bool inSide(int r, int c, int w) const { // w in X_{r|c}?
    std::vector<int> stck{r}; std::vector<char> vis(n, 0); vis[r] = 1; vis[c] = 1;
    while (!stck.empty()) { int x = stck.back(); stck.pop_back(); if (x == w) return true; for (int y : adj[x]) if (!vis[y]) { vis[y] = 1; stck.push_back(y); } }
    return false;
  }
  int edgeIdx(const Forest& F, int a, int b) const { for (size_t k = 0; k < F.e.size(); k++) if ((F.e[k].first == a && F.e[k].second == b) || (F.e[k].first == b && F.e[k].second == a)) return k; return -1; }
};

// orient edge xy in F so that x receives type t (SO: x is tail; SI: x is head). returns false if illegal
static bool orientTo(Forest& F, int x, int y, int t) {
  int k = -1; for (size_t j = 0; j < F.e.size(); j++) if ((F.e[j].first == x && F.e[j].second == y) || (F.e[j].first == y && F.e[j].second == x)) k = j;
  if (k < 0) return false;
  int tail = (t == SO) ? x : y, head = (t == SO) ? y : x;
  bool fwd = (F.e[k].first == tail);
  if (!legalMove(F, k, fwd)) return false;
  F = applyMove(F, k, fwd);
  (void)head;
  return true;
}
static int bar(int t) { return t == SI ? SO : SI; }
static int mulT(int s, int t) { return t == SO ? mulO(s) : mulI(s); }

long long nPos = 0, nMoves = 0, failThm = 0, failLemI = 0, failLemII = 0, failProof = 0, failProofI = 0, nReplies = 0;
std::map<std::string, long long> caseCount;

static void report(const char* what, const Forest& X, int extra = -1) {
  static int shown = 0; if (shown++ > 40) return;
  printf("%s: n=%d st=", what, X.n); for (int i = 0; i < X.n; i++) putchar(SC[X.st[i]]);
  printf(" edges:"); for (auto& p : X.e) printf(" %d-%d", p.first, p.second); printf(" extra=%d\n", extra);
}

// proof strategy for (ii): returns true if the literal strategy works for the move (k,fwd), given defect w (or -1 for clean)
static bool proofStrategy(const X_& X, int w, int k, bool fwd, std::string& cs) {
  const Forest& F = X.f; int e = F.e.size();
  int tail = F.e[k].first, head = F.e[k].second; if (!fwd) std::swap(tail, head);
  Forest X1 = applyMove(F, k, fwd);
  int E1;
  auto noReply = [&]() { bool ok = isCsum(X1, &E1) && E1 == e - 1; return ok; };
  auto withReply = [&](int x, int y, int t) { Forest X2 = X1; if (!orientTo(X2, x, y, t)) return false; int E2; nReplies++; return isCsum(X2, &E2) && E2 == e - 2; };
  if (w < 0) { cs = "clean"; return noReply(); }
  // type received by a vertex in the move
  auto recv = [&](int x) { return x == tail ? SO : SI; };
  if (w == tail || w == head) {
    if (X.deg[w] == 1) { cs = "1a"; return noReply(); }
    int xx = (w == tail) ? head : tail; int th = recv(w);
    int y = X.adj[w][0] == xx ? X.adj[w][1] : X.adj[w][0];
    if (mulT(F.st[w], th) == SF) { cs = "1b-f"; return noReply(); }
    if (X.deg[y] != 2) { cs = "1b-y13"; return noReply(); }
    cs = "1b-y2"; return withReply(w, y, bar(th));
  }
  int a, b; if (X.inSide(tail, head, w)) { a = tail; b = head; } else { a = head; b = tail; }
  int th = recv(a);
  if (mulT(F.st[a], th) == SF) { cs = "2.1"; return noReply(); }
  if (X.deg[a] >= 4) { cs = "2.2"; return noReply(); }
  if (X.deg[a] == 3) {
    std::vector<int> r; for (int y : X.adj[a]) if (y != b) r.push_back(y);
    if (X.deg[w] == 1 && (r[0] == w || r[1] == w)) {
      int r2 = (r[0] == w) ? r[1] : r[0]; int pi = F.st[w];
      if (pi != th) { cs = "2.3.1-ne"; return noReply(); }
      cs = "2.3.1-eq"; return withReply(a, r2, bar(th));
    }
    bool need = false; for (int y : r) if (y != w && X.deg[y] == 2) need = true;
    if (!need) { cs = "2.3.2-none"; return noReply(); }
    int rr = X.inSide(r[0], a, w) ? r[1] : r[0];
    cs = "2.3.2-reply"; return withReply(a, rr, bar(th));
  }
  if (X.deg[a] == 2) {
    int z = X.adj[a][0] == b ? X.adj[a][1] : X.adj[a][0]; int pi = th;
    if (z == w) {
      if (X.deg[w] != 2) { cs = "2.4-bad"; return false; }
      int x = X.adj[w][0] == a ? X.adj[w][1] : X.adj[w][0];
      if (F.st[w] != pi) { cs = "2.4.1-ne"; return noReply(); }
      cs = "2.4.1-eq"; return withReply(w, x, bar(pi));
    }
    if (X.deg[z] < 3) { cs = "2.4-bad2"; return false; }
    if ((F.st[z] == SI || F.st[z] == SO) && F.st[z] != pi) { cs = "2.4.2-opp"; return noReply(); }
    cs = "2.4.2-reply"; bool all = true; int cnt = 0;
    for (int q : X.adj[z]) if (q != a && !X.inSide(q, z, w)) { cnt++; if (!withReply(z, q, bar(pi))) all = false; }
    return all && cnt > 0;
  }
  cs = "2-bad-deg"; return false;
}

static void testPos(const Forest& Xf, const std::vector<int>& defects) {
  nPos++;
  int e = Xf.e.size();
  int g = grundyForest(Xf);
  if (g != (e & 1)) { failThm++; report("THEOREM FAILS", Xf, g); }
  X_ X; X.init(Xf);
  // Lemma (i) statement
  bool someGood = false;
  for (int k = 0; k < e; k++) for (int fwd = 0; fwd < 2; fwd++) {
    if (!legalMove(Xf, k, fwd)) continue;
    Forest X1 = applyMove(Xf, k, fwd); int E1;
    if (isCsum(X1, &E1) && E1 == e - 1) someGood = true;
  }
  if (!someGood) { failLemI++; report("LEMMA(i) FAILS", Xf); }
  // proof (i) strategies
  if (e >= 2) {
    std::vector<int> ws = defects; if (ws.empty()) ws.push_back(-1);
    for (int w : ws) {
      bool ok = true;
      if (w < 0) { // clean: every leaf, both orientations
        for (int l = 0; l < X.n; l++) if (X.deg[l] == 1) for (int t : {SI, SO}) { Forest F2 = Xf; if (!orientTo(F2, l, X.adj[l][0], t)) { ok = false; continue; } int E1; if (!(isCsum(F2, &E1) && E1 == e - 1)) ok = false; }
      } else if (X.deg[w] == 1) {
        Forest F2 = Xf; if (!orientTo(F2, w, X.adj[w][0], bar(Xf.st[w]))) ok = false; else { int E1; if (!(isCsum(F2, &E1) && E1 == e - 1)) ok = false; }
      } else if (X.deg[w] == 2) {
        for (int x : X.adj[w]) { Forest F2 = Xf; if (!orientTo(F2, w, x, bar(Xf.st[w]))) { ok = false; continue; } int E1; if (!(isCsum(F2, &E1) && E1 == e - 1)) ok = false; }
      } // deg>=3: clean, handled by w<0 entry
      if (!ok) { failProofI++; report("PROOF(i) FAILS", Xf, w); }
    }
  }
  // Lemma (ii) statement and proof strategy
  for (int k = 0; k < e; k++) for (int fwd = 0; fwd < 2; fwd++) {
    if (!legalMove(Xf, k, fwd)) continue;
    nMoves++;
    Forest X1 = applyMove(Xf, k, fwd); int E1;
    bool ok = isCsum(X1, &E1) && E1 == e - 1;
    if (!ok) {
      for (size_t j = 0; j < X1.e.size() && !ok; j++) for (int f2 = 0; f2 < 2 && !ok; f2++) {
        if (!legalMove(X1, j, f2)) continue;
        Forest X2 = applyMove(X1, j, f2); int E2;
        if (isCsum(X2, &E2) && E2 == e - 2) ok = true;
      }
    }
    if (!ok) { failLemII++; report("LEMMA(ii) FAILS", Xf, k * 2 + fwd); }
    if (e >= 2) {
      std::vector<int> ws = defects; if (ws.empty()) ws.push_back(-1);
      for (int w : ws) {
        int ww = w;
        if (w >= 0 && X.deg[w] >= 3) ww = -1; // clean
        std::string cs;
        bool r = proofStrategy(X, ww, k, fwd, cs);
        caseCount[cs]++;
        if (!r) { failProof++; report(("PROOF(ii) FAILS case " + cs).c_str(), Xf, k * 2 + fwd); }
      }
    }
  }
}


#ifdef RANDMODE
#include <random>
int main(int argc, char** argv) {
  int samples = argc > 1 ? atoi(argv[1]) : 20;
  std::mt19937_64 rng(12345);
  long long nClean = 0, nAlmost = 0; std::string line;
  while (std::getline(std::cin, line)) {
    std::istringstream is(line); int n, m; is >> n >> m;
    Forest T; T.n = n; for (int k = 0; k < m; k++) { int u, v; is >> u >> v; T.e.push_back({u, v}); }
    std::vector<int> deg(n, 0); for (auto& p : T.e) { deg[p.first]++; deg[p.second]++; }
    std::vector<std::vector<int>> adj(n); for (auto& p : T.e) { adj[p.first].push_back(p.second); adj[p.second].push_back(p.first); }
    bool hasChain = false; for (auto& p : T.e) if (deg[p.first] == 2 && deg[p.second] == 2) hasChain = true;
    std::vector<int> cand; if (!hasChain) cand.push_back(-1);
    for (int w = 0; w < n; w++) { bool ok = true;
      for (auto& p : T.e) if (deg[p.first] == 2 && deg[p.second] == 2 && p.first != w && p.second != w) ok = false;
      if (deg[w] == 1 && deg[adj[w][0]] < 3) ok = false; if (ok && deg[w] <= 2) cand.push_back(w); }
    if (cand.empty()) continue;
    for (int s = 0; s < samples; s++) {
      int w = cand[rng() % cand.size()];
      Forest X = T;
      for (int i = 0; i < n; i++) X.st[i] = deg[i] == 1 ? SF : (int)(rng() % 3);
      if (w >= 0) X.st[w] = (rng() & 1) ? SI : SO;
      std::vector<int> defs;
      bool clean = !hasChain; for (int i = 0; i < n; i++) if (deg[i] == 1 && X.st[i] != SF) clean = false;
      if (!clean) {
        for (int ww = 0; ww < n; ww++) {
          if (X.st[ww] != SI && X.st[ww] != SO) continue; bool ok = true;
          for (int i = 0; i < n; i++) if (i != ww && deg[i] == 1 && X.st[i] != SF) ok = false;
          for (auto& p : T.e) if (deg[p.first] == 2 && deg[p.second] == 2 && p.first != ww && p.second != ww) ok = false;
          if (deg[ww] == 1 && deg[adj[ww][0]] < 3) ok = false;
          if (ok) defs.push_back(ww);
        }
        nAlmost++;
      } else nClean++;
      testPos(X, defs);
    }
  }
  printf("random positions=%lld clean=%lld almost=%lld moves=%lld replies=%lld\n", nPos, nClean, nAlmost, nMoves, nReplies);
  printf("theorem failures=%lld lemma(i) failures=%lld lemma(ii) failures=%lld proof(i) failures=%lld proof(ii) failures=%lld nLeafFlag=%d memo=%zu\n", failThm, failLemI, failLemII, failProofI, failProof, nLeafFlag, MEMO.cnt);
  for (auto& kv : caseCount) printf("  case %-12s %lld\n", kv.first.c_str(), kv.second);
}
#else
int main(int argc, char** argv) {
  int maxV = argc > 1 ? atoi(argv[1]) : 99;
  std::set<std::pair<uint64_t,uint64_t>> seenKeys;
  long long nClean = 0, nAlmost = 0;
  std::string line;
  while (std::getline(std::cin, line)) {
    std::istringstream is(line); int n, m; is >> n >> m; if (n > maxV) continue;
    Forest T; T.n = n; for (int k = 0; k < m; k++) { int u, v; is >> u >> v; T.e.push_back({u, v}); }
    std::vector<int> deg(n, 0); for (auto& p : T.e) { deg[p.first]++; deg[p.second]++; }
    std::vector<std::vector<int>> adj(n); for (auto& p : T.e) { adj[p.first].push_back(p.second); adj[p.second].push_back(p.first); }
    if (m == 1) { // single edges: f-f, f-i, f-o, i-o
      int combos[4][2] = {{SF, SF}, {SF, SI}, {SF, SO}, {SI, SO}};
      for (auto& cb : combos) { Forest X = T; X.st[0] = cb[0]; X.st[1] = cb[1]; Key kk = canonKey(X); if (seenKeys.insert({kk.hi, kk.lo}).second) testPos(X, {}); }
      continue;
    }
    std::vector<int> nonleaf; for (int i = 0; i < n; i++) if (deg[i] > 1) nonleaf.push_back(i);
    bool hasChain = false; for (auto& p : T.e) if (deg[p.first] == 2 && deg[p.second] == 2) hasChain = true;
    // candidates: w = -1 (clean) or each vertex w with s(w) in {i,o}
    for (int w = -1; w < n; w++) {
      if (w >= 0) {
        bool ok = true;
        for (auto& p : T.e) if (deg[p.first] == 2 && deg[p.second] == 2 && p.first != w && p.second != w) ok = false;
        if (deg[w] == 1 && deg[adj[w][0]] < 3) ok = false;
        if (!ok) continue;
      } else if (hasChain) continue;
      std::vector<int> free_; for (int v : nonleaf) if (v != w) free_.push_back(v);
      long long tot = 1; for (size_t i = 0; i < free_.size(); i++) tot *= 3;
      for (int sw = (w >= 0 ? SI : 0); sw <= (w >= 0 ? SO : 0); sw++)
      for (long long code = 0; code < tot; code++) {
        Forest X = T; long long c = code;
        for (int i = 0; i < n; i++) X.st[i] = SF;
        for (int v : free_) { X.st[v] = c % 3; c /= 3; }
        if (w >= 0) X.st[w] = sw;
        Key kk = canonKey(X);
        if (!seenKeys.insert({kk.hi, kk.lo}).second) continue;
        // find all valid defects of X (for proof strategy)
        std::vector<int> defs;
        bool clean = !hasChain; for (int i = 0; i < n; i++) if (deg[i] == 1 && X.st[i] != SF) clean = false;
        if (!clean) {
          for (int ww = 0; ww < n; ww++) {
            if (X.st[ww] != SI && X.st[ww] != SO) continue;
            bool ok = true;
            for (int i = 0; i < n; i++) if (i != ww && deg[i] == 1 && X.st[i] != SF) ok = false;
            for (auto& p : T.e) if (deg[p.first] == 2 && deg[p.second] == 2 && p.first != ww && p.second != ww) ok = false;
            if (deg[ww] == 1 && deg[adj[ww][0]] < 3) ok = false;
            if (ok) defs.push_back(ww);
          }
          if (defs.empty()) { printf("enumeration bug\n"); exit(1); }
          nAlmost++;
        } else nClean++;
        testPos(X, defs);
      }
    }
  }
  printf("positions(distinct up to iso)=%lld clean=%lld almost-clean(not clean)=%lld moves=%lld replies-tested=%lld\n", nPos, nClean, nAlmost, nMoves, nReplies);
  printf("theorem failures=%lld lemma(i) failures=%lld lemma(ii) failures=%lld proof(i) failures=%lld proof(ii) failures=%lld nLeafFlag=%d memo=%zu\n", failThm, failLemI, failLemII, failProofI, failProof, nLeafFlag, MEMO.cnt);
  for (auto& kv : caseCount) printf("  case %-12s %lld\n", kv.first.c_str(), kv.second);
}

#endif
