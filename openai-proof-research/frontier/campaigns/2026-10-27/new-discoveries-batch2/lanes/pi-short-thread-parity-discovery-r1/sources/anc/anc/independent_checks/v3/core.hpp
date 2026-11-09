// Independent solver for the arrow game on status-labelled forests (Lemma 3.2 rules).
// Statuses: N=0 (no arcs), I=1 (has incoming), O=2 (has outgoing), F=3 (free).
#pragma once
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>
#include <algorithm>
#include <utility>

enum { SN = 0, SI = 1, SO = 2, SF = 3 };
static const int MAXV = 64;
static bool USE_OPP = false, USE_REV = false;

static inline int mulO(int s) { return (s == SI || s == SF) ? SF : SO; }  // s * o
static inline int mulI(int s) { return (s == SO || s == SF) ? SF : SI; }  // s * i

struct Forest {
  int n = 0;
  uint8_t st[MAXV];
  std::vector<std::pair<int,int>> e;
};

// legality of orienting u->v given degrees d and statuses (Lemma 3.2)
static inline bool legalUV(int du, int su, int dv, int sv) {
  return (du >= 2 || su == SI || su == SF) && (dv >= 2 || sv == SO || sv == SF);
}

// Normal form: delete dead edges (ends -> F), split F vertices, drop isolated vertices.
static void normalize(const Forest& in, std::vector<Forest>& out) {
  Forest f = in;
  bool changed = true;
  while (changed) {
    changed = false;
    int d[MAXV] = {0};
    for (auto& p : f.e) { d[p.first]++; d[p.second]++; }
    for (size_t k = 0; k < f.e.size(); k++) {
      int x = f.e[k].first, y = f.e[k].second;
      bool l1 = legalUV(d[x], f.st[x], d[y], f.st[y]);
      bool l2 = legalUV(d[y], f.st[y], d[x], f.st[x]);
      if (!l1 && !l2) {
        f.st[x] = SF; f.st[y] = SF;
        f.e.erase(f.e.begin() + k);
        changed = true;
        break;
      }
    }
  }
  if (USE_OPP) {
    int d[MAXV] = {0}; int nb[MAXV];
    for (auto& p : f.e) { d[p.first]++; d[p.second]++; nb[p.first] = p.second; nb[p.second] = p.first; }
    uint8_t ns[MAXV]; memcpy(ns, f.st, f.n);
    for (int z = 0; z < f.n; z++) if (d[z] == 1 && (f.st[z] == SI || f.st[z] == SO)) {
      int v = nb[z]; if ((f.st[v] == SI || f.st[v] == SO) && f.st[v] != f.st[z]) ns[v] = SF; }
    memcpy(f.st, ns, f.n);
  }
  // split F vertices
  int m = f.e.size();
  int nn = f.n;
  std::vector<std::pair<int,int>> E(m);
  std::vector<uint8_t> S(f.st, f.st + f.n);
  for (int k = 0; k < m; k++) {
    int x = f.e[k].first, y = f.e[k].second;
    if (f.st[x] == SF) { x = nn++; S.push_back(SF); }
    if (f.st[y] == SF) { y = nn++; S.push_back(SF); }
    E[k] = {x, y};
  }
  // union-find
  std::vector<int> par(nn);
  for (int i = 0; i < nn; i++) par[i] = i;
  auto fnd = [&](int x) { while (par[x] != x) { par[x] = par[par[x]]; x = par[x]; } return x; };
  for (auto& p : E) { int a = fnd(p.first), b = fnd(p.second); if (a != b) par[a] = b; }
  std::vector<int> compId(nn, -1), newId(nn, -1);
  out.clear();
  for (auto& p : E) {
    int r = fnd(p.first);
    if (compId[r] < 0) { compId[r] = out.size(); out.emplace_back(); out.back().n = 0; }
    Forest& c = out[compId[r]];
    for (int x : {p.first, p.second}) if (newId[x] < 0) { newId[x] = c.n; c.st[c.n++] = S[x]; if (c.n > MAXV) { fprintf(stderr, "too big\n"); exit(1);} }
    c.e.push_back({newId[p.first], newId[p.second]});
  }
}

// ---------- canonical key of a status-labelled tree ----------
struct Key { uint64_t hi, lo; bool operator==(const Key& o) const { return hi == o.hi && lo == o.lo; } };

static std::string rcode(int v, int p, const std::vector<std::vector<int>>& adj, const uint8_t* st) {
  std::vector<std::string> ch;
  for (int u : adj[v]) if (u != p) ch.push_back(rcode(u, v, adj, st));
  std::sort(ch.begin(), ch.end());
  std::string s(1, char('a' + st[v]));
  for (auto& c : ch) s += c;
  s += ')';
  return s;
}

static std::string canonString(const Forest& t) {
  int n = t.n;
  std::vector<std::vector<int>> adj(n);
  for (auto& p : t.e) { adj[p.first].push_back(p.second); adj[p.second].push_back(p.first); }
  if (n == 1) return std::string("U") + rcode(0, -1, adj, t.st);
  std::vector<int> deg(n), layer;
  for (int i = 0; i < n; i++) { deg[i] = adj[i].size(); if (deg[i] <= 1) layer.push_back(i); }
  int rem = n;
  std::vector<char> gone(n, 0);
  while (rem > 2) {
    std::vector<int> nl;
    for (int v : layer) { gone[v] = 1; rem--; for (int u : adj[v]) if (!gone[u]) { if (--deg[u] == 1) nl.push_back(u); } }
    layer = nl;
  }
  std::vector<int> cen;
  for (int i = 0; i < n; i++) if (!gone[i]) cen.push_back(i);
  if (cen.size() == 1) return std::string("U") + rcode(cen[0], -1, adj, t.st);
  std::string a = rcode(cen[0], cen[1], adj, t.st), b = rcode(cen[1], cen[0], adj, t.st);
  if (b < a) std::swap(a, b);
  return std::string("B") + a + b;
}

static Key canonKey1(const Forest& t, const std::string& s);
static Key canonKey(const Forest& t) {
  std::string s = canonString(t);
  if (USE_REV) {
    Forest r = t; for (int i = 0; i < r.n; i++) if (r.st[i] == SI) r.st[i] = SO; else if (r.st[i] == SO) r.st[i] = SI;
    std::string s2 = canonString(r); if (s2 < s) s = s2;
  }
  return canonKey1(t, s);
}
static Key canonKey1(const Forest& t, const std::string& s) {
  // pack: header n (6 bits), flag (1 bit), then per char: open -> 1 s1 s0, close -> 0
  unsigned __int128 x = 0;
  int bits = 0;
  auto push = [&](unsigned v, int nb) { x = (x << nb) | v; bits += nb; };
  push(t.n, 6);
  push(s[0] == 'B', 1);
  for (size_t i = 1; i < s.size(); i++) {
    if (s[i] == ')') push(0, 1); else push(4 | (s[i] - 'a'), 3);
  }
  if (bits > 127) { fprintf(stderr, "key overflow n=%d\n", t.n); exit(1); }
  x = (x << (128 - bits));
  x |= 1;  // never zero
  return Key{(uint64_t)(x >> 64), (uint64_t)x};
}

// ---------- open addressing hash map Key -> uint8 ----------
struct Memo {
  std::vector<uint64_t> H, L; std::vector<uint8_t> V; size_t cap = 0, cnt = 0;
  Memo() { rehash(1 << 20); }
  static size_t h(const Key& k) { uint64_t z = k.hi * 0x9E3779B97F4A7C15ULL ^ (k.lo + 0x632BE59BD9B4E019ULL); z ^= z >> 31; z *= 0xBF58476D1CE4E5B9ULL; z ^= z >> 29; return z; }
  void rehash(size_t nc) {
    std::vector<uint64_t> oH = std::move(H), oL = std::move(L); std::vector<uint8_t> oV = std::move(V);
    H.assign(nc, 0); L.assign(nc, 0); V.assign(nc, 0); cap = nc; cnt = 0;
    for (size_t i = 0; i < oH.size(); i++) if (oH[i] | oL[i]) put(Key{oH[i], oL[i]}, oV[i]);
  }
  int get(const Key& k) const {
    size_t i = h(k) & (cap - 1);
    while (H[i] | L[i]) { if (H[i] == k.hi && L[i] == k.lo) return V[i]; i = (i + 1) & (cap - 1); }
    return -1;
  }
  void put(const Key& k, int v) {
    if ((cnt + 1) * 10 > cap * 7) rehash(cap * 2);
    size_t i = h(k) & (cap - 1);
    while (H[i] | L[i]) { if (H[i] == k.hi && L[i] == k.lo) { V[i] = v; return; } i = (i + 1) & (cap - 1); }
    H[i] = k.hi; L[i] = k.lo; V[i] = v; cnt++;
  }
};

static Memo MEMO;

static int grundyComp(const Forest& c);

static int grundyForest(const Forest& f) {
  std::vector<Forest> comps;
  normalize(f, comps);
  int g = 0;
  for (auto& c : comps) g ^= grundyComp(c);
  return g;
}

// apply orientation u->v of edge index k to forest c (no normalization)
static Forest applyMove(const Forest& c, int k, bool fwd) {
  Forest f = c;
  int u = c.e[k].first, v = c.e[k].second;
  if (!fwd) std::swap(u, v);
  f.e.erase(f.e.begin() + k);
  f.st[u] = mulO(f.st[u]);
  f.st[v] = mulI(f.st[v]);
  return f;
}

static bool legalMove(const Forest& c, int k, bool fwd) {
  int d[MAXV] = {0};
  for (auto& p : c.e) { d[p.first]++; d[p.second]++; }
  int u = c.e[k].first, v = c.e[k].second;
  if (!fwd) std::swap(u, v);
  return legalUV(d[u], c.st[u], d[v], c.st[v]);
}

// c must be a normal-form connected component
static int grundyComp(const Forest& c) {
  Key k = canonKey(c);
  int g = MEMO.get(k);
  if (g >= 0) return g;
  int d[MAXV] = {0};
  for (auto& p : c.e) { d[p.first]++; d[p.second]++; }
  uint64_t seen[4] = {0, 0, 0, 0};
  for (size_t j = 0; j < c.e.size(); j++) {
    for (int fwd = 0; fwd < 2; fwd++) {
      int u = c.e[j].first, v = c.e[j].second;
      if (!fwd) std::swap(u, v);
      if (!legalUV(d[u], c.st[u], d[v], c.st[v])) continue;
      Forest f = applyMove(c, j, fwd);
      int x = grundyForest(f);
      if (x >= 256) { fprintf(stderr, "big grundy\n"); exit(1); }
      seen[x >> 6] |= 1ULL << (x & 63);
    }
  }
  int mex = 0;
  while (seen[mex >> 6] >> (mex & 63) & 1) mex++;
  if (mex > 250) { fprintf(stderr, "big mex\n"); exit(1); }
  MEMO.put(k, mex);
  return mex;
}

// Pieces of a tree T (edge list on n vertices): returns forest of markable edges with statuses
static Forest treeToForest(int n, const std::vector<std::pair<int,int>>& E) {
  std::vector<int> deg(n, 0);
  for (auto& p : E) { deg[p.first]++; deg[p.second]++; }
  std::vector<char> special(n, 0);
  for (auto& p : E) {
    if (deg[p.first] == 1 && deg[p.second] > 1) special[p.second] = 1;
    if (deg[p.second] == 1 && deg[p.first] > 1) special[p.first] = 1;
  }
  Forest f; f.n = n;
  for (int i = 0; i < n; i++) f.st[i] = special[i] ? SF : SN;
  for (auto& p : E) if (deg[p.first] > 1 && deg[p.second] > 1) f.e.push_back(p);
  return f;
}
