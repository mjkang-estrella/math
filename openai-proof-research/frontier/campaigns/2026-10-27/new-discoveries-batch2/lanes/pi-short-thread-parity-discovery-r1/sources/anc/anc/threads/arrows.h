// Normal-form solver for the arrow game on status-labelled trees (Game of Arrows).
// Statuses: 0=n, 1=i, 2=o, 3=f   (as in Lemma 3.2 / Def 3.4 of the paper)
// A component is a tree; vertices of status f are leaves (normal form).
// Canonical key: 128-bit Merkle hash of the tree rooted at its centre(s),
// minimised over the global reversal i<->o.
// Optional twin reduction (Theorem 3.11 adapted to labelled trees): if a vertex c has two
// child branches B1,B2 with B2 isomorphic to the i<->o flip of B1, delete both and set s(c)=f.
#pragma once
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64;

enum { SN = 0, SI = 1, SO = 2, SF = 3 };
static const uint8_t OUTA[4] = {SO, SF, SO, SF};  // status after gaining an outgoing arc
static const uint8_t INA[4] = {SI, SI, SF, SF};   // status after gaining an incoming arc
static const uint8_t FLIP[4] = {SN, SO, SI, SF};

static const int MAXV = 160;

struct Key {
    u64 a, b;
    bool operator==(const Key& o) const { return a == o.a && b == o.b; }
    bool operator<(const Key& o) const { return a < o.a || (a == o.a && b < o.b); }
};

static inline u64 smix(u64 x) {
    x += 0x9e3779b97f4a7c15ULL;
    x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
    x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
    return x ^ (x >> 31);
}
static inline u64 smix2(u64 x) {
    x ^= 0x6a09e667f3bcc909ULL;
    x = (x ^ (x >> 33)) * 0xff51afd7ed558ccdULL;
    x = (x ^ (x >> 33)) * 0xc4ceb9fe1a85ec53ULL;
    return x ^ (x >> 33);
}

// ---------------- memo table: 128-bit key -> uint8 value
struct Memo {
    vector<u64> ka, kb;
    vector<uint8_t> val;  // 255 = empty
    size_t mask = 0, used = 0;
    size_t maxEntries = 60000000;
    Memo() { init(1 << 22); }
    void init(size_t cap) {
        ka.assign(cap, 0); kb.assign(cap, 0); val.assign(cap, 255); mask = cap - 1; used = 0;
    }
    int get(const Key& k) const {
        size_t i = (size_t)(k.a ^ (k.b >> 7)) & mask;
        while (val[i] != 255) {
            if (ka[i] == k.a && kb[i] == k.b) return val[i];
            i = (i + 1) & mask;
        }
        return -1;
    }
    void put(const Key& k, int v) {
        if ((used + 1) * 4 > ka.size() * 3) {
            if (ka.size() * 2 * 3 / 4 > maxEntries * 1.5) { init(ka.size()); }  // full: clear
            else grow();
        }
        size_t i = (size_t)(k.a ^ (k.b >> 7)) & mask;
        while (val[i] != 255) {
            if (ka[i] == k.a && kb[i] == k.b) { val[i] = v; return; }
            i = (i + 1) & mask;
        }
        ka[i] = k.a; kb[i] = k.b; val[i] = (uint8_t)v; used++;
    }
    void grow() {
        vector<u64> oa, ob; vector<uint8_t> ov;
        oa.swap(ka); ob.swap(kb); ov.swap(val);
        init(oa.size() * 2);
        for (size_t i = 0; i < oa.size(); i++) if (ov[i] != 255) put(Key{oa[i], ob[i]}, ov[i]);
    }
};

// ---------------- a labelled tree component
struct EdgeList {
    pair<uint8_t, uint8_t> e[MAXV];
    int cnt = 0;
    void push_back(pair<int, int> p) { e[cnt++] = {(uint8_t)p.first, (uint8_t)p.second}; }
    int size() const { return cnt; }
    pair<uint8_t, uint8_t>* begin() { return e; }
    pair<uint8_t, uint8_t>* end() { return e + cnt; }
    const pair<uint8_t, uint8_t>* begin() const { return e; }
    const pair<uint8_t, uint8_t>* end() const { return e + cnt; }
    const pair<uint8_t, uint8_t>& operator[](int i) const { return e[i]; }
    void clear() { cnt = 0; }
};
struct Comp {
    int n = 0;
    uint8_t lab[MAXV];
    EdgeList E;
};

struct Solver {
    Memo memo;
    bool twin = true;
    bool n4 = true;
    u64 nodes = 0;

    static inline bool canTail(int lab, int d) { return d >= 2 || lab == SI || lab == SF; }
    static inline bool canHead(int lab, int d) { return d >= 2 || lab == SO || lab == SF; }

    // Normalise a labelled forest (labels lab[0..n-1], edge list E) into components.
    // lab is modified (dead-edge endpoints become f).
    void normalise(int n, uint8_t* lab, EdgeList& E, vector<Comp>& out) {
        int deg[MAXV];
        for (int i = 0; i < n; i++) deg[i] = 0;
        for (auto& e : E) { deg[e.first]++; deg[e.second]++; }
        // dead edges (one pass suffices: removing a dead edge only turns its endpoints into f,
        // which can only make other edges more legal; Lemma 3.5)
        EdgeList keep;
        int killv[2 * MAXV], nk = 0;
        for (auto& e : E) {
            int u = e.first, v = e.second;
            bool ok = (canTail(lab[u], deg[u]) && canHead(lab[v], deg[v])) ||
                      (canTail(lab[v], deg[v]) && canHead(lab[u], deg[u]));
            if (ok) keep.push_back(e); else { killv[nk++] = u; killv[nk++] = v; }
        }
        for (int k = 0; k < nk; k++) lab[killv[k]] = SF;
        // (N4) a vertex v of status i (resp. o) adjacent to a blocked leaf z of status o (resp. i)
        // never becomes a sink or source: the edge vz can only be oriented so as to give v an arc
        // of the type it lacks.  Hence s(v) may be set to f.
        if (n4) {
            int dg2[MAXV]; int nbr[MAXV];
            for (int i = 0; i < n; i++) dg2[i] = 0;
            for (int q = 0; q < keep.size(); q++) { auto& e = keep[q]; dg2[e.first]++; dg2[e.second]++; nbr[e.first] = e.second; nbr[e.second] = e.first; }
            int setf[MAXV], ns = 0;
            for (int z = 0; z < n; z++) if (dg2[z] == 1 && (lab[z] == SI || lab[z] == SO)) {
                int v = nbr[z];
                if (dg2[v] >= 2 && (lab[v] == SI || lab[v] == SO) && lab[v] != lab[z]) setf[ns++] = v;
            }
            for (int q = 0; q < ns; q++) lab[setf[q]] = SF;
        }
        int par[MAXV];
        for (int i = 0; i < n; i++) par[i] = i;
        auto fd = [&](int x) { while (par[x] != x) { par[x] = par[par[x]]; x = par[x]; } return x; };
        for (auto& e : keep) {
            int u = e.first, v = e.second;
            if (lab[u] != SF && lab[v] != SF) { int a = fd(u), b = fd(v); if (a != b) par[a] = b; }
        }
        int cid[MAXV], loc[MAXV];
        for (int i = 0; i < n; i++) { cid[i] = -1; loc[i] = -1; }
        for (auto& e : keep) {
            int u = e.first, v = e.second;
            int ci;
            if (lab[u] == SF && lab[v] == SF) { out.emplace_back(); ci = out.size() - 1; }
            else {
                int r = fd(lab[u] != SF ? u : v);
                if (cid[r] < 0) { out.emplace_back(); cid[r] = out.size() - 1; }
                ci = cid[r];
            }
            Comp& C = out[ci];
            int ab[2]; int uv[2] = {u, v};
            for (int k = 0; k < 2; k++) {
                int x = uv[k];
                if (lab[x] == SF) { C.lab[C.n] = SF; ab[k] = C.n++; }
                else { if (loc[x] < 0) { loc[x] = C.n; C.lab[C.n] = lab[x]; C.n++; } ab[k] = loc[x]; }
            }
            C.E.push_back({ab[0], ab[1]});
        }
    }

    // ---- canonical hashing with optional twin reduction.  Modifies C (reduction) and may
    // produce several components after reduction; returns them in out with their keys.
    struct HV { u64 a, b; };

    static inline bool hvless(const HV& p, const HV& q) { return p.a < q.a || (p.a == q.a && p.b < q.b); }

    void canonAll(Comp& C, vector<pair<Comp, Key>>& res) {
        int n = C.n, m = C.E.size();
        int off[MAXV + 1], nb[2 * MAXV], fill[MAXV], deg[MAXV];
        for (int i = 0; i <= n; i++) off[i] = 0;
        for (auto& e : C.E) { off[e.first + 1]++; off[e.second + 1]++; }
        for (int i = 0; i < n; i++) off[i + 1] += off[i];
        for (int i = 0; i < n; i++) fill[i] = off[i];
        for (auto& e : C.E) { nb[fill[e.first]++] = e.second; nb[fill[e.second]++] = e.first; }
        (void)m;
        // centre(s)
        int rem = n; int layer[MAXV], nl = 0, nxt[MAXV], nn = 0; bool removed[MAXV];
        for (int i = 0; i < n; i++) { deg[i] = off[i + 1] - off[i]; removed[i] = false; if (deg[i] <= 1) layer[nl++] = i; }
        while (rem > 2) {
            nn = 0;
            for (int t = 0; t < nl; t++) {
                int x = layer[t]; removed[x] = true; rem--;
                for (int j = off[x]; j < off[x + 1]; j++) { int y = nb[j]; if (!removed[y] && --deg[y] == 1) nxt[nn++] = y; }
            }
            for (int t = 0; t < nn; t++) layer[t] = nxt[t];
            nl = nn;
        }
        int centres[2], nc = 0;
        for (int i = 0; i < n; i++) if (!removed[i]) centres[nc++] = i;
        Key best{~0ULL, ~0ULL};
        HV h[MAXV], hf[MAXV], ch[MAXV], chf[MAXV];
        int order[MAXV], parent[MAXV], st[MAXV], kids[MAXV];
        for (int ci = 0; ci < nc; ci++) {
            int root = centres[ci];
            int top = 0, cnt = 0;
            st[top++] = root; parent[root] = -1;
            while (top) { int x = st[--top]; order[cnt++] = x; for (int j = off[x]; j < off[x + 1]; j++) { int y = nb[j]; if (y != parent[x]) { parent[y] = x; st[top++] = y; } } }
            for (int k = cnt - 1; k >= 0; k--) {
                int x = order[k];
                int nk = 0;
                for (int j = off[x]; j < off[x + 1]; j++) { int y = nb[j]; if (y != parent[x]) { kids[nk] = y; ch[nk] = h[y]; chf[nk] = hf[y]; nk++; } }
                if (twin && nk >= 2) {
                    int ya = -1, yb = -1;
                    for (int p = 0; p < nk && ya < 0; p++)
                        for (int q = p + 1; q < nk; q++)
                            if (ch[p].a == chf[q].a && ch[p].b == chf[q].b) { ya = kids[p]; yb = kids[q]; break; }
                    if (ya >= 0) {
                        // twins at x: delete both branches, set x to f, renormalise
                        bool del[MAXV]; for (int i = 0; i < n; i++) del[i] = false;
                        int stk[MAXV], sp = 0; stk[sp++] = ya; stk[sp++] = yb;
                        while (sp) { int z = stk[--sp]; del[z] = true; for (int j = off[z]; j < off[z + 1]; j++) { int w = nb[j]; if (w != parent[z]) stk[sp++] = w; } }
                        uint8_t lab2[MAXV]; for (int i = 0; i < n; i++) lab2[i] = C.lab[i];
                        lab2[x] = SF;
                        EdgeList E2;
                        for (auto& e : C.E) if (!del[e.first] && !del[e.second]) E2.push_back(e);
                        vector<Comp> parts;
                        normalise(n, lab2, E2, parts);
                        for (auto& P : parts) canonAll(P, res);
                        return;
                    }
                }
                sort(ch, ch + nk, hvless);
                sort(chf, chf + nk, hvless);
                u64 a = smix(1000 + C.lab[x]), b = smix2(2000 + C.lab[x]);
                for (int t = 0; t < nk; t++) { a = smix(a ^ ch[t].a) + 0x1234567ULL; b = smix2(b + ch[t].b) ^ 0x7654321ULL; }
                a = smix(a + nk); b = smix2(b ^ (nk * 0x10001ULL));
                u64 fa = smix(1000 + FLIP[C.lab[x]]), fb = smix2(2000 + FLIP[C.lab[x]]);
                for (int t = 0; t < nk; t++) { fa = smix(fa ^ chf[t].a) + 0x1234567ULL; fb = smix2(fb + chf[t].b) ^ 0x7654321ULL; }
                fa = smix(fa + nk); fb = smix2(fb ^ (nk * 0x10001ULL));
                h[x] = {a, b}; hf[x] = {fa, fb};
            }
            Key k1{h[root].a, h[root].b}, k2{hf[root].a, hf[root].b};
            if (k1 < best) best = k1;
            if (k2 < best) best = k2;
        }
        res.push_back({C, best});
    }

    int grundyComp(Comp& C, const Key& key) {
        int r = memo.get(key);
        if (r >= 0) return r;
        nodes++;
        int n = C.n, m = C.E.size();
        int deg[MAXV];
        for (int i = 0; i < n; i++) deg[i] = 0;
        for (auto& e : C.E) { deg[e.first]++; deg[e.second]++; }
        u64 opts[4] = {0, 0, 0, 0};
        uint8_t lab2[MAXV];
        EdgeList E2;
        vector<Comp> parts; vector<pair<Comp, Key>> cres;
        for (int ei = 0; ei < m; ei++) {
            for (int d = 0; d < 2; d++) {
                int t = d ? C.E[ei].second : C.E[ei].first;
                int hh = d ? C.E[ei].first : C.E[ei].second;
                if (!canTail(C.lab[t], deg[t]) || !canHead(C.lab[hh], deg[hh])) continue;
                for (int i = 0; i < n; i++) lab2[i] = C.lab[i];
                lab2[t] = OUTA[lab2[t]]; lab2[hh] = INA[lab2[hh]];
                E2.clear();
                for (int j = 0; j < m; j++) if (j != ei) E2.push_back(C.E[j]);
                parts.clear();
                normalise(n, lab2, E2, parts);
                int x = 0;
                for (auto& P : parts) {
                    cres.clear();
                    canonAll(P, cres);
                    for (auto& pk : cres) x ^= grundyComp(pk.first, pk.second);
                }
                opts[x >> 6] |= 1ULL << (x & 63);
            }
        }
        r = 0;
        while ((opts[r >> 6] >> (r & 63)) & 1) r++;
        memo.put(key, r);
        return r;
    }

    // Grundy value of an arbitrary labelled forest
    int grundyForest(int n, uint8_t* lab, const vector<pair<int, int>>& Ev) {
        EdgeList E; for (auto& e : Ev) E.push_back(e);
        vector<Comp> parts;
        uint8_t l2[MAXV]; for (int i = 0; i < n; i++) l2[i] = lab[i];
        normalise(n, l2, E, parts);
        int x = 0;
        for (auto& P : parts) {
            vector<pair<Comp, Key>> cres;
            canonAll(P, cres);
            for (auto& pk : cres) x ^= grundyComp(pk.first, pk.second);
        }
        return x;
    }

    // Grundy value of a piece: tree whose leaves are f and other vertices n
    int grundyPiece(int n, const vector<pair<int, int>>& E) {
        uint8_t lab[MAXV];
        vector<int> deg(n, 0);
        for (auto& e : E) { deg[e.first]++; deg[e.second]++; }
        for (int i = 0; i < n; i++) lab[i] = (deg[i] <= 1) ? SF : SN;
        return grundyForest(n, lab, E);
    }

    // Grundy value of an original tree (pendant edges removed, special vertices f)
    int grundyTree(int n, const vector<pair<int, int>>& E, int* mOut) {
        vector<int> deg(n, 0);
        for (auto& e : E) { deg[e.first]++; deg[e.second]++; }
        uint8_t lab[MAXV];
        for (int i = 0; i < n; i++) lab[i] = SN;
        vector<pair<int, int>> M;
        for (auto& e : E) {
            if (deg[e.first] == 1) lab[e.second] = SF;
            else if (deg[e.second] == 1) lab[e.first] = SF;
        }
        for (auto& e : E) if (deg[e.first] > 1 && deg[e.second] > 1) M.push_back(e);
        if (mOut) *mOut = M.size();
        return grundyForest(n, lab, M);
    }
};
