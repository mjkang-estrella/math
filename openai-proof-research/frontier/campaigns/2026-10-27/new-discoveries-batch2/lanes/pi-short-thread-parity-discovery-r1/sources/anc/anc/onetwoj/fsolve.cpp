// fsolve.cpp -- fixed-short-legs solver for the Game of Arrows on spiders S(x,y,z),
// x,y fixed, z = 1..Z.  Written from Prop. 6.1 (spider-state recursion) of goc_trees.tex.
//
// State: centre status s in {N,I,O} (F is closed form N1), short legs X,Y with codes
//   0 = detached, code(h,phi) = (h-1)*3+phi+1, phi in {F=0, IN=1, OUT=2};
// long leg (h, phi) stored in dense tables V[sigma][h*3+phi].
// Usage:  fsolve x y Z [dump]
//   prints G(S(x,y,z)) for z=1..Z on one line; with "dump" also prints the long-leg
//   tables for all sigma (for structural analysis).
#include <bits/stdc++.h>
using namespace std;
enum { F = 0, IN = 1, OUT = 2 };
enum { SN = 0, SI = 1, SO = 2, SF = 3 };
static inline int rho(int h, int d, int phi) {  // detached run, near end blocked d
    if (h == 0) return 0;
    if (phi == F) return h;
    if (phi == d) return h & 1;
    return (h >= 2 && h % 2 == 0) ? 1 : 0;
}
static inline int rhoF(int h, int phi) {  // detached run, near end free
    if (h == 0) return 0;
    if (phi == F) return h & 1;
    return h;
}
static inline int sstep(int s, int d) {  // d = IN: arc into c; OUT: arc out of c
    if (s == SN) return d == IN ? SI : SO;
    if (s == SI) return d == IN ? SI : SF;
    if (s == SO) return d == OUT ? SO : SF;
    return SF;
}
static inline int hof(int c) { return (c - 1) / 3 + 1; }
static inline int fof(int c) { return (c - 1) % 3; }
static inline int code(int h, int f) { return (h - 1) * 3 + f + 1; }

int X, Y, Z;
int NX, NY;  // number of codes incl. 0
// short-only states (long leg detached): memo
map<array<int, 3>, int> shortMemo;
int shortGamma(int s, int cx, int cy) {
    int att = (cx > 0) + (cy > 0);
    if (s == SF) {
        int v = 0;
        if (cx) v ^= rhoF(hof(cx), fof(cx));
        if (cy) v ^= rhoF(hof(cy), fof(cy));
        return v;
    }
    if (att == 0) return 0;
    if (att == 1) {
        int c = cx ? cx : cy;
        assert(s == SI || s == SO);
        return rho(hof(c), s == SI ? OUT : IN, fof(c));
    }
    assert(s == SI || s == SO);
    array<int, 3> key = {s, cx, cy};
    auto it = shortMemo.find(key);
    if (it != shortMemo.end()) return it->second;
    set<int> opts;
    int cc[2] = {cx, cy};
    for (int t = 0; t < 2; t++) {
        int h = hof(cc[t]), phi = fof(cc[t]);
        for (int j = 1; j <= h; j++)
            for (int d = IN; d <= OUT; d++) {
                if (j == h && phi != F && d != phi) continue;
                int det = rho(h - j, d, phi);
                int nc[2] = {cc[0], cc[1]};
                int v;
                if (j >= 2) {
                    nc[t] = code(j - 1, d);
                    v = shortGamma(s, nc[0], nc[1]);
                } else {
                    nc[t] = 0;
                    v = shortGamma(sstep(s, d), nc[0], nc[1]);
                }
                opts.insert(det ^ v);
            }
    }
    int g = 0;
    while (opts.count(g)) g++;
    shortMemo[key] = g;
    return g;
}

// sigma index
static inline int sig(int s, int cx, int cy) { return (s * NX + cx) * NY + cy; }
vector<vector<int32_t>> V;  // V[sigma][h*3+phi]
vector<int> stamp;
int stampId = 0;

// Gamma of state (s,cx,cy,long=(h,phi)), h>=1; long-leg-detached handled by shortGamma.
// Gamma with s in {I,O} and only the long leg attached: N2.
static inline int getLong(int s, int cx, int cy, int h, int phi) {
    if (s == SF) {
        int v = rhoF(h, phi);
        if (cx) v ^= rhoF(hof(cx), fof(cx));
        if (cy) v ^= rhoF(hof(cy), fof(cy));
        return v;
    }
    if (s != SN && cx == 0 && cy == 0) return rho(h, s == SI ? OUT : IN, phi);
    return V[sig(s, cx, cy)][h * 3 + phi];
}

void computeState(int s, int cx, int cy, int h, int phi) {
    ++stampId;
    int maxv = 0;
    auto add = [&](int v) {
        if (v >= (int)stamp.size()) stamp.resize(2 * v + 16, 0);
        stamp[v] = stampId;
    };
    // short-leg moves
    int cc[2] = {cx, cy};
    for (int t = 0; t < 2; t++) {
        if (!cc[t]) continue;
        int hs = hof(cc[t]), ps = fof(cc[t]);
        for (int j = 1; j <= hs; j++)
            for (int d = IN; d <= OUT; d++) {
                if (j == hs && ps != F && d != ps) continue;
                int det = rho(hs - j, d, ps);
                int nc[2] = {cc[0], cc[1]};
                int v;
                if (j >= 2) {
                    nc[t] = code(j - 1, d);
                    v = getLong(s, nc[0], nc[1], h, phi);
                } else {
                    nc[t] = 0;
                    v = getLong(sstep(s, d), nc[0], nc[1], h, phi);
                }
                add(det ^ v);
            }
    }
    // long-leg moves
    for (int j = 1; j <= h; j++)
        for (int d = IN; d <= OUT; d++) {
            if (j == h && phi != F && d != phi) continue;
            int det = rho(h - j, d, phi);
            int v;
            if (j >= 2)
                v = getLong(s, cx, cy, j - 1, d);
            else
                v = shortGamma(sstep(s, d), cx, cy);
            add(det ^ v);
        }
    int g = 0;
    while (g < (int)stamp.size() && stamp[g] == stampId) g++;
    V[sig(s, cx, cy)][h * 3 + phi] = g;
    (void)maxv;
}

int main(int argc, char** argv) {
    X = atoi(argv[1]);
    Y = atoi(argv[2]);
    Z = atoi(argv[3]);
    bool dump = argc > 4 && string(argv[4]) == "dump";
    NX = 3 * X + 1;
    NY = 3 * Y + 1;
    V.assign(3 * NX * NY, vector<int32_t>());
    // valid sigmas: s=N: cx,cy both attached; s in {I,O}: exactly one attached
    vector<array<int, 3>> order;
    for (int s : {SI, SO})
        for (int cx = 0; cx < NX; cx++)
            for (int cy = 0; cy < NY; cy++)
                if ((cx > 0) + (cy > 0) == 1) order.push_back({s, cx, cy});
    for (int cx = 1; cx < NX; cx++)
        for (int cy = 1; cy < NY; cy++) order.push_back({SN, cx, cy});
    // only codes reachable: (h,F) only for h == full length
    auto okcode = [&](int c, int L) { return c == 0 || (fof(c) == F ? hof(c) == L : hof(c) < L); };
    vector<array<int, 3>> ord2;
    for (auto& a : order)
        if (okcode(a[1], X) && okcode(a[2], Y)) ord2.push_back(a);
    order = ord2;
    for (auto& a : order) V[sig(a[0], a[1], a[2])].assign(3 * (Z + 1), -1);
    stamp.assign(1 << 16, 0);
    for (int h = 1; h <= Z; h++)
        for (int phi : {IN, OUT, F})
            for (auto& a : order) computeState(a[0], a[1], a[2], h, phi);
    for (int z = 1; z <= Z; z++)
        printf("%d%c", V[sig(SN, code(X, F), code(Y, F))][z * 3 + F], z == Z ? '\n' : ' ');
    if (dump) {
        for (auto& a : order) {
            int s = a[0], cx = a[1], cy = a[2];
            for (int phi : {IN, OUT, F}) {
                printf("S %d X %d %d Y %d %d phi %d :", s, cx ? hof(cx) : 0, cx ? fof(cx) : -1,
                       cy ? hof(cy) : 0, cy ? fof(cy) : -1, phi);
                for (int h = 1; h <= Z; h++) printf(" %d", V[sig(s, cx, cy)][h * 3 + phi]);
                printf("\n");
            }
        }
    }
}
