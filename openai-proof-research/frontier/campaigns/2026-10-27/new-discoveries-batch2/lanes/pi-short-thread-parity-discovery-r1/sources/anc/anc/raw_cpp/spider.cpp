// Independent spider solver (my own derivation from the raw rules, validated
// against the raw brute force).  State of the centre component: status s of the
// centre c in {n,i,o} (status "both in and out" splits the component) and the
// multiset of attached legs (h, far), h>=1 unmarked edges counted from c, far in
// {free, IN, OUT}.  Detached runs are solved by a separate DP over raw path moves.
//
// Modes:
//   ./spider val x1 x2 ... xk        -> Grundy value of S(x1..xk) (k<=4)
//   ./spider pos x1..xk ; s h1 f1 ... -> (unused)
//   ./spider sweep L                  -> all 3-leg spiders with legs<=L: per-g minimal-m spider etc.
//   ./spider family x y Z             -> values g(S(x,y,z)) for z=1..Z
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64;

enum { FREE = 0, IN = 1, OUT = 2 };   // also run constraints: 0 none, 1 = L (towards c), 2 = R (away from c)
enum { SN = 0, SI = 1, SO = 2, SF = 3 };

int K;                       // max run length
vector<array<array<int,3>,3>> RUN;  // RUN[k][a][b]
void build_runs(int maxk) {
    K = maxk; RUN.assign(maxk + 1, {});
    for (int k = 0; k <= maxk; k++) for (int a = 0; a < 3; a++) for (int b = 0; b < 3; b++) {
        if (k == 0) { RUN[k][a][b] = 0; continue; }
        // options: orient e_j (1..k) in direction d in {1(L),2(R)}
        vector<char> seen(2 * k + 4, 0);
        for (int j = 1; j <= k; j++) for (int d = 1; d <= 2; d++) {
            if (j == 1 && a != 0 && a != d) continue;
            if (j == k && b != 0 && b != d) continue;
            int v = RUN[j - 1][a][d] ^ RUN[k - j][d][b];
            if (v < (int)seen.size()) seen[v] = 1;
        }
        int r = 0; while (r < (int)seen.size() && seen[r]) r++;
        RUN[k][a][b] = r;
    }
}
static inline int sstep(int s, int arc /*IN or OUT relative to c*/) {
    // centre gains an incoming (IN) or outgoing (OUT) arc
    if (s == SN) return arc == IN ? SI : SO;
    if (s == SI) return arc == IN ? SI : SF;
    if (s == SO) return arc == OUT ? SO : SF;
    return SF;
}
// leg code: h>=1, far in {0,1,2}: code = (h-1)*3 + far + 1
static inline int code(int h, int f) { return (h - 1) * 3 + f + 1; }
static inline int hof(int c) { return (c - 1) / 3 + 1; }
static inline int fof(int c) { return (c - 1) % 3; }

// ---------- storage: hash for generic, dense for 3-leg sweep
struct Hash {
    vector<u64> k; vector<int16_t> v; size_t mask, used = 0;
    Hash() { k.assign(1 << 22, ~0ULL); v.assign(1 << 22, 0); mask = (1 << 22) - 1; }
    static inline u64 h(u64 x) { x ^= x >> 33; x *= 0xff51afd7ed558ccdULL; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL; x ^= x >> 33; return x; }
    int get(u64 key) { size_t i = h(key) & mask; while (k[i] != ~0ULL) { if (k[i] == key) return v[i]; i = (i + 1) & mask; } return -1; }
    void put(u64 key, int val) {
        if ((used + 1) * 2 > k.size()) { vector<u64> ok; vector<int16_t> ov; ok.swap(k); ov.swap(v); k.assign(ok.size() * 2, ~0ULL); v.assign(ok.size() * 2, 0); mask = k.size() - 1; used = 0; for (size_t i = 0; i < ok.size(); i++) if (ok[i] != ~0ULL) put(ok[i], ov[i]); }
        size_t i = h(key) & mask; while (k[i] != ~0ULL) { if (k[i] == key) { v[i] = val; return; } i = (i + 1) & mask; }
        k[i] = key; v[i] = val; used++;
    }
};
Hash H;
bool dense = false; int DC = 0; vector<uint8_t> D;   // dense: value+1, 0 = unknown

int G(int s, vector<int> legs);  // legs: codes, any order

int Gsorted(int s, vector<int>& legs) {
    // legs sorted descending, all >=1
    int d = legs.size();
    if (d == 0) return 0;
    u64 key = 0; size_t di = 0;
    if (dense) {
        int c[3] = {0, 0, 0}; for (int i = 0; i < d; i++) c[i] = legs[i];
        di = (((size_t)s * DC + c[0]) * DC + c[1]) * DC + c[2];
        if (D[di]) return D[di] - 1;
    } else {
        key = s; for (int i = 0; i < d; i++) key = (key << 14) | legs[i]; key = (key << 3) | d;
        int r = H.get(key); if (r >= 0) return r;
    }
    static thread_local int dummy;
    vector<char> seen(1024, 0);
    for (int t = 0; t < d; t++) {
        if (t > 0 && legs[t] == legs[t - 1]) continue;  // identical legs give identical options
        int h = hof(legs[t]), far = fof(legs[t]);
        vector<int> rest; rest.reserve(d);
        for (int u = 0; u < d; u++) if (u != t) rest.push_back(legs[u]);
        for (int j = 1; j <= h; j++) for (int dl = IN; dl <= OUT; dl++) {
            if (j == h && far != FREE && dl != far) continue;
            if (j == 1 && d == 1) {   // centre has a single unmarked edge
                // OUT gives c an outgoing arc: legal iff c already has an incoming arc
                if (dl == OUT && s != SI) continue;
                if (dl == IN && s != SO) continue;
            }
            int det = RUN[h - j][dl][far];
            int att;
            if (j >= 2) {
                vector<int> nl = rest; nl.push_back(code(j - 1, dl));
                att = G(s, nl);
            } else {
                int s2 = sstep(s, dl);
                if (s2 == SF) { att = 0; for (int c : rest) att ^= RUN[hof(c)][FREE][fof(c)]; }
                else att = G(s2, rest);
            }
            int v = det ^ att;
            if (v >= (int)seen.size()) seen.resize(v + 1, 0);
            seen[v] = 1;
        }
    }
    int r = 0; while (r < (int)seen.size() && seen[r]) r++;
    if (dense) D[di] = r + 1; else H.put(key, r);
    return r;
}
int G(int s, vector<int> legs) { sort(legs.rbegin(), legs.rend()); return Gsorted(s, legs); }

int spider_value(const vector<int>& xs) {
    vector<int> legs; for (int x : xs) legs.push_back(code(x, FREE));
    return G(SN, legs);
}

int main(int argc, char** argv) {
    string mode = argv[1];
    if (mode == "val") {
        vector<int> xs; int mx = 0; for (int i = 2; i < argc; i++) { xs.push_back(atoi(argv[i])); mx = max(mx, xs.back()); }
        build_runs(mx + 2);
        printf("%d\n", spider_value(xs));
    } else if (mode == "batch") {  // read lines of legs from stdin
        build_runs(700);
        string line;
        while (getline(cin, line)) { istringstream in(line); vector<int> xs; int x; while (in >> x) xs.push_back(x); if (xs.empty()) continue; printf("%d\n", spider_value(xs)); fflush(stdout); }
    } else if (mode == "runs") {
        int M = atoi(argv[2]); build_runs(M); int bad = 0;
        for (int k = 0; k <= M; k++) {
            int A = RUN[k][0][0], B1 = RUN[k][0][2], B2 = RUN[k][0][1], B3 = RUN[k][2][0], B4 = RUN[k][1][0];
            int C1 = RUN[k][2][2], C2 = RUN[k][1][1], D1 = RUN[k][2][1], D2 = RUN[k][1][2];
            int Dexp = (k >= 2 && k % 2 == 0) ? 1 : 0;
            if (A != k % 2 || B1 != k || B2 != k || B3 != k || B4 != k || C1 != k % 2 || C2 != k % 2 || D1 != Dexp || D2 != Dexp) { bad++; printf("run mismatch k=%d\n", k); }
        }
        printf("runs checked up to %d, mismatches %d\n", M, bad);
    } else if (mode == "sweep") {
        int L = atoi(argv[2]); build_runs(L + 2);
        dense = true; DC = 3 * L + 1; D.assign((size_t)4 * DC * DC * DC, 0);
        map<int, tuple<int,int,int,int>> best; // g -> (m,x,y,z)
        long cnt = 0; int Lmark[] = {30, 80, 120}; map<int,int> maxg;
        vector<long> hist(256, 0);
        for (int z = 1; z <= L; z++) for (int y = 1; y <= z; y++) for (int x = 1; x <= y; x++) {
            int g = spider_value({x, y, z}); cnt++; hist[g]++;
            int m = x + y + z;
            auto cand = make_tuple(m, x, y, z);
            if (!best.count(g) || cand < best[g]) best[g] = cand;
            for (int l : Lmark) if (z <= l) maxg[l] = max(maxg[l], g);
        }
        printf("spiders: %ld\n", cnt);
        for (auto& [g, t] : best) printf("g=%d  S(%d,%d,%d)  m=%d  count=%ld\n", g, get<1>(t), get<2>(t), get<3>(t), get<0>(t), hist[g]);
        for (auto& [l, g] : maxg) printf("max g for legs<=%d: %d\n", l, g);
    } else if (mode == "family") {
        int x = atoi(argv[2]), y = atoi(argv[3]), Z = atoi(argv[4]); build_runs(Z + 2);
        for (int z = 1; z <= Z; z++) printf("%d%c", spider_value({x, y, z}), z == Z ? '\n' : ' ');
    }
}
