// Raw-rules brute-force Game of Arrows solver (C++ twin of raw.py).
// Input (stdin), one instance per line:
//   n  u1 v1 ... u_{n-1} v_{n-1}  K  t1 h1 ... tK hK  [opt]
// (K pre-marked arcs tail->head).  If the trailing token opt is 1, also print the
// value of every legal move from the given position.
// Output per line: g  m   [ ; tail>head:value ... ]
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64;

struct Table {
    vector<u64> keys; vector<uint8_t> vals; vector<uint32_t> stamp; uint32_t cur = 1; size_t mask, used = 0;
    Table() { init(1 << 20); }
    void init(size_t cap) { keys.assign(cap, 0); vals.assign(cap, 0); stamp.assign(cap, 0); mask = cap - 1; used = 0; cur = 1; }
    void clear() { cur++; used = 0; if (cur == 0) { init(keys.size()); } }
    static inline u64 h(u64 k) { k ^= k >> 33; k *= 0xff51afd7ed558ccdULL; k ^= k >> 33; k *= 0xc4ceb9fe1a85ec53ULL; k ^= k >> 33; return k; }
    int get(u64 k) const { size_t i = h(k) & mask; while (stamp[i] == cur) { if (keys[i] == k) return vals[i]; i = (i + 1) & mask; } return -1; }
    void put(u64 k, int v) {
        if ((used + 1) * 2 > keys.size()) grow();
        size_t i = h(k) & mask; while (stamp[i] == cur) { if (keys[i] == k) { vals[i] = v; return; } i = (i + 1) & mask; }
        stamp[i] = cur; keys[i] = k; vals[i] = v; used++;
    }
    void grow() {
        vector<u64> ok; vector<uint8_t> ov; vector<uint32_t> os; ok.swap(keys); ov.swap(vals); os.swap(stamp); uint32_t oc = cur;
        init(ok.size() * 2);
        for (size_t i = 0; i < ok.size(); i++) if (os[i] == oc) put(ok[i], ov[i]);
    }
};

int n, E;
vector<int> eu, ev;
vector<u64> inc, flp;
Table T;

static inline bool bad(int w, u64 marked, u64 dirm) {
    u64 im = inc[w];
    if (im == 0 || (marked & im) != im) return false;
    u64 x = (dirm ^ flp[w]) & im;  // 0 bit = into w
    return x == 0 || x == im;
}

int g(u64 marked, u64 dirm) {
    u64 key = marked | (dirm << 32);
    int r = T.get(key);
    if (r >= 0) return r;
    u64 opts[4] = {0, 0, 0, 0};
    for (int i = 0; i < E; i++) {
        if ((marked >> i) & 1) continue;
        u64 nm = marked | (1ULL << i);
        for (int d = 0; d < 2; d++) {
            u64 nd = dirm | ((u64)d << i);
            if (bad(eu[i], nm, nd) || bad(ev[i], nm, nd)) continue;
            int v = g(nm, nd);
            opts[v >> 6] |= 1ULL << (v & 63);
        }
    }
    r = 0;
    while ((opts[r >> 6] >> (r & 63)) & 1) r++;
    T.put(key, r);
    return r;
}

int main() {
    string line;
    while (getline(cin, line)) {
        if (line.empty()) continue;
        istringstream in(line);
        in >> n; E = n - 1;
        eu.assign(E, 0); ev.assign(E, 0);
        inc.assign(n, 0); flp.assign(n, 0);
        vector<int> deg(n, 0);
        for (int i = 0; i < E; i++) {
            in >> eu[i] >> ev[i];
            inc[eu[i]] |= 1ULL << i; inc[ev[i]] |= 1ULL << i; flp[eu[i]] |= 1ULL << i;
            deg[eu[i]]++; deg[ev[i]]++;
        }
        int K = 0; in >> K;
        u64 marked = 0, dirm = 0;
        for (int k = 0; k < K; k++) {
            int t, h; in >> t >> h;
            int found = -1;
            for (int i = 0; i < E; i++) {
                if (eu[i] == t && ev[i] == h) { found = i; marked |= 1ULL << i; }
                else if (eu[i] == h && ev[i] == t) { found = i; marked |= 1ULL << i; dirm |= 1ULL << i; }
            }
            if (found < 0) { fprintf(stderr, "bad arc\n"); return 1; }
        }
        int opt = 0; in >> opt;
        for (int w = 0; w < n; w++) if (bad(w, marked, dirm)) { fprintf(stderr, "illegal start position\n"); return 1; }
        T.clear();
        int m = 0;
        for (int i = 0; i < E; i++) if (deg[eu[i]] > 1 && deg[ev[i]] > 1) m++;
        int r = g(marked, dirm);
        printf("%d %d", r, m);
        if (opt) {
            printf(" ;");
            for (int i = 0; i < E; i++) {
                if ((marked >> i) & 1) continue;
                u64 nm = marked | (1ULL << i);
                for (int d = 0; d < 2; d++) {
                    u64 nd = dirm | ((u64)d << i);
                    if (bad(eu[i], nm, nd) || bad(ev[i], nm, nd)) continue;
                    int t = d ? ev[i] : eu[i], h = d ? eu[i] : ev[i];
                    printf(" %d>%d:%d", t, h, g(nm, nd));
                }
            }
        }
        printf("\n");
        fflush(stdout);
    }
}
