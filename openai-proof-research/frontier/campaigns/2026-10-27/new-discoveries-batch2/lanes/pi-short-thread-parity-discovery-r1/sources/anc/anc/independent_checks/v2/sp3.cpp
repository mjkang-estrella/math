// Independent 3-legged spider-state solver: Prop 6.1 (with (N1)-(N3)) + Thm 4.3.
// Usage:
//   sp3 thm  JMAX ZMAX            -> verify Thm onetwoj, window remark, corollary period/density
//   sp3 blk  XMAX KMAX            -> verify prop:blockedleg for gadgets K = centre + free legs (x,y)
//   sp3 val  x y z                -> print Gamma(n;(x,F),(y,F),(z,F))
#include <bits/stdc++.h>
using namespace std;

enum { F = 0, IN = 1, OUT = 2 };
enum { SN = 0, SI = 1, SO = 2, SF = 3 };

static int Xmax[3];
static int dimL[3];
static vector<int16_t> memo;

static inline int rho(int h, int d, int phi) {
    if (phi == F) return h;
    if (phi == d) return h & 1;
    return (h >= 2 && (h % 2 == 0)) ? 1 : 0;
}
static inline int rhofree(int h, int phi) { return phi == F ? (h & 1) : h; }
static inline int sdot(int s, int d) {
    if (d == IN) { static const int t[4] = {SI, SI, SF, SF}; return t[s]; }
    static const int t[4] = {SO, SF, SO, SF}; return t[s];
}
static inline size_t key(int s, const int* h, const int* p) {
    size_t k = s;
    for (int t = 0; t < 3; t++) k = k * dimL[t] + (h[t] * 3 + p[t]);
    return k;
}

int Gam(int s, const int* h, const int* p) {
    int cnt = 0, last = -1;
    for (int t = 0; t < 3; t++) if (h[t] > 0) { cnt++; last = t; }
    if (cnt == 0) return 0;                                   // (N3)
    if (s == SF) { int v = 0; for (int t = 0; t < 3; t++) if (h[t] > 0) v ^= rhofree(h[t], p[t]); return v; } // (N1)
    if ((s == SI || s == SO) && cnt == 1) return rho(h[last], s == SI ? OUT : IN, p[last]);             // (N2)
    size_t k = key(s, h, p);
    if (memo[k] >= 0) return memo[k];
    vector<char> seen(2 * (h[0] + h[1] + h[2]) + 8, 0);
    for (int t = 0; t < 3; t++) {
        if (h[t] <= 0) continue;
        int hh = h[t], ph = p[t];
        for (int j = 1; j <= hh; j++) for (int d = IN; d <= OUT; d++) {
            if (j == hh && ph != F && d != ph) continue;
            int det = rho(hh - j, d, ph);
            int nh[3] = {h[0], h[1], h[2]}, np[3] = {p[0], p[1], p[2]};
            int v;
            if (j >= 2) { nh[t] = j - 1; np[t] = d; v = det ^ Gam(s, nh, np); }
            else { nh[t] = 0; np[t] = 0; v = det ^ Gam(sdot(s, d), nh, np); }
            if (v < (int)seen.size()) seen[v] = 1;
        }
    }
    int m = 0; while (m < (int)seen.size() && seen[m]) m++;
    memo[k] = m;
    return m;
}

void setup(int a, int b, int c) {
    Xmax[0] = a; Xmax[1] = b; Xmax[2] = c;
    size_t tot = 4;
    for (int t = 0; t < 3; t++) { dimL[t] = 3 * (Xmax[t] + 1); tot *= dimL[t]; }
    memo.assign(tot, -1);
}

int G3(int s, int h0, int p0, int h1, int p1, int h2, int p2) {
    int h[3] = {h0, h1, h2}, p[3] = {p0, p1, p2};
    return Gam(s, h, p);
}

static bool inS(int j, long b) { return (b & (j - 1)) == 0; }
static int formula(int j, int z) {  // Thm onetwoj(b) formula, needs z-2j+2>=0
    int w = z - 2 * j + 2; int b = w / 4, r = w % 4;
    if (inS(j, b)) return r == 2 ? 1 : 0;
    return z % 2;
}

int main(int argc, char** argv) {
    string mode = argv[1];
    if (mode == "val") {
        int x = atoi(argv[2]), y = atoi(argv[3]), z = atoi(argv[4]);
        setup(x, y, z);
        printf("%d\n", G3(SN, x, F, y, F, z, F));
        return 0;
    }
    if (mode == "thm") {
        int JMAX = atoi(argv[2]), ZMAX = atoi(argv[3]);
        long totbad = 0;
        for (int j = 1; j <= JMAX; j++) {
            int y = 2 * j;
            setup(1, y, ZMAX);
            vector<int> g(ZMAX + 1, -1);
            for (int z = 1; z <= ZMAX; z++) g[z] = G3(SN, 1, F, y, F, z, F);
            if (j == 1) {
                int bad = 0;
                for (int z = 1; z <= ZMAX; z++) if (g[z] != (z + 1) % 2) bad++;
                printf("j=1: part (a) (z+1)%%2 for 1<=z<=%d: mismatches=%d\n", ZMAX, bad);
                totbad += bad;
                continue;
            }
            int bad = 0;
            for (int z = 2 * j + 2; z <= ZMAX; z++) if (g[z] != formula(j, z)) bad++;
            totbad += bad;
            // window: smallest z0 such that formula holds for all z0<=z<=ZMAX (z>=2j-2 domain)
            int z0 = ZMAX + 1;
            for (int z = ZMAX; z >= 2 * j - 2 && z >= 1; z--) { if (g[z] == formula(j, z)) z0 = z; else break; }
            // failures below 2j+2 (within formula domain)
            string fl;
            for (int z = max(1, 2 * j - 2); z < 2 * j + 2; z++) if (g[z] != formula(j, z)) fl += to_string(z) + " ";
            // extend formula to z=2j-3 (w=-1): b=-1? report actual value and both parities
            int zm = 2 * j - 3;
            string below;
            if (zm >= 1) below = "g(2j-3)=" + to_string(g[zm]) + " (formula ext. would be 1-?)";
            // least period on z>=2j+2
            int K = 1; while (K < j) K <<= 1;
            int pmin = -1;
            for (int p = 1; p <= (ZMAX - (2 * j + 2)) / 2; p++) {
                bool ok = true;
                for (int z = 2 * j + 2; z + p <= ZMAX; z++) if (g[z] != g[z + p]) { ok = false; break; }
                if (ok) { pmin = p; break; }
            }
            // density of violations over one period 4K (gv != (z+1)%2)
            int viol = 0;
            for (int z = 2 * j + 2; z < 2 * j + 2 + 4 * K; z++) if (g[z] != (z + 1) % 2) viol++;
            int sd = __builtin_popcount(j - 1);
            double dens = 1.0 - 0.75 * pow(2.0, -sd);
            // parity-holds characterization check
            int pc = 0;
            for (int z = 2 * j + 2; z <= ZMAX; z++) {
                int w = z - 2 * j + 2, b = w / 4, r = w % 4;
                bool holds = (g[z] == (z + 1) % 2);
                bool pred = (r == 1 || r == 2 || r == 3) && inS(j, b);
                if (holds != pred) pc++;
            }
            totbad += pc;
            printf("j=%2d: thm(b) mismatches z in [%d,%d]: %d | formula holds from z0=%d (2j-2=%d) | "
                   "fails in [2j-2,2j+1]: {%s} | g(2j-3)=%d formula-would-need-check | least period=%d (4K=%d) | "
                   "viol density=%d/%d=%.6f claim %.6f | parity-char mismatches=%d\n",
                   j, 2 * j + 2, ZMAX, bad, z0, 2 * j - 2, fl.c_str(), zm >= 1 ? g[zm] : -1, pmin, 4 * K, viol, 4 * K,
                   (double)viol / (4 * K), dens, pc);
            fflush(stdout);
        }
        printf("THM TOTAL mismatches=%ld\n", totbad);
        return 0;
    }
    if (mode == "blk") {
        int XM = atoi(argv[2]), KM = atoi(argv[3]);
        long viol = 0, rev = 0, gadgets = 0;
        for (int x = 1; x <= XM; x++) for (int y = x; y <= XM; y++) {
            setup(x, y, KM);
            vector<int> h(KM + 1), ho(KM + 1);
            for (int k = 1; k <= KM; k++) { h[k] = G3(SN, x, F, y, F, k, IN); ho[k] = G3(SN, x, F, y, F, k, OUT); }
            for (int k = 1; k <= KM; k++) if (h[k] != ho[k]) rev++;
            int bad = 0;
            for (int k = 2; k <= KM; k++) {
                if (h[k] == h[k - 1]) bad++;
                for (int kp = 1; kp <= k - 2; kp++) if (h[k] == h[kp] || h[k] == (h[kp] ^ 1)) bad++;
            }
            // floor(h/2) taken at most twice, consecutive
            map<int, vector<int>> occ;
            for (int k = 1; k <= KM; k++) occ[h[k] / 2].push_back(k);
            int bad2 = 0;
            for (auto& kv : occ) { auto& v = kv.second; if (v.size() > 2 || (v.size() == 2 && v[1] != v[0] + 1)) bad2++; }
            viol += bad + bad2; gadgets++;
            // eventual form h(k)=k+c ? report c on last 40 values if constant
            int c = h[KM] - KM; bool lin = true;
            for (int k = KM - 40; k <= KM; k++) if (h[k] - k != c) lin = false;
            printf("gadget (%d,%d): blockedleg violations=%d floor-viol=%d  tail: %s c=%d  h(1..12)=", x, y, bad, bad2,
                   lin ? "h=k+c" : "nonlinear", c);
            for (int k = 1; k <= 12; k++) printf("%d ", h[k]);
            printf("\n");
            fflush(stdout);
        }
        printf("BLK gadgets=%ld total violations=%ld reversal mismatches=%ld\n", gadgets, viol, rev);
        return 0;
    }
    return 1;
}
