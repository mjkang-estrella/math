// famstates.cpp -- all spider-state families of S(x,y,.) with a long third leg.
// Implements Proposition 6.1 (spider-state recursion) of the paper directly.
//
// Leg state: (h, phi), h>=1 unmarked edges attached to the centre, phi in {F=0, IN=1, OUT=2}
// (IN = first arc on the leg points toward the centre; OUT = away), or 0 = detached.
// Centre status: N=0, I=1, O=2, F=3.
// Family:  V(sigma, r, f) = Gamma(s; short legs of sigma, long leg (r,f)).
//
// Usage: ./famstates x y R [mode]
//   prints one line per family: label s1 s2 f : V(r) for r=1..R
#include <bits/stdc++.h>
using namespace std;
enum { F = 0, IN = 1, OUT = 2 };
enum { SN = 0, SI = 1, SO = 2, SF = 3 };

// run values, Theorem 4.3
static inline long rho(long k, int near, int far) {  // near in {F,IN,OUT}, far in {F,IN,OUT}
    if (k == 0) return 0;
    if (near == F && far == F) return k & 1;           // A_k
    if (near == F || far == F) return k;               // B_k
    if (near == far) return k & 1;                     // C_k
    return (k >= 2 && k % 2 == 0) ? 1 : 0;             // D_k
}
static inline int step(int s, int arc) {  // status of centre after an arc IN/OUT at it
    if (s == SN) return arc == IN ? SI : SO;
    if (s == SI) return arc == IN ? SI : SF;
    if (s == SO) return arc == OUT ? SO : SF;
    return SF;
}
int X, Y, R;
int C0, C1, C2;
static inline int code(int h, int f) { return (h - 1) * 3 + f + 1; }
static inline int hof(int c) { return (c - 1) / 3 + 1; }
static inline int fof(int c) { return (c - 1) % 3; }
vector<long> M;  // memo, -1 unknown

long Gamma(int s, const int c[3]);

long Gamma(int s, const int c[3]) {
    int d = (c[0] > 0) + (c[1] > 0) + (c[2] > 0);
    if (d == 0) return 0;                                        // (N3)
    if (s == SF) {                                               // (N1)
        long v = 0;
        for (int t = 0; t < 3; t++) if (c[t]) v ^= rho(hof(c[t]), F, fof(c[t]));
        return v;
    }
    if ((s == SI || s == SO) && d == 1) {                        // (N2)
        for (int t = 0; t < 3; t++) if (c[t]) return rho(hof(c[t]), s == SI ? OUT : IN, fof(c[t]));
    }
    size_t idx = (((size_t)s * C0 + c[0]) * C1 + c[1]) * C2 + c[2];
    if (M[idx] >= 0) return M[idx];
    vector<long> opts;
    for (int t = 0; t < 3; t++) {
        if (!c[t]) continue;
        int h = hof(c[t]), phi = fof(c[t]);
        for (int j = 1; j <= h; j++) for (int dl = IN; dl <= OUT; dl++) {
            if (j == h && phi != F && dl != phi) continue;
            long det = rho(h - j, dl, phi);
            int nc[3] = {c[0], c[1], c[2]};
            long att;
            if (j >= 2) { nc[t] = code(j - 1, dl); att = Gamma(s, nc); }
            else { nc[t] = 0; att = Gamma(step(s, dl), nc); }
            opts.push_back(det ^ att);
        }
    }
    sort(opts.begin(), opts.end());
    long g = 0;
    for (long v : opts) { if (v == g) g++; else if (v > g) break; }
    M[idx] = g;
    return g;
}

int main(int argc, char** argv) {
    X = atoi(argv[1]); Y = atoi(argv[2]); R = atoi(argv[3]);
    C0 = 3 * X + 1; C1 = 3 * Y + 1; C2 = 3 * R + 1;
    M.assign((size_t)4 * C0 * C1 * C2, -1);
    // list sigmas: label N with both short attached; label I/O with exactly one attached
    auto states = [](int L) { vector<int> v; v.push_back(code(L, F)); for (int h = 1; h < L; h++) { v.push_back(code(h, IN)); v.push_back(code(h, OUT)); } return v; };
    vector<array<int, 3>> sig;
    for (int a : states(X)) for (int b : states(Y)) sig.push_back({SN, a, b});
    for (int lab = SI; lab <= SO; lab++) {
        for (int a : states(X)) sig.push_back({lab, a, 0});
        for (int b : states(Y)) sig.push_back({lab, 0, b});
    }
    // fill in increasing r so that recursion depth stays small
    for (int r = 1; r <= R; r++)
        for (int f = 0; f < 3; f++)
            for (auto& s : sig) { int c[3] = {s[1], s[2], code(r, f)}; Gamma(s[0], c); }
    const char* LB = "NIOF"; const char* FS = "FTA";
    auto legstr = [&](int c) { if (!c) return string("-"); return to_string(hof(c)) + FS[fof(c)]; };
    for (auto& s : sig) for (int f = 0; f < 3; f++) {
        printf("%c %s %s %c :", LB[s[0]], legstr(s[1]).c_str(), legstr(s[2]).c_str(), FS[f]);
        for (int r = 1; r <= R; r++) { int c[3] = {s[1], s[2], code(r, f)}; printf(" %ld", Gamma(s[0], c)); }
        printf("\n");
    }
}
