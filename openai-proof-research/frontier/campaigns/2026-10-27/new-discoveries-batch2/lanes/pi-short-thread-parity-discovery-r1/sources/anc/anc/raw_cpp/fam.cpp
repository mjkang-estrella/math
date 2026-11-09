// Fast positional 3-leg spider solver for families S(x,y,z), z=1..Z.
// Same game logic as spider.cpp (own derivation), but legs are kept in fixed
// positions (code 0 = detached) and memoised in a dense array.
#include <bits/stdc++.h>
using namespace std;
enum { FREE = 0, IN = 1, OUT = 2 };
enum { SN = 0, SI = 1, SO = 2, SF = 3 };
vector<array<array<int,3>,3>> RUN;
void build_runs(int maxk) {
    RUN.assign(maxk + 1, {});
    for (int k = 0; k <= maxk; k++) for (int a = 0; a < 3; a++) for (int b = 0; b < 3; b++) {
        if (k == 0) { RUN[k][a][b] = 0; continue; }
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
static inline int sstep(int s, int arc) {
    if (s == SN) return arc == IN ? SI : SO;
    if (s == SI) return arc == IN ? SI : SF;
    if (s == SO) return arc == OUT ? SO : SF;
    return SF;
}
static inline int code(int h, int f) { return (h - 1) * 3 + f + 1; }
static inline int hof(int c) { return (c - 1) / 3 + 1; }
static inline int fof(int c) { return (c - 1) % 3; }
int C0, C1, C2;
vector<int16_t> M;  // value+1
int G(int s, int c[3]) {
    int d = (c[0] > 0) + (c[1] > 0) + (c[2] > 0);
    if (d == 0) return 0;
    size_t idx = (((size_t)s * C0 + c[0]) * C1 + c[1]) * C2 + c[2];
    if (M[idx]) return M[idx] - 1;
    vector<char> seen(2048, 0);
    for (int t = 0; t < 3; t++) {
        if (!c[t]) continue;
        int h = hof(c[t]), far = fof(c[t]);
        for (int j = 1; j <= h; j++) for (int dl = IN; dl <= OUT; dl++) {
            if (j == h && far != FREE && dl != far) continue;
            if (j == 1 && d == 1) {
                if (dl == OUT && s != SI) continue;
                if (dl == IN && s != SO) continue;
            }
            int det = RUN[h - j][dl][far];
            int att;
            int nc[3] = {c[0], c[1], c[2]};
            if (j >= 2) { nc[t] = code(j - 1, dl); att = G(s, nc); }
            else {
                nc[t] = 0;
                int s2 = sstep(s, dl);
                if (s2 == SF) { att = 0; for (int u = 0; u < 3; u++) if (nc[u]) att ^= RUN[hof(nc[u])][FREE][fof(nc[u])]; }
                else att = G(s2, nc);
            }
            int v = det ^ att;
            if (v >= (int)seen.size()) seen.resize(v + 1, 0);
            seen[v] = 1;
        }
    }
    int r = 0; while (r < (int)seen.size() && seen[r]) r++;
    M[idx] = r + 1;
    return r;
}
int main(int argc, char** argv) {
    int x = atoi(argv[1]), y = atoi(argv[2]), Z = atoi(argv[3]);
    build_runs(max({x, y, Z}) + 2);
    C0 = 3 * x + 1; C1 = 3 * y + 1; C2 = 3 * Z + 1;
    M.assign((size_t)3 * C0 * C1 * C2, 0);
    for (int z = 1; z <= Z; z++) {
        int c[3] = {code(x, FREE), code(y, FREE), code(z, FREE)};
        printf("%d%c", G(SN, c), z == Z ? '\n' : ' ');
    }
}
