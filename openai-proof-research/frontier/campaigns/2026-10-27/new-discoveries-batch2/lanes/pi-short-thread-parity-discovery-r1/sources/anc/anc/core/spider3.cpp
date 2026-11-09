// Fast solver for the Game of Arrows on 3-legged spiders.
// Coupled states: centre label N (three attached legs) or I (two attached legs);
// O is obtained from I by reversing all arrows (swap T <-> A).
// A leg is (r, f): r >= 1 unmarked edges between centre and first marked edge / trimmed leaf,
// f in {F=0, T=1, A=2} = far end free, or forced Toward / Away from the centre.
// Usage: ./spider3 M   -> prints G(S(x,y,z)) for trimmed legs 1<=x<=y<=z<=M
#include <bits/stdc++.h>
using namespace std;
int M;
static inline int runv(int k, int nearf, int farf) {
    if (k == 0) return 0;
    if (nearf == 0 && farf == 0) return k & 1;
    if (nearf == 0 || farf == 0) return k;
    if (nearf == farf) return k & 1;
    return (k >= 2 && k % 2 == 0) ? 1 : 0;
}
static inline int flipf(int f) { return f == 0 ? 0 : 3 - f; }
// encode leg as r*3+f, r in [1,M]
int L;  // number of leg codes = (M+1)*3
vector<int> memoN, memoI;
inline int legcode(int r, int f) { return r * 3 + f; }
int coupledI(int a, int b);
int coupledN(int a, int b, int c);
int coupledO(int a, int b) {
    int ra = a / 3, fa = a % 3, rb = b / 3, fb = b % 3;
    return coupledI(legcode(ra, flipf(fa)), legcode(rb, flipf(fb)));
}
int mexOf(vector<int>& v) {
    sort(v.begin(), v.end());
    int g = 0;
    for (int x : v) { if (x == g) g++; else if (x > g) break; }
    return g;
}
int coupledI(int a, int b) {
    if (a > b) swap(a, b);
    int key = a * L + b;
    if (memoI[key] >= 0) return memoI[key];
    vector<int> opts;
    int legs[2] = {a, b};
    for (int i = 0; i < 2; i++) {
        int r = legs[i] / 3, f = legs[i] % 3, other = legs[1 - i];
        int ro = other / 3, fo = other % 3;
        for (int j = 1; j <= r; j++) for (int d = 1; d <= 2; d++) {
            if (j == r && f != 0 && d != f) continue;
            int det = runv(r - j, d, f);
            int val;
            if (j >= 2) {
                val = coupledI(legcode(j - 1, d), other);
            } else {
                if (d == 1) {  // toward centre: centre stays I, one leg left -> must leave via 'away'
                    val = runv(ro, 2, fo);
                } else {       // away: centre becomes free
                    val = runv(ro, 0, fo);
                }
            }
            opts.push_back(det ^ val);
        }
    }
    int g = mexOf(opts);
    memoI[key] = g;
    return g;
}
int coupledN(int a, int b, int c) {
    // canonical: sort, and also compare with flipped version (choose min key) -- values equal
    int v[3] = {a, b, c};
    sort(v, v + 3);
    long long key = ((long long)v[0] * L + v[1]) * L + v[2];
    if (memoN[key] >= 0) return memoN[key];
    vector<int> opts;
    for (int i = 0; i < 3; i++) {
        int r = v[i] / 3, f = v[i] % 3;
        int o1 = v[(i + 1) % 3], o2 = v[(i + 2) % 3];
        for (int j = 1; j <= r; j++) for (int d = 1; d <= 2; d++) {
            if (j == r && f != 0 && d != f) continue;
            int det = runv(r - j, d, f);
            int val;
            if (j >= 2) val = coupledN(legcode(j - 1, d), o1, o2);
            else val = (d == 1) ? coupledI(o1, o2) : coupledO(o1, o2);
            opts.push_back(det ^ val);
        }
    }
    int g = mexOf(opts);
    memoN[key] = g;
    return g;
}
int main(int argc, char** argv) {
    M = atoi(argv[1]);
    L = (M + 1) * 3;
    memoN.assign((size_t)L * L * L, -1);
    memoI.assign((size_t)L * L, -1);
    for (int x = 1; x <= M; x++)
        for (int y = x; y <= M; y++)
            for (int z = y; z <= M; z++)
                printf("%d %d %d %d\n", x, y, z, coupledN(legcode(x, 0), legcode(y, 0), legcode(z, 0)));
    return 0;
}
