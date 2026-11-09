/* 366914: linear realizations of {1^a, x^b, y^c}, x = y-k (arXiv:2502.00164, Conjecture 1.11).
   A linear realization is a Hamiltonian path on vertices 0..v-1 (v = a+b+c+1) whose multiset of
   |u-w| edge lengths is exactly {1^a, x^b, y^c}.  Exhaustive DFS over start vertex and moves with a
   node cap; prints FOUND path, or NONE (exhaustive, no cap hit), or CAP (undecided).
   usage: linreal y k a b c cap */
#include <stdio.h>
#include <stdlib.h>
static int v, len[3], rem[3], used[200], path[200];
static long long nodes, cap;
static int capped;
static int dfs(int cur, int depth) {
    if (depth == v) return 1;
    if (++nodes > cap) { capped = 1; return 0; }
    for (int t = 0; t < 3; t++) {
        if (!rem[t]) continue;
        int L = len[t];
        for (int s = -1; s <= 1; s += 2) {
            int nx = cur + s * L;
            if (nx < 0 || nx >= v || used[nx]) continue;
            used[nx] = 1; rem[t]--; path[depth] = nx;
            if (dfs(nx, depth + 1)) return 1;
            used[nx] = 0; rem[t]++;
            if (capped) return 0;
        }
    }
    return 0;
}
static int solve(int y, int k, int a, int b, int c, int verbose);
int main(int argc, char **argv) {
    if (argc == 5) { /* sweep: linreal ymin ymax B cap */
        int y0 = atoi(argv[1]), y1 = atoi(argv[2]), B = atoi(argv[3]); cap = atoll(argv[4]);
        long long inst = 0, found = 0, none = 0, capc = 0;
        for (int y = y0; y <= y1; y++) for (int k = 3; 2 * k < y; k++) {
            int x = y - k, f;
            if (x % 2 == 0 && y % 2 == 0) continue; /* Theorem 1.4: a >= y-1 suffices */
            if (x == 3 || (x % 2 == 0 && y % 2 == 1)) f = x + y - 2; else f = x + y - 1;
            for (int a = y; a < f; a++) for (int b = 1; b <= B; b++) for (int c = 1; c <= B; c++) {
                int r = solve(y, k, a, b, c, 0); inst++;
                if (r == 1) found++; else if (r == 0) { none++; printf("NONE y=%d k=%d a=%d b=%d c=%d\n", y, k, a, b, c); }
                else { capc++; printf("CAP y=%d k=%d a=%d b=%d c=%d\n", y, k, a, b, c); }
                fflush(stdout);
            }
            printf("done y=%d k=%d instances_so_far=%lld\n", y, k, inst); fflush(stdout);
        }
        printf("SUMMARY instances=%lld found=%lld none=%lld cap=%lld\n", inst, found, none, capc);
        return 0;
    }
    int y = atoi(argv[1]), k = atoi(argv[2]), a = atoi(argv[3]), b = atoi(argv[4]), c = atoi(argv[5]);
    cap = atoll(argv[6]);
    int r = solve(y, k, a, b, c, 1); return r < 0;
}
static int solve(int y, int k, int a, int b, int c, int verbose) {
    nodes = 0;
    v = a + b + c + 1; len[0] = 1; len[1] = y - k; len[2] = y;
    /* by reflection u -> v-1-u it suffices to start in the lower half */
    for (int st = 0; st <= (v - 1) / 2; st++) {
        for (int i = 0; i < v; i++) used[i] = 0;
        rem[0] = a; rem[1] = b; rem[2] = c; used[st] = 1; path[0] = st; capped = 0;
        if (dfs(st, 1)) {
            if (verbose) { printf("FOUND y=%d k=%d a=%d b=%d c=%d v=%d path=", y, k, a, b, c, v);
            for (int i = 0; i < v; i++) printf("%d%c", path[i], i + 1 < v ? ',' : '\n'); }
            return 1;
        }
        if (capped) { if (verbose) printf("CAP y=%d k=%d a=%d b=%d c=%d v=%d start=%d\n", y, k, a, b, c, v, st); return -1; }
    }
    if (verbose) printf("NONE y=%d k=%d a=%d b=%d c=%d v=%d\n", y, k, a, b, c, v);
    return 0;
}
