/* Independent exhaustive check of the literal definition of R_cyc(S_a^sc, P_b^mon) for n <= 7.
   usage: brute a b n   -> prints "GOOD k" (number of colourings avoiding both) ; GOOD 0 means property holds at n.
   Colouring: bit e = 1 means colour 2 (Lean code 1). Embedding phi(i) = s[(i - t) mod k] for a sorted k-subset s
   and rotation t, i.e. j -> phi(t+j) strictly increasing (literal arXiv:2604.16188 Sec. 1 / Lean IsCyclicEmbedding). */
/* no libc headers available: prototypes declared manually */
int printf(const char*,...); int atoi(const char*);
static int n, eid[16][16];
static unsigned long long masks[2][200000]; static int nm[2];
static void gen(int which, int k, int nedge, int (*ed)[2]) {
  int s[16];
  for (int i = 0; i < k; i++) s[i] = i;
  for (;;) {
    for (int t = 0; t < k; t++) {
      int phi[16];
      for (int i = 0; i < k; i++) phi[i] = s[((i - t) % k + k) % k];
      unsigned long long m = 0;
      for (int e = 0; e < nedge; e++) m |= 1ULL << eid[phi[ed[e][0]]][phi[ed[e][1]]];
      masks[which][nm[which]++] = m;
    }
    int i = k - 1;
    while (i >= 0 && s[i] == n - k + i) i--;
    if (i < 0) break;
    s[i]++;
    for (int j = i + 1; j < k; j++) s[j] = s[j - 1] + 1;
  }
}
int main(int argc, char **argv) {
  int a = atoi(argv[1]), b = atoi(argv[2]); n = atoi(argv[3]);
  int E = 0;
  for (int u = 0; u < n; u++) for (int v = u + 1; v < n; v++) { eid[u][v] = eid[v][u] = E++; }
  int st[16][2], pa[16][2];
  for (int i = 1; i < a; i++) { st[i - 1][0] = 0; st[i - 1][1] = i; }
  for (int i = 0; i + 1 < b; i++) { pa[i][0] = i; pa[i][1] = i + 1; }
  if (a <= n) gen(0, a, a - 1, st);
  if (b <= n) gen(1, b, b - 1, pa);
  long long good = 0; unsigned long long ex = 0; int have = 0;
  for (unsigned long long c = 0; c < (1ULL << E); c++) {
    int bad = 0;
    for (int i = 0; i < nm[0] && !bad; i++) if ((c & masks[0][i]) == 0) bad = 1;
    for (int i = 0; i < nm[1] && !bad; i++) if ((c & masks[1][i]) == masks[1][i]) bad = 1;
    if (!bad) { good++; if (!have) { ex = c; have = 1; } }
  }
  printf("a=%d b=%d n=%d edges=%d tuples1=%d tuples2=%d GOOD %lld", a, b, n, E, nm[0], nm[1], good);
  if (have) printf(" example=%llx", ex);
  printf("\n");
  return 0;
}
