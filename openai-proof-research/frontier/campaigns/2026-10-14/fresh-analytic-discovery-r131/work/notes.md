# r131 durable research notes (author: Myeongjin Kang; runner Factory Droid / claude-opus-5-5 / high)

## 2026-10-20 orientation
- Read AGENTS.md, common brief 2026-10-20, r131 brief, r130 REPORT + public report/screens/reading-limits,
  r130 parent intake.json + primary-check.json, NEW-TEN acceptance section (lines 1-~40).
- r130 lane (072 Brennan) and 213 avoided per brief. Erdős similarity 084 heavily developed (I36 TECHNICAL, I37 parked,
  Jiang–Xi lower-ratio) -> avoided.
- Selected family 088, Brannen's reverse projection inequality P_n(K)=|ΠK|/|K|^{n-1} <= c_n=(n+1)n^n/n!.
  Status: true n=2 (Rogers–Shephard), n=3 (Chen–Feng–Li–Xi–Xu Thm 1.2; equality Feng–Hu–Liu–Xu Thm 1.2),
  false n>=9 (Feng–Hu–Liu–Xu Thm 1.3, at most n+2 facets), source P (product T10xT10, n=20; exponential excess).
  OPEN: 4<=n<=8 (FHLX intro, explicitly "still unresolved").
- Project history: I43 §1.3 "RP4" parked: tested only simplex-product partitions for n=4..8 (none beats simplex);
  r112 cites I43 and excludes product blocks. No project record of a general-polytope search found so far.
- FHLX mechanism (read §4 in full from I43's retained text literature/reverseprojection.txt): Minkowski-existence polytope
  with area vectors -P_F e_i, F={1,a}^perp, lower bound P_n(Q) >= n^n V(S) V(P_F C_m) via Minkowski's first inequality;
  first variation from the degenerate a0=(-1,0,...,0,1) (which is the simplex, equality) with equally spaced split b;
  sign of 9∫(L^2-|L|) flips exactly at n=9 (E|h| vs E h^2 on [-1/2,1/2]^{n-1}).

## Direction
Search for exact rational counterexample polytopes in n in {4..8}. If found: exact certificate = full proof.
