# r133 durable notes (Factory Droid / claude-opus-5-5 / high)
Start: 2026-10-20T16:47:42Z (UTC)

## 16:47-16:52Z reads (all before any computation or derivation)
- AGENTS.md, research-brief-2026-10-20.txt, fresh-analytic-r133-brief.txt read in full; hashes in input-hashes-start.txt
  (also hashes of every r132 + r132-parent file, 33 files, read-only).
- r132: REPORT.md, packet/public/report.md, reading-limits.md, work/notes.md in full; parent intake.json and
  primary-metadata-check.json in full.
- FHLX (arXiv 2610.13953v1) via I43-retained text frontier/sources/i43_convex_isoperimetric_discovery/literature/
  reverseprojection.txt: read lines 1-1092 IN FULL (intro, Thm 1.1-1.3, sect 2, sect 3 incl. Props 3.1-3.4, sect 4
  Props 4.1, 4.2, Lemmas 4.3, 4.4, Props 4.5, 4.6, lifting (4.19), references).
- Source P (pinned preprint "A product counterexample ...", 2026-09-24): README.md, build/main.tex, build/references.tex
  fetched from pinned raw URLs into packet/private/upstream, git-blob SHA-1 authenticated vs preprints-tree.json
  (all True). main.tex read IN FULL (lem:facets, prop:product R(AxB)=R(A)R(B), prop:simplex, thm:counterexample
  T10xT10, cor:exponential-excess).
- CONTENTS.md entry 088 (lines 2161-2179) read.

## Validation of r132 R1-R4 / (star) (author re-derivation, independent of r132 code)
- Exponential representation: s=E/S, S~Gamma(m) indep => M(0|a)=(m-1) f_Y(0), Y=sum a_i E_i. Checked.
- Asymmetric Laplace: U=(1-c)X-(1+c)Z has density (1/2)exp(-u^+/(1-c)-u^-/(1+c)). Checked (convolution).
  Hence f_Y(0)=(1/2)E exp(-W^+/(1+c)-W^-/(1-c)); (star) equals Phi<=1 at t=0. Checked.
- Box removal: if b leaves the box, true D(a) >= 2(n+1)+D(b), so LHS(star) <= Phi_true; equivalence holds. Checked.
- Simplex value: (s_1,s_m) density (m-1)(m-2)(1-x-y)^{m-3} gives M(0)=(m-1)/2, Phi=1. Checked.

## 16:52-17:05Z history search (before any new derivation was frozen; nothing frozen yet)
- rg -uu (hidden+ignored, no size cutoff) over the whole project for Brannen/reverse projection/2610.13953/FHLX/
  simplex maximum/n+2 facets; excluded: active roots fresh-arithmetic-discovery-r98, discovery-arithmetic-r98-parent,
  fresh-structural-discovery-r134, own root, .git, site-packages, frozen/corpus/pinned/snapshots/inputs copies
  (copied corpora and catalogue copies). 155 files; operative hits: iterations/i43 sect 1.3 (lines 60-80 read: RP4
  parked after simplex-product test), r112 research-report (088 paragraph read: product optimisation not fresh),
  r131 notes (selected 088, numeric search), r132 (read in full). Remaining hits are CONTENTS copies/ledgers.
  First broad search including "B-spline|divided difference|Dirichlet mean|Markov-Krein|projection body" returned
  1692 files, dominated by unrelated uses and copies; not followed beyond the narrowed search (disclosed limit).

## New author observations (17:05Z)
O1 (pi-representation). For sorted knots and t=0: pi_i := P(Y - a_i E_i > 0) = P(Y>0) - a_i f_Y(0) (memoryless
   exponential), hence D(a) f_Y(0) = sum_{i<j}(pi_i - pi_j) and Phi = (1/(n+1)) sum_i (n+3-2i) pi_i. Reformulation only.
O2 (pyramid decomposition). With r positive, s negative, z zero knots: Phi = [(r+s-1)Phi_0 + z Lambda]/(r+s-1+z),
   Lambda = (sum|a_i|) f_Y(0). Generalises FHLX lifting (4.19); routine.
O3 (r=1 lemma). If exactly one knot lies strictly above t (or below), Phi <= 1, strict unless s=1. (needs write-up)
O4 (zonoid form of G2). N_c(b)=E psi_c(W) is the support function of the zonoid Z_c={E[theta(E)E]: theta in
   [-1/(1-c),1/(1+c)]}; D(b) is the support function of the permutohedral zonotope; so G2 <=> one vertex
   v*=(2j-n-1)_j lies in 2(n+1)Z_c for all c.
O5 (KEY CANDIDATE MECHANISM). W=U-V has log-concave density (convolution of log-concave), so W|W>0 and -W|W<0 are
   IFR => NBUE => HNBUE => each is <=_cx the exponential with the same mean. e^{-x/alpha} convex => 
   E e^{-psi_c(W)} <= p/(1+A/alpha) + (1-p)/(1+B/beta), p=P(W>0), A=E[W|W>0], B=E[-W|W<0].
   Then (star) for all scales lambda b holds iff (quadratic in lambda) d <= arithmetic mean (G2) AND d <= harmonic
   mean H_c = [p^2 alpha/P + (1-p)^2 beta/N]^{-1}, d=D(b)/(2(n+1)). Worst c at endpoints gives the scale-free
   SUFFICIENT condition (S): D(b) P(W>0)^2 <= (n+1) E[W^+] for all b in R^n (and its mirror, equivalent by b->-b).
   (S) coincides with G2 for symmetric b. To test numerically next.

## 17:12Z exploration of (S) (scratch, float, ulimit -v 1GB, one process)
- sup_b D(b)P(W>0)^2/((n+1)E W^+): n=2..9: .333 .666 .897 1.060 1.181 1.272 1.346 1.405 (random local search).
  Maximiser is the degenerate corner b=(-1,eps^{n-1}); corner value 2(n-1)^2/(n(n+1)) (author asymptotic:
  p~eps(n-1), E W^+~eps^2 n(n-1)/2). <1 iff n<=4. So (S) can at best give n<=4.
- The corner corresponds to c->1, scale->infinity, i.e. actual knots ~(-1,0^-,eps^{n-1},0^+) where the outer-pair
  HNBUE replacement is lossy (true Phi there is <1, s=1-like regime).

## 17:25Z HNBUE bound with the TRUE outer pair (box respected) - exploration (scratch/hnbue.py)
- Outer-pair HNBUE bound >= Phi checked on random configs; control n=9 FHLX: bound 1.00094 > 1 (true 1.00049).
- Random search sup of outer-pair bound over configs, n=4..8: .998 .998 .999 .998 .998 (only near simplex curve).
- Ray structure: along b -> lambda b (fixed c), bound-1 = lambda*(lin + lambda*quad)/(...) with
  lin = d - P/alpha - N/beta (G2 at c), quad = d(pN/((1-p)beta)+(1-p)P/(p alpha)) - PN/(p(1-p)alpha beta).
  So bound<=1 on the box <=> G2 and the value at lambda_max (box face). Faces: sup ->1 only at simplex-curve ends
  c->+-1; but n=8 face-left non-degenerate point .9758 (small margin). n=5..8 would need certified 7-9 dim compute.
- (S) unconstrained suffices (worst c, every scale) and holds numerically for n<=4 only (sup .897 at n=4).
DECISION DIRECTION (prefreeze): target full theorem in dimension 4 for polytopes with at most 6 facets via exact
reduction + HNBUE convex-order bound + (S)_4. Need rigorous proof of (S)_4 by sign patterns.
- Lemma (overshoot): ordering positive coefficients increasingly, E[W|W>0] = sum_i P(I=i|W>0) sum_{j>=i}u_j >= u_max.

## 17:15-17:25Z exact certificates for (S)_4 (scratch/cert.py, exact Fractions, ulimit -v 1-2GB, one process)
- Ordered variables x_i, y_j >= 0 (u_i = x_i+..+x_k, v_j = y_j+..+y_l), p = Np/Den, E W^+ = NP/Den,
  Den = prod(u_i+v_j); T = (n+1) NP Den - D Np^2. For n=4 ALL 10 sign patterns (k,l,z), k>=1, have T with
  nonnegative coefficients (min coefficient 2; (2,2,0): 118 terms; (3,1,0): 84 terms). Independent numeric check
  of Np/Den, NP/Den, D vs s4.py formulas: ok. => (S)_4 holds for all b in R^4 (author, exact).
- Sanity n=5: only pattern (4,1,0) has negative coefficients (4 terms, min -6), consistent with the corner failure.
- Corrected chain (author): with alpha=1+c, beta=1-c, A=P/p, B=N/(1-p), HNBUE gives Psi <= (1+d)[p alpha/(alpha+A)
  + (1-p) beta/(beta+B)]; <=1 iff (after clearing) [d - P/alpha - N/beta] + [d(pB/beta+(1-p)A/alpha) - AB/(alpha beta)]
  <= 0. (S)(b) and (S)(-b) give 2dp^2<=P, 2d(1-p)^2<=N => second bracket <=0 (alpha+beta=2) and first bracket <=0
  (Cauchy-Schwarz: P/alpha+N/beta >= (sqrt P+sqrt N)^2/2 >= d). p in {0,1}: direct. b=0: Psi=1.
- b=0 forces a vector of the Gale space supported on the two outer indices with opposite signs => two facets with
  the same outer normal: impossible for a genuine 6-facet polytope. Hence strict inequality for 6 facets.
- /tmp/r133-hits*.txt (history-search temp lists, outside root - violation of write-only-root rule) removed 17:20Z.
- For n>=5 the separation of the two brackets is lossy (corner has huge N/beta slack); the true obligation is
  G2 (bracket 1) + box-face condition. Not pursued: needs certified 6-9 dim near-equality analysis.

## 17:21:32Z FREEZE: packet/public/FROZEN-THEOREM.md (4-polytopes with <=6 facets, |PiK|<=(160/3)|K|^3, equality iff simplex). sha256 in work/frozen-hash.txt; file made read-only. Literature check 17:18-17:21Z recorded in the frozen file.

## 17:22-17:35Z post-freeze: packet/public/certificate.py (exact, all 10 patterns PASS, strict monomial in x_k,y_l
present for every pattern, partial-fraction identity checks, negative control n=5 (4,1,0) rejected, MC sanity);
packet/public/geometry_control.py (float): direct vertex/face-recursion computation of P_4 for 40 random 6-facet
4-polytopes equals reduction formula at t* to 1e-10, grid max over t <= value at t*, Minkowski check, max P/c4
.999891 < 1; random simplex gives 160/3. Literature (late, before freeze 17:18-17:21Z): FHLX abstract page (v1 only),
Saroglou 1409.4347v2 intro/refs (prior results: 3-dim zonoids/cones/double cones), Brauner-Ortega-Moreno-Schuster
2610.18268 (irrelevant), web searches found no n+2-facet or dimension-4 result. Saroglou 2011 PDF: TLS failure.
Next: proof.md (full), report, reading-limits, verify, controls, seal.

## 17:36-17:45Z proof and packaging
- packet/public/proof.md written (full author proof at frozen scope): Lemma 1 (exact variational, Minkowski
  equality), Lemma 2 (Gale/Jacobi), Lemma 3 (coarea + Gamma-Dirichlet, continuity of density versions), Prop A,
  Lemma 4 normal form, Lemma 4' (b != 0 for genuine 6-facet), Lemma 5 (log-concavity), Lemma 6 (HNBUE Laplace bound,
  self-contained), Prop B (reduction to (S) for b,-b with strictness), Lemma 7 (partial fractions), Prop C ((S)_4
  certificate), proof of Theorem, scope/limits.
- Late reads after freeze: Petty companion (README, main.tex, intro, consequences; blobs authenticated) - lower
  bound only, no overlap; NEW-TEN lines 1-60 (acceptance rules); upstream.json. r132 FINAL/CONTROL-RESULTS/verify.py
  viewed as format reference.
- Inputs recheck 17:40Z: all 36 hashes in input-hashes-start.txt unchanged.
- Final status: full author-proof nominee at frozen scope; no self-gates/count.
