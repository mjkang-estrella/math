# r132 durable notes (Factory Droid / claude-opus-5-5 / high)
Start: 2026-10-20T09:17:52-07:00
- Read in full: AGENTS.md (1298 B), research-brief-2026-10-20.txt (5570 B), fresh-analytic-r132-brief.txt (4501 B). Hashes in input-hashes-start.txt.

## 2026-10-20T09:20:24-07:00 reads
- r130: REPORT.md, packet/public/{report,screens,reading-limits}.md in full; parent intake.json, primary-check.json in full.
- r131 (read-only, nothing run/copied): parent intake.json, partial-inventory.json; work/notes.md, acquisition-log.jsonl;
  scratch/opt.py, rnum.py read in full; opt4.json: first ~3000 bytes + top-level structure (36 records, all n=4).
  Observation: the top n=4 records have ratio 1.0000000000000044 etc. = float noise around the simplex. No counterexample.
- I43 iteration md: section 1.3 (lines 66-80) and handoff (line 330); FHLX full text retained by I43
  (frontier/sources/i43_convex_isoperimetric_discovery/literature/reverseprojection.txt): lines 1-400 and 560-1092 read
  (intro, Thm1.1-1.3, sect.2, Prop3.1, sect.4 in full incl. Prop4.1, 4.2, Lemma4.3, 4.4, Prop4.5, 4.6, lifting, refs).
  Lines 401-559 (Prop 3.2-3.3 dim-3 equality) not read: not operative for sect.4.
- r112 public research-report (in full), catalog-088.txt, history-088.json head; parent intake line 35.

## Key observation O1 (author, to be proved carefully)
FHLX Prop 4.1 is a lower bound via Minkowski's first inequality at a FIXED lambda. Maximizing over lambda makes it EXACT:
for any polytope Q with facet area vectors -q_i (q_i=P_F e_i), P_n(Q) = n^n V_F(P_F C_m) * max_lambda V_F(S_lambda),
attained at lambda proportional to Q's support numbers (Minkowski equality = homothety).
For m=n+2, F=F_a={1,a}^perp, S_lambda depends only on t=<a,lambda>, and f_a is the density of <a,s>, s uniform on the
simplex Delta^{m-1}, i.e. the Curry-Schoenberg B-spline M(t|a_1..a_m). Every n-polytope with n+2 facets is GL-equivalent
to some Q_a (Gale/row-space argument). Hence, writing m=n+2:
   sup{P_n(Q)/c_n : Q n-polytope with <= n+2 facets} = sup_a D(a) ||M(.|a)||_inf / (n+1)^2.
FHLX used only t=0 and symmetric equally spaced perturbations of a0=(-1,0^{m-2},1) [simplex].
Plan: bounded exact/numeric exploration of Phi_m(a)=D(a)max_t M(t|a)/(m-1)^2 for m=6..10 (n=4..8).
If Phi>1 anywhere for some n<=8: rational knots + exact rational certificate => counterexample in that dimension.

## 2026-10-20T09:25:25-07:00 bounded exploration 1 (scratch/explore.py, pure python, ulimit -v 1GB, 1 process; output explore-run1.txt)
- Controls: Phi=1 on a0=(-1,0^{m-2},1) for m=4..12; FHLX m=11 eps=.01 gives 1.000489 (>1); m=9 analogue 0.99518.
- Random local search, 6 seeds each, m=4..11: m<=10 all runs collapse to (0,c^{m-2},1) with Phi=1-O(1e-6);
  m=11 reaches 1.00068 (non-equally spaced interior knots). Float only; no claim.
## Derivations (author)
- Exponential representation: s=E/S, S~Gamma(m) indep of s => M(0|a) = (m-1) f_Y(0), Y=sum a_i E_i.
  Zero knots drop out of Y. With P={a_i>0}, N={a_i<0}: f_Y(0)=int_0^inf f_U f_V.
- Equality curve a=(-1,c^k,1), k=m-2, t=c: D=2(k+1), M(c)=(k+1)/2, Phi=1 for all c in (-1,1).
- First variation from curve point c in direction b in R^k (middle knots c+eps b), t fixed at c:
  Phi = 1 + eps*G_c(b) + O(eps^2), G_c(b) = D(b)/(2(k+1)) - P/(1+c) - N/(1-c), P=E(sum b_j E_j)^+, N=E(...)^-.
  Optimizing c: G*(b) = D(b)/(2(k+1)) - (sqrt P + sqrt N)^2/2. FHLX = c=0, b equally spaced symmetric (P=N).
- Partial fractions: E Z^+ = sum_{b_j>0} b_j prod_{l!=j} b_j/(b_j-b_l) for distinct b.
Next: compute sup_b R_k(b)=D(b)/((k+1)(sqrtP+sqrtN)^2) for k=2..9.

## 2026-10-20T09:28:57-07:00 first-variation exploration (scratch/firstvar.py, output firstvar-run1.txt)
- FHLX k=9 b=(-4..4), c=0: G=0.0992>0 (R=1.0168), consistent with FHLX Prop 4.5.
- sup_b R_k (optimized b and c, float): k=2..10: .333 .5 .619 .718 .804 .882 .953 1.0195 1.0817.
  => first-order threshold within the (n+2)-facet class off the WHOLE simplex curve is exactly n=9; n<=8 negative.
## General-m exact reduction (author, to verify)
For an n-polytope with m facets, r=m-1-n: there is A in R^{m x r} with
  P_n(Q)/c_n = sup_t Psi(A - 1 t^T),  Psi(A) = (1/(n+1)) sum_{|J|=r+1} |det[1 A]_J| * f_{A^T E}(0), E iid Exp(1) in R^m.
(cube projection via complementary minors; section via coarea; f_X(t)=(m-1)!/(m-1-r)! f_Y(0) by S~Gamma(m) indep.)
Simplex check r=0: Psi=1. Pair-merge simplex points with r pairs: first variation separable with denominator (k+r)=n+1
but only k=n+1-r perturbable rows => r=1 best among pair merges.
Single (r+1)-group merge (T=conv(a_G) simplex containing 0, n=k zero rows): first variation
  G(B) = sum_{j<j'} psi(b_j-b_j')/((n+1)Delta0) - E phi_T(-sum_j b_j E_j),
  psi(v)=sum_{i<i'} |det(v, a_l: l!=i,i')|, phi_T gauge of T, Delta0=|det[1 a_G]|, g_Y0(y)=e^{-phi(y)}/Delta0.
Next: Monte Carlo (CRN) screen of r=2 triangle groups for n=7,8 (exploration only).

## 2026-10-20T09:39:01-07:00 further runs and reads
- fv_r2.py (MC, CRN): triangle-group (r=2) first variation n=4: .62 (= r=1 value); n=8 best fresh .956; n=9 best .990 (<1.0195 of r=1).
  So no first-order improvement over pair merges seen. Outputs fv_r2-n8.txt, fv_r2-n9.txt.
- psi2.py: exact iterated-residue 2D density; validated (simplex groups ->1; residue vs brute quadrature agree 1e-8;
  3-cube max_t Psi = 0.44444 vs 8/18). Random-start search m=11 (n=8): best .9607; control m=12 (n=9): .9786.
  Search is weak (does not even find FHLX n=9 violator) -> uninformative, not escalated.
- Global reformulation (star), verified vs B-spline by MC (4 random configs, agreement to ~3 digits):
  (n+2)-facet Brannen in dim n=k <=> for all c in (-1,1), b in R^k:
     (1 + D(b)/(2(k+1))) * E exp(-W^+/(1+c) - W^-/(1-c)) <= 1,  W = sum_j b_j E_j.
  (Exact: f_Y(0) = E g_c(-W)/..., D linear on the segment from the curve since middle knots stay inside.)
  Linearization at b->0 is the first-variation inequality D(b) <= (k+1)(sqrtP+sqrtN)^2.
- Primary check: arXiv:2610.13953 abs page (v1 only, 16 Aug 2026) = FHLX; abstract unchanged. Web searches (2 queries) found no
  resolution of 4<=n<=8 and no B-spline/exact-max formulation. Bounded; not priority clearance.
- Source P fetched at pin into packet/private/upstream (4 files, git-blob authenticated vs complete tree);
  main.tex lines 38-237 read (intro, thm:counterexample, lem:facets, prop:product). Simplex products are (n+2)-facet polytopes.

## Decision (PREFREEZE, no nominee)
No full-scope statement could be proved: the sharp (n+2)-facet theorem for n=4..8 needs (star) for k=4..8 globally, an
8-parameter sharp inequality with ~5% first-order margin at k=8; no analytic proof found, and computer-assisted
branch-and-bound would be disproportionate in this environment. Counterexample route for n<=8: first variation negative
off every pair- and triangle-merge simplex point (numerical). Nothing frozen.

## 2026-10-20T09:42:46-07:00 packaging
- History search done (see packet/private/registers/history-register.json): no project antecedent of R1-R4/(star) found.
- Public: packet/public/{report.md, reading-limits.md, verify.py, controls.py}; code + outputs in scratch/ (MIT).
- Private: packet/private/upstream (source P, authenticated), packet/private/registers/{upstream,primary,history}-register.json.
- Inputs re-checked unchanged before seal: AGENTS.md + both briefs (input-hashes-start.txt), all 9 r131 partial files.
- Seal: packet/MANIFEST.json, FINAL.json, REPORT.md; controls on disposable copies in control-tmp/ (removed after).
