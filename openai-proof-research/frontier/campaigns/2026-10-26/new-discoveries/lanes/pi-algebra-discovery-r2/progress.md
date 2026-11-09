# pi-algebra-discovery-r2 lane progress

Research sub-agent: Pi. Date 2026-10-26. Standard speed, no children, no external
posting, no git. Own lane only.

## Phase 0 — ledger/prior-work audit

Read AGENTS.md, ledger.json (16 accepted / 21 excluded), NEXT.md,
RESULTS.md, parent-next-screen SCREENING.md, pi-next-discovery progress.md.
Accepted matrix/inequality outcomes already covering: 372758 (connection–Dirac),
347947 (maximal index), 371345/371346 (Vendi–LCR), 351633, 355008/355009,
353909 (C*-Sendov). Excluded by actual prior: 322914/324064 (Audenaert Thm 1),
324172 (Li–Sze Cor 2.7), 329167 (Berndt–Sra Cor 3.4), 323049 (known 2020
counterexamples). Active other lanes: 332493 (four projections, projection-trace
lane) and combinatorial targets (discrete-r2 lane) — both avoided here.
matrixShapiro 352327: two prior numerical searches negative; not duplicated.

## Phase 1 — parent lead: Krishna 2206.09197 C*-algebraic Casas–Alvero (MathDB 355066)

Actual source read in full (arXiv:2206.09197v2, 3 pages, SHA of PDF recorded in
sources/). Conjecture 2.1 hypothesis: **A is a commutative C*-algebra**, P(z) =
(z−a1)…(z−an), ai ∈ A; conclusion P = (z−a)^n. Degree-2 proved in-source via
Gelfand–Naimark (uses: (b−a)^2 = 0 ⟹ a = b in C(X)).

Parent's M2(C) sketch (square-zero R, P(z)=(z−R)z², D1=3z²−2Rz, D2=6z−2R,
shared zeros 0 and R/3) is **definitively ruled out**:

1. **Hypothesis violation.** The conjecture quantifies over commutative
   C*-algebras only; M2(C) is noncommutative. The sketch is outside scope, not a
   source-faithful counterexample.
2. **No nilpotents in scope.** A commutative C*-algebra ≅ C(X) is reduced; the
   exact mechanism of the sketch (R² = 0 ≠ 0) cannot occur. The source's own
   degree-2 proof is precisely the observation that squares are zero only for
   zero elements.
3. **Equivalence to the classical open conjecture.** For A = C(X), evaluation is
   pointwise: P(z)(x) = Π(z(x) − ai(x)) and P^(j)(z)(x) is the j-th scalar
   derivative pointwise. Hence the C*-hypothesis holds iff for every x the
   scalar polynomial p_x = Π(t − ai(x)) satisfies the classical Casas–Alvero
   hypothesis. Classical CA (any degree ≥ 3 over any char-0 field) would give
   p_x = (t − λ(x))^n pointwise, hence a1 = … = an = λ ∈ C(X) and P = (z−λ)^n;
   conversely A = ℂ is a commutative C*-algebra, so the C*-conjecture implies
   classical CA. The C*-conjecture is therefore *equivalent* to the classical
   Casas–Alvero conjecture (degree by degree) — no source-faithful nontrivial
   outcome is reachable without resolving classical CA itself.
4. **Prior-art status of classical CA.** Still open: Ghosh arXiv:2501.09272
   (v1 Jan 2025, v2) is an unrefereed preprint claiming a Koszul-homology
   proof; MathDB itself carries 382345/361137/359117/365893 (incl. "Ghosh's
   regular-sequence conjecture") as open, and no journal version is visible.
5. The dual-numbers counterexample P(z) = (z−ε)z² over ℂ[ε]/ε² (same shape:
   P,P′ share 0; P,P″ share ε/3) is the standard known nilpotent obstruction —
   uncountable under strict novelty even in a noncommutative reading.

Verdict: **lead excluded; no claim.** Recorded here only; no shared edits.

## Phase 2 — target selection: MathDB 346741 (norm-sum Recht–Ré)

Screened the live open matrix-inequalities tag (46 posts re-fetched live
2026-10-26). 375999 (Lin multivariable Young) resolved in-source by Pang
2607.11866; 369147 (Lee/Frobenius) solved per its own MathDB statement. Chosen
target: **346741** — Recht–Ré Conjecture 2 (sum-of-norms / termwise variant):

    (1/n^m) Σ_{all ordered tuples} ‖A_{j1}···A_{jm}‖ ≥ ((n−m)!/n!) Σ_{distinct} ‖…‖

- Status verified against primary sources: Lai–Lim arXiv:2006.01510 states it
  as **Conjecture 2** and leaves it open ("not clear to us if the noncommutative
  Positivstellensatz might perhaps also shed light on this related conjecture");
  known for m = 2, 3 for every unitarily invariant norm (Israel–Krahmer–Ward,
  arXiv:1411.0333 / Lin. Alg. Appl. 2016). Open for m ≥ 4.
- Fresh October 2026 work checked and *does not touch it*: arXiv:2610.00155
  (two-factor Loewner sharpness, m=2 only) and the Zenodo "Exact Low-Length
  Recht–Ré Inequalities" candidate manuscript (Loewner sums E_{m,n} only; its
  p.2 explicitly says the termwise-norm variant "is distinct from the norm of
  the averaged product"). Neither proves, bounds, nor disproves Conjecture 2.
- No normalization appears in the statement; the inequality is homogeneous
  degree 1 in each A_i.
- Exact-witness path: rank-one PSD matrices A_i = v_i v_i^T reduce the spectral
  norm of every product to Π_k |⟨v_{jk}, v_{jk+1}⟩| — with rational-coordinate
  vectors this is a finite inequality between rationals (Lean-tractable with no
  transcendental functions).

Two approaches planned: (A) rank-1 combinatorial reduction + exact/narrowed
search for a counterexample; (B) direct small-PSD search / analytical attack on
m = 4. See progress notes below.

## Phase 3 — Casas-Alvero equivalence note (superseded sketch)

Covered in Phase 1.

## Phase 4 — deep work on 346741 (Recht–Ré Conjecture 2)

### 4.1 Two deep approaches tried (per task requirement)

**Approach A — counterexample search (exhaustive within classes).**
(a) Rank-1 PSD: product norms factor as products of inner products; 2215
random configs over d ∈ {1..16}, n ∈ {4,5,6,8}, m ∈ {4,5,6}: zero violations
(verify_rank1.py). (b) General PSD Wishart tuples: clean. (c) Hill-climbing
over 2×2 PSD with per-matrix log-scales (opt_rr2v2.py, 40 restarts): every run
converges to Φ = 0, the all-equal basin; an earlier "hit" of −1e41 was diagnosed
as exp-overflow garbage (Φ → +∞ along scale blow-up; only the uniform diagonal
is scale-invariant) — caught and documented. (d) Rank-1-Gram hill climbing:
converges to Φ = 0.

**Approach B — proof.** Complete structural reduction obtained (see
discovery.md §2.1–2.4): scale-polynomial reformulation with the negative part
exactly the distinct-tuple sum; convexity in log-scales giving an exact
convex criterion and GP-dual condition; proved Lemma 1 and Corollary L
(log-convexity of PSD chains, with 2-line proof and 500/500 numerical
confirmation); identified that the naive global AM-GM condition
GM(repeat) ≥ AM(distinct) fails (0.871) so the weights must enter through the
Lemma-L system; quantified the pair-covering shortfall (2W_D vs 9.67 W_D).
Ruled-out route: diagonal-only domination T_m ≤ ((n)_m/n^m)W_m is false near
orthogonal configurations (caught an initial buggy numerical run that hid
this; corrected and documented).

### 4.2 Exact verification of m=n=4 (convex_check.py)

For random and adversarial PSD quadruples (near-orthogonal clusters, wild
scales, near-commuting), the convex minimization of F(u) =
Σ_repeat w(τ)exp(⟨e(τ)−1,u⟩) was run to convergence: min F ≥ (29/3)W_D in
220/220 configs, worst ratio 1.0289. The m=n=4 conjecture never failed.

### 4.3 Honest status

No complete proof of any new case; no counterexample. The m=n=4 gap is now a
precisely stated finite problem (explicit feasible GP-dual point via the
Lemma-L inequality system). Retained for a future session; all artifacts in
this lane. No shared or other-lane edits, no git, no children, no posts.
