# Discovery lane report — pi-algebra-discovery-r2 (2026-10-26)

Agent: Pi, research sub-agent, solo, no children, standard speed, no external
posting, no git. Own lane only. Ledger read first (16 accepted / 21 excluded);
active other lanes (332493 four-projections; combinatorial discrete targets)
avoided; matrixShapiro 352327 prior negative searches not duplicated.

**Candid verdict: NO countable discovery this session.** Two substantive
investigations were completed: (1) the parent-suggested Krishna C*-Casas–Alvero
lead is definitively ruled out on the actual source hypotheses; (2) a deep
attack on MathDB 346741 (Recht–Ré Conjecture 2, sum-of-norms form) produced a
complete structural reduction of its first open case (m=n=4), a fully proved
elementary log-convexity lemma, exact convex-criterion verification with zero
counterexamples, and a precise statement of the remaining gap. No PROOF.md is
filed because no complete new theorem resolving a source question was finished.

---

## Part 1 — Ruled out: Krishna 2206.09197 / MathDB 355066 (C*-algebraic Casas–Alvero)

Actual source read in full: arXiv:2206.09197v2 (3 pp.), PDF SHA256
b46325f797cb755d3261a65a0774d59a1ff35b0f8d9bd12da8e9a1c8a86f7b72.
Conjecture 2.1 hypothesis: **A commutative** C*-algebra; P(z) = ∏(z − a_i);
conclusion P = (z−a)^n. Degree 2 proved in-source via Gelfand–Naimark.

The parent's M2(C) sketch (R² = 0, P(z) = (z−R)z², shared zeros 0 and R/3)
fails for three independent reasons:

1. **Scope.** M2(C) is noncommutative; the conjecture quantifies over
   commutative C*-algebras only.
2. **No nilpotents in scope.** C(X) is reduced; the source's own degree-2 proof
   is exactly "(b−a)² = 0 ⟹ a = b". The sketch's mechanism cannot occur.
3. **Equivalence to classical CA.** For A = C(X) everything is pointwise: the
   C*-hypothesis holds iff each scalar p_x = ∏(t − a_i(x)) satisfies the
   classical Casas–Alvero hypothesis; classical CA gives p_x = (t−λ(x))^n
   pointwise, hence a_1 = … = a_n and P = (z−λ)^n; conversely A = ℂ recovers
   classical CA. So Conjecture 2.1 is **equivalent, degree by degree, to the
   classical Casas–Alvero conjecture** — no source-faithful nontrivial outcome
   exists without resolving classical CA itself (open; Ghosh arXiv:2501.09272
   is an unrefereed preprint, and MathDB carries 365893 "Ghosh's
   regular-sequence conjecture" as open). The dual-numbers counterexample
   P(z) = (z−ε)z² over ℂ[ε]/(ε²) is the standard known nilpotent obstruction,
   uncountable under strict novelty in any reading.

## Part 2 — Deep dive: MathDB 346741, Recht–Ré Conjecture 2 (sum of norms)

Live record fetched 2026-10-26 (sources/346741-live.json; solutions, human
solves, model attempts, comments all empty; status open). Statement:

    (1/n^m) Σ_{all ordered j_1..j_m} ‖A_{j1}⋯A_{jm}‖ ≥ ((n−m)!/n!) Σ_{distinct} ‖…‖

**Status verified against primary sources.** Lai–Lim arXiv:2006.01510 states it
as Conjecture 2 and leaves it open; proved for m = 2, 3 for every unitarily
invariant norm by Israel–Krahmer–Ward (arXiv:1411.0333, abstract read). Fresh
October 2026 work does not touch it: arXiv:2610.00155 (m=2 Loewner sharpness
only) and the Zenodo "Exact Low-Length Recht–Ré Inequalities" manuscript
(Loewner sums E_{m,n} only; its p.2 explicitly flags the termwise-norm variant
as adjacent and distinct). **The case m ≥ 4 is open in the literature.**

### 2.1 Structural reduction (new observation, this lane)

Write A_i = t_i B_i with t_i > 0 and B_i PSD. Since A_{j1}⋯A_{jm} =
(∏_k t_{jk}) B_{j1}⋯B_{jm}, the conjecture at fixed m,n is equivalent to

    P(t) := Σ_{repeat tuples τ} w(τ) Π_k t_{τ_k} − (n^m/(n)_m − 1) Σ_{distinct d} w(d) Π_{j∈d} t_j ≥ 0  ∀ t ∈ R_{>0}^n,

where w(τ) = ‖B_{τ1}⋯B_{τm}‖ (operator norm; any fixed UI norm works). Key
points:

- **The negative part is exactly the distinct-tuple sum**, with coefficient
  n^m/(n)_m − 1 > 0; e.g. m=n=4 gives 29/3.
- **Sharpness is exactly at the AM-GM point**: for w ≡ c (all B_i equal) P
  reduces to ((Σt)^m − n^m·∏t)·c ≥ 0, i.e. precisely the AM–GM inequality —
  so any proof must be exactly sharp at B_1 = … = B_m, matching the classical
  AM-GM equality structure. (Consistent with Recht–Ré's motivation.)
- **Convexity**: P(t)/∏_i t_i = Σ_τ w(τ) exp(⟨e(τ)−1, u⟩) − (n^m/(n)_m − 1)Σ_D w(d),
  u = log t, e(τ) = multiplicity vector. This is a **convex function of u**,
  so the quantifier "for all scales" is an exactly checkable convex condition
  (no heuristics), and the geometric-programming dual gives the equivalent
  condition: ∃ weights λ on repeat tuples with Σλ_τ(e(τ) − 1) = 0 and
  Π_τ (w(τ)/λ_τ)^{λ_τ} ≥ (n^m/(n)_m − 1) Σ_D w(d).

### 2.2 A proved elementary lemma (log-convexity of PSD chains)

**Lemma 1.** For PSD A, B and arbitrary X: ‖A^{1/2}XB^{1/2}‖² ≤ ‖AX‖‖XB‖.

*Proof.* ‖A^{1/2}XB^{1/2}‖² = λmax(B^{1/2}X*AXB^{1/2}) = λmax(X*AXB) (using
λ(PQ) = λ(QP) twice) ≤ ‖X*AXB‖ = ‖(X*A)(XB)‖ ≤ ‖X*A‖‖XB‖ = ‖AX‖‖XB‖. ∎

**Corollary L.** For PSD A, B, C, D (operator norm, and by the same proof any
unitarily invariant norm via the same λmax start for the spectral case; the
UI-norm extension needs the standard argument and is not claimed here):
‖ABCD‖² ≤ ‖A²BC‖·‖BCD²‖.

*Proof.* Lemma 1 with A → A², B → D², X → BC. ∎

Consequence for Conjecture 2: **every distinct-product norm is dominated by
the geometric mean of two repeat-product norms**:
w(d₁,d₂,d₃,d₄)² ≤ w(d₁,d₁,d₂,d₃)·w(d₂,d₃,d₄,d₄), and both dominating tuples
are repeat tuples (for n=m=4), whose scale monomials are AM-GM-complementary
(e(t) + e(t') = (2,2,2,2)). Numerically ‖ABCD‖² ≤ ‖A²BC‖‖BCD²‖ held in 500/500
random PSD trials (worst ratio 0.997).

### 2.3 What is verified (exact, no counterexample anywhere)

All scripts in this lane; seed fixed; runnable.

1. `verify_rank1.py` — rank-1 witnesses A_i = v_i v_i^T reduce every product
   norm to products of inner products; 2215 random configs (d ∈ {1,…,16},
   n ∈ {4,5,6,8}, m ∈ {4,5,6}): **zero violations** of E[walk] ≥ E[path];
   minimum gap 0 exactly at parallel configurations (the equality case).
2. `search_rr2.py` / `opt_rr2v2.py` — random PSD (Wishart, d ∈ {2,3}) and
   hill-climbing over 2×2 PSD with per-matrix scales (clamped): all converge
   to Φ = 0, the all-equal basin; no negative Φ found.
3. `convex_check.py` — the **exact** convex criterion of §2.1 at m=n=4:
   60 random + 160 adversarial configs (near-orthogonal clusters, wild scales,
   near-commuting families): min F(u)/((29/3)W_D) ≥ 1.0289 in all cases.
   The m=n=4 conjecture held in every exact test.

### 2.4 The precise remaining gap (for a future proof of m=n=4)

Need: Σ_{232 repeat tuples} w(τ)Π_τ ≥ (29/3)·Σ_{24 distinct} w(d)·t₁t₂t₃t₄
for all scales. The naive global AM-GM reduces this to GM(repeat norms) ≥
AM(distinct norms), which **fails** numerically (worst ratio 0.871) — the
weights must be exploited through the Lemma-L log-convexity system
w(a,b,c,d)² ≤ w(a,a,b,c)w(b,c,d,d), which propagates to a whole graph of
inequalities on repeat tuples (e.g. w(a,a,b,c)² ≤ w(a,a,a,b)·w(a,b,c,c)). The
required object is an explicit feasible dual point λ (a fractional packing of
AM-GM groups whose exponent vectors average to (1,1,1,1)) with group values
bounded below through that system; at w ≡ c the unique sharp choice is
uniform, so the construction must degenerate exactly to full AM-GM there.
Pair-covering alone gives only 2W_D of the needed 9.67·W_D. This is a
self-contained finite combinatorial-matrix problem, fully specified in this
lane, and is the recommended next step. The general n > m case needs the same
covering per monomial t_{d1}⋯t_{dm} with coefficient n^m/(n)_m − 1.

Also probed and ruled out as proof routes this session: diagonal-only C-S
domination S_m ≤ T_m ≤ ((n)_m/n^m)W_m (second inequality false near orthogonal
configurations, ratio ≫ 1 — test in lane notes), and direct pair covering
(factor ~4.83 short).

## Files

- search_rr2.py, opt_rr2.py, opt_rr2v2.py — counterexample searches (all clean)
- verify_rank1.py — rank-1 walk/path verification (2215 configs, clean)
- convex_check.py — exact convex criterion for m=n=4 (clean)
- sources/ — live MathDB records, Krishna PDF/TXT with SHA256s
- provenance.json — source register
