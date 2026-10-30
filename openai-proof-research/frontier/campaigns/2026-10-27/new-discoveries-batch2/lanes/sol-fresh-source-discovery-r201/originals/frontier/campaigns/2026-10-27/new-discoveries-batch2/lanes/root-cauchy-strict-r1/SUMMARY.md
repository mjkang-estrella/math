# SUMMARY.md — pi-cauchy-strict-discovery-r1

## Result (one nominated outcome)

`alpha < 1/n => K_alpha in STP_n` for `K_alpha(t,x) = 1/(t^2 + 2 cos(pi alpha) t x + x^2)`
on `(0,inf)^2` — resolves the Simon conjecture (arXiv:1305.1173 displayed Conjecture (2);
MathDB 325521, open). Complete proof in PROOF.md; independent verification below.

## Strongest objection / falsifier

**Objection (substantive):** the proof consumes Theorem 1 of Simon, Constr. Approx. 44
(2016) 103–120 (`f_alpha(xy^{-1}) in TP_n` for `alpha < 1/n`) as a cited black box, and the
Zolotarev/Sato convergent series for `f_alpha` as a classical black box. If either
statement is misquoted (e.g., the published Constr. Approx. version differs from arXiv
v1 — only v1 is public and was read), the proof weakens. Mitigations: the conjecture's
hardness is explicitly about *strictness* (Remark 2(b) of 1412.0132), not `TP_n`, whose
classification is stated identically in the arXiv text, the MathDB record, and the
publisher's page; and the series was verified to ~1e-40 against independent computations
(inverse Laplace; closed form at `alpha = 1/2`).

**Falsifier:** a single explicit `m <= n`, `alpha < 1/n`, and ordered tuples with
`det[K_alpha(t_i, s_j)] = 0` would refute the theorem; the proof shows this impossible,
and high-precision scans (mpmath dps=60, n <= 7, random and near-equal adversarial tuples)
found all minors strictly positive, with failures appearing only above `1/n`
(scripts/check_fast.py, Check 3/D).

**Second objection (novelty):** the strictification mechanism (Gram/Andreief + analytic
non-degeneracy) might be a known Karlin-type lemma, reducing the work to a routine
citation. Screened: no such public statement located (details in discovery.md); the source
itself declares the factorization route powerless for strictness. Residual risk documented,
not eliminated.

## Honest gaps

1. **No Lean artifact.** No Lean/elan toolchain exists in this lane's environment, and a
   literal endpoint is blocked anyway by two source dependencies outside mathlib:
   (a) Simon's `TP_n` theorem for `f_alpha(xy^{-1})` (its own proof uses a local limit
   theorem and Karlin's Theorem 3.2.1), and (b) the Zolotarev/Sato series plus the stable
   Mellin transform and `|Gamma(1+iu)|^2`. None may be silently assumed or axiomatized.
   A literal formalization is a multi-module project (see plan below). **Status: no formal
   PASS claimed; conditional analytic-kernel lemmas alone would not be a full endpoint.**
2. The published JAT/Constr.Approx. bodies were not read (paywalled); evidence is at
   arXiv-HTML + publisher-snippet level.
3. Karlin (1968) and Pinkus (2010) book bodies were not directly accessible; the
   nonexistence of a covering strict-composition theorem is argued from the accessible
   literature and from 1412.0132 Remark 2(b), not from a full book scan.
4. Numerics are diagnostics only, never proof; the ill-conditioning of the Zolotarev
   series for `alpha -> 1, x -> 0` (catastrophic cancellation) limited some float checks
   to `alpha <= 0.6` regimes; the proof itself never evaluates `f_alpha` numerically.

## Literal Lean plan (pinned toolchain lean4.34.1 / mathlib d13f23b7; standard3 only)

Target statement (top level, `CauchySTP.lean`):
```
theorem K_alpha_STP (n : ℕ) (hn : 2 ≤ n) (α : ℝ) (hα : 0 < α) (hlt : α < 1 / n) :
    StrictTotalPositiveOfOrder (K α) n
```
with `K α t x = 1 / (t^2 + 2 * Real.cos (π * α) * t * x + x^2)` and `StrictTotalPositiveOfOrder`
defined as: ∀ m ≤ n, ∀ strictly monotone tuples, `(fun i j => K α (t i) (s j)).det > 0`.

Modules, each closed (no `sorry`/`axiom`/`unsafe`/`native_decide`):
1. `Andreief.lean` — Andreief identity for continuous `φ_i, ψ_j` with `∫|φ_iψ_j| < ∞`:
   finite Cauchy–Binet (`Matrix.det` expansion over `Fin m → Fin N` subsequences; mathlib
   has the ingredients) + approximation/Fubini over `ℝ^m` (mathlib measure theory).
2. `StableSeries.lean` — Zolotarev series: define `f α x = Σ' k, c k * x^(-(α*k+1))`,
   prove absolute local-uniform convergence (`summable` comparison; the term ratio is
   `O(k^{α-1})`), hence `AnalyticOn` on `(0, ∞)`, and `c k ≠ 0` for `k ≤ n` when `α n < 1`.
   **Hardest honest piece**: proving this series equals the stable density with Laplace
   transform `e^{-λ^α}` (Sato/Zolotarev) — must be proven, not assumed.
3. `TPAlpha.lean` — Theorem A (`f α (x * y⁻¹)` TP_n for `α < 1/n`): must reprove Simon's
   argument (local limit theorem for `X_{α,n}` densities — Fourier/characteristic-function
   machinery largely absent from mathlib — plus the classical `TP_n` of `(y-x)_+^{β-1}`
   for `β > n-1`, itself a Karlin theorem to be reproved). This is the dominant cost.
4. `Gram.lean` — the Gram representation: the Mellin-transform derivation of
   `J_α(d) = sin(πα)/(2π(cosh(αd)+cos(πα)))` (needs item 3's Mellin facts plus Fourier
   uniqueness on `L¹`) and Andreief application.
5. `Strictify.lean` — Lemma 4.1 + Lemma 5.1: analytic zero sets on connected open sets
   (identity theorem propagation), the asymptotic expansion of `det[Σ_k c_k e^{(αk+1)U} r_k c_k']`
   with error `o(e^{(m+αm(m+1)/2)U})`, and the Vandermonde reduction
   `det[z_i^{αk+1}] = (∏ z_i) * det[(z_i^α)^{k-1}]` (mathlib `Matrix.vandermonde`) giving
   nonvanishing. Self-contained given 1–4.
6. Assembly and the `m ≤ n`/`αm < 1` bookkeeping.

Estimated effort: items 1, 5, 6 are weeks-scale; items 2–4 (source reproofs, especially 3)
are months-scale and are the reason **no formal component was started** in this lane
(per the brief: do not invest in heavy formalization before substantive/prior gates, and
the toolchain is absent here anyway). The lane delivers the ordinary proof + verification;
the formal endpoint stays with root.

## Independent verification performed (no second agent; two disjoint methods)

* Symbolic/asymptotic: full analytic proof (PROOF.md), written independently of the
  numerics; the one earlier derivation attempt that failed (termwise series integration
  for `J_α`) was discarded when its prediction contradicted numerics, and replaced by the
  Mellin/Fourier derivation — this trap is documented in progress.md.
* Numerical (diagnostic only): (i) Zolotarev series vs closed form (`α=1/2`) and vs
  numerical inverse Laplace (`α ∈ {0.3,0.55,0.7,0.9}`) — agreement ≤ 1e-33 in
  well-conditioned regimes; (ii) the Gram representation and `J_α` closed form —
  relative error ≤ 5e-6 (quadrature-limited); (iii) discrete Cauchy–Binet/Andreief —
  ≤ 1e-12; (iv) `D_x` nonvanishing asymptotics ratio → 1 for `(m,α)` up to `(6,0.15)`;
  (v) strict positivity of all minors for `n ≤ 7` strictly inside `α < 1/n` (random and
  adversarial near-equal tuples, dps 60), with negative minors appearing only for
  `α > 1/n` as the classification demands.

## Files

* `discovery.md` — outcome, quantifiers, novelty/substantive screens, credit recommendation
* `PROOF.md` — complete proof
* `progress.md` — work log with the discarded route
* `provenance.json` — URLs, hashes, access limits
* `scripts/` — `falpha.py`, `check_fast.py`, `check_final.py`, logs
* `cites-*.json` — Semantic Scholar citation dumps (raw)
