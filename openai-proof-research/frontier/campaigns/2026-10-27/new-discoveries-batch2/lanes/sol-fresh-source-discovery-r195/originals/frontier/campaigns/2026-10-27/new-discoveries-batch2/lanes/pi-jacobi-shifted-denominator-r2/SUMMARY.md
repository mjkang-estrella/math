# SUMMARY — lane pi-jacobi-shifted-denominator-r2

**Target**: exact δ_r in Remark 3.8 of arXiv:2608.23006v2 (exponent of 2 in the common
denominator of the shifted-variable coefficients of κ_r, Definition 2.1). Guessed law:
δ_r = 2r + ν₂((r−1)!).

**Outcome: partial credit claim — major structural theorems proved, law not closed.**

## What is proved (all-order, self-contained proofs in discovery.md §1–3)

1. **Theorem 1 (antisymmetry).** B_n(v,u) = conj(B_n(u,v)) for all n ≥ 1. Hence
   Im B_{2k} = 0 ∀k (even cumulants real), (u−v) | Im B_n with symmetric quotient,
   and F(Z)F(−Z) ∈ R[[Z^{−1}]]. Corollary: re-derives and strengthens the companion's
   Theorem 1.5 (Im g_{2k} = 0) — ours holds for the full polynomial at all (u,v).
2. **Theorem 2 (exact decomposition).**
   Im B_{2m+1} = [slice difference] + uv(u−v)R_{2m+1}, R symmetric ∈ Z[u,v].
   Pure coefficients of ImB are exactly ± coefficients of the one-center slice
   ImB_{2m+1}(0,v); mixed coefficients are uv(u−v)-multiples.
3. **Theorem 3 (exact reduction).** The Law (min ν₂(ImB_{2m+1}) = 3m ⟺
   δ_{m+1} = 2(m+1)+ν₂(m!)) holds **iff** (A) the one-center slice law
   (2^{3m} | ImB_{2m+1}(0,v), [v^{m+1}] exactly 2^{3m}·odd) and (B) 2^{3m} | R_{2m+1}.

## What is verified (exact integer arithmetic, m ≤ 30 / n ≤ 61)

Law itself; slice law (A); coupling divisibility (B); refined minimum
min ν₂(K) = 3m + 1_{m=2^k−1}; degree law deg B_n = ⌈n/2⌉ (n ≤ 61); top-layer
identification (14) with γ_rI_r (r ≤ 31); mod-2 normal form
ImB = 2^{3m}(u−v)Q̃, Q̃ ≡ (u+v)^m + 1_{m≡1(4)}(u+v)^{m−1}.

## Why not full credit

The Law is not proved: (A) and (B) remain open. (A) is a one-variable cumulant
problem for log ₂F₁(1/2−β, 1/2+β; 1−Z; y₀); (B) needs a bivariate version of the
companion's §10 valuation transfer. No PROOF.md, no Lean (a conditional skeleton was
deliberately not written — see discovery.md §6).

## Files

- `discovery.md` — theorems, proofs, verification table, obstacles.
- `scripts/core.py` — fresh exact pipeline (κ₁..κ₄ and ℓ₁..ℓ₄ cross-checked).
- `scripts/structure.py`, `extended_checks.py`, `decomposition.py` — checks.
- `verification_results.json`, `progress.md`, `provenance.json`.
