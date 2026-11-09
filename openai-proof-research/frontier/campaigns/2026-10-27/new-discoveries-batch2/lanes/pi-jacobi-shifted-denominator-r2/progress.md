# progress — pi-jacobi-shifted-denominator-r2 (2026-10-27, solo)

1. Read context: batch/root AGENTS.md, ledger.json, prior-campaign-context.json,
   old lane (2026-10-26) discovery/progress/provenance + jacobi_shifted_core.py.
2. Verified sources live (2608.23006v2, 2609.29531v2) against cached texts.
3. Built fresh exact pipeline `scripts/core.py` (A_n via S₂/C̃, cumulant recursion);
   fixed an off-by-one; cross-checked κ₁..κ₄, ℓ₁..ℓ₄ bookkeeping (κ₂ = (u−v)(u+v−3)/48
   shifted; (A−B)(A+B−7/2)/48 original, ℓ₂ = −7/96 ✓, E₂ = 5 ✓).
4. `scripts/structure.py`: mod-2 normal form; antisymmetry observations.
5. **Theorem 1 proved**: B_n(v,u) = conj B_n(u,v) → ImB_{2k} = 0, (u−v)|ImB_n,
   symmetric quotient; re-derives companion Thm 1.5 as corollary.
6. **Theorem 2 proved**: exact decomposition ImB_{2m+1} = slice-difference + uv(u−v)R,
   R symmetric; layer interpretation via companion Cor 8.2 (W = layer 0, K = layers ≥1,
   only r ≤ ⌊(2m+1)/3⌋ enter).
7. **Theorem 3 proved**: Law ⟺ (A) slice law ∧ (B) 2^{3m} | R. Attainment at pure
   coefficients comes free from (A).
8. `scripts/extended_checks.py`, `decomposition.py`: all statements verified m ≤ 30
   (n ≤ 61); refined K-minimum pattern 3m + 1_{m=2^k−1}; degree law n ≤ 61;
   top-layer (14) r ≤ 31.
9. Wrote discovery.md (proofs + verification + obstacles), SUMMARY.md, provenance.json,
   verification_results.json. No PROOF.md / Lean: law not closed (deliberate — see
   discovery.md §6).

Not attempted (documented dead ends + unproved routes in discovery.md §5, §7).
