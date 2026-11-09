# P1 — MathDB 338290: counterexample to Conjecture 3.8 of arXiv:1801.08029v2

Screening-stage brief. No credit. Needs independent hypothesis review, a registry/prior check and formalization.

## Source and literal quantifiers
- Source: Acharya, Mukherjee, Sahoo, arXiv:1801.08029v2 (17 Feb 2020), retained `sources/arxiv/1801.08029.pdf`. The text lines cited below are from the retained `.txt`.
- Definitions (lines ~37–62): players p_1..p_m have weights w_i and a preassigned quota q. C is winning iff Σ_{p_i∈C} w_i ≥ q. (p_i, C) is a critical pair iff C ∈ W and C−{p_i} ∉ W. γ_i is the number of critical pairs for p_i. The **absolute** index is β_i = γ_i / 2^{m−1} and the **normalized** index is β̃_i = γ_i / Σ_j γ_j.
- Conjecture 3.8 (line ~380): "Let w_1,…,w_m be positive weights, w their maximum, N = Σ w_i; then the relative Banzhaf indices β_i ≤ 2w/N". The surrounding sentence says the relation is "valid for any voting game". No restriction is placed on q.
- Scope ambiguity: the word "relative" points to the normalized index, but the symbol β_i is the absolute index. Both readings are refuted below. Both refuting games use a strict-majority quota q > N/2, so neither depends on a degenerate quota.

## Counterexample A (absolute index)
Weights (3,1,1,1,1), so N = 7, w = 3, and 2w/N = 6/7. Quota q = 4 > 7/2.
- Big player: a coalition containing it plus k small players wins iff k ≥ 1. Without it, k small players win iff k = 4. So it is critical iff 1 ≤ k ≤ 3, which gives γ = 4+6+4 = 14.
- β_big = 14/2^4 = 7/8 > 6/7, since 49 > 48.

## Counterexample B (normalized index, and also absolute)
Weights (7,1,1,1,1,1,1,1,1), so N = 15, w = 7, and 2w/N = 14/15. Quota q = 8 > 15/2.
- Big player: critical iff 1 ≤ k ≤ 7 small partners, which gives γ_big = 2^8 − 2 = 254.
- Small player i: critical exactly in {big, i} and in {all eight small players}, so γ_i = 2.
- β̃_big = 254/270 = 127/135, and 127·15 = 1905 > 1890 = 14·135. So β̃_big > 14/15.
- β_big = 254/256 > 14/15 as well.

General family: weights (k; 1^{k+1}) with q = k+1. The normalized index violates the bound iff 2^{k+1} > 4k²+4k+2, i.e. for every k ≥ 7.

## Decisive check (run)
`scripts/banzhaf.py` (guarded; `runs/banzhaf.r1.txt`) does an exact rational exhaustive search over m ≤ 9, integer weights ≤ 8, and all quotas.
- No normalized-index violation exists with m ≤ 8.
- The first one is (7;1^8), q = 8.
- An absolute-index violation already exists at m = 3: (8,7,7) with q = 8, a non-majority quota.
- The family table was recomputed for k = 1..11.

## Certificate / formal dependencies
- Certificate size: one 9-player game, 512 coalitions; exact integer counting.
- A Lean endpoint needs a finite definition of the game, swings and both indices. It can be proved by `decide` over `Finset (Fin 9)` (512 subsets), or by the explicit binomial argument above. It does not need native_decide.

## Objections / limits
- Prior/novelty: HOLD. No current registry or successor search route was available. The counterexample is elementary, so prior public notice is plausible.
- The authors may have intended a restricted class (e.g. their EU-type games), but the literal statement says "any voting game".
- Possible "routine" objection: this is a direct finite refutation, not an adaptation of a known theorem.
