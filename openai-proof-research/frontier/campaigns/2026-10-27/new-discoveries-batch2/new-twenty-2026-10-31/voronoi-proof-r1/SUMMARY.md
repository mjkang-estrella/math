# voronoi-proof-r1: SUMMARY (MathDB 371207, Day–Johnson conjecture)

Claude Opus 5.5, 2026-11-03. Hypothesis proof lane, **not acceptance**. Credit claimed: 0. Root decides.

## Outcome: PARKED, with the exact gap identified

I have **not** found a proof that the 8-player subspace profiles m = (t+1, t, …, t) (n = 7t + 1) are equilibria for all t. The conjecture is therefore not refuted by this lane.

What I did establish:

1. **Fidelity** (PROOF.md, Part A). The game comes from Stylianou arXiv:2510.25392v1, Section 1:
   - ties are split equally, and co-located players count separately;
   - positions need not be distinct (the Bristol abstract says so);
   - a player may move to any vertex, including an occupied one;
   - an equilibrium is a profile with no strictly profitable unilateral move (pure Nash).

   The Prop to prove is ∃ k ≥ 5 ∀ N ∃ n ≥ N ∃ P: IsEquilibrium P. Subspace profiles are legal, with 8 distinct points whenever the used functionals span the dual. For the family every m_f ≥ 1, so the points are distinct.
2. **Exact lemmas, fully proved** (Part B):
   - each player scores exactly 1/8, so it suffices to check player 0;
   - an exact finite binomial-sum formula for the deviator's score as a function of the deviation shape c;
   - the uniform-shift identity and a 4-dimensional lift;
   - a one-coordinate step identity with an exact simplification, σ(e_j) − 1/8 = ½ Δ_{m−e_g}(g⊥);
   - the parity lemma (ψ).
   - **Observation:** Stylianou's "balanced" 4-player profiles are exactly the 2-dimensional subspace profiles. So his Theorem 1.2 is the d = 2 analogue, and it holds for all multiplicities. For d = 3 it fails, for example for uniform multiplicities.
3. **All weight-free shortcuts fail, shown by exact counterexamples** (B.6):
   - Stylianou-style sign-class averaging: the worst pattern averages 55/384 > 1/8;
   - the step integrand is not pointwise nonpositive, nor after translation or sign-class averaging;
   - m → m + (1, …, 1) does not preserve equilibria;
   - the score is not coordinatewise monotone in the shape.

   So any proof must use the binomial weights, which makes it analytic.
4. **Analytic results** (Part C):
   - **Gaussian corner slope, rigorous within the Gaussian model:** dΓ/dc_g = −(3/4)h_o/t in every direction, where h_o = ∫φ³Φ⁵ ≈ 0.0083306. Equivalently, 8Γ ≈ 1 − 6h_o|c|/t.
   - **Local expansion for fixed moves, derived but not proved:**
     - if ψ ≠ 0: t·(8σ(c) − 1) → −h_o·(6|c| + 2·[|c| odd]);
     - if ψ = 0: t·(8σ(c) − 1) → −h_o·(6|c| − 14·[|c| odd]), which is +8h_o > 0 at |c| = 1.

     This **derives the empirical ψ rule**. It matches exact data up to t = 8: for example 0.06652 at t = 8 against the predicted 8h_o = 0.06664, and 0.0964 at t = 7 against 12h_o = 0.0999 for |c| = 2.
   - **Global Gaussian Monte Carlo (not validated numerics):** 8Γ ≤ 0.991 for |γ|₁ ≥ 0.25 and ≤ 0.951 for |γ|₁ ≥ 1.
5. **Missing Lemma M** (Part D). There are t_0 and κ > 0 such that for all t ≥ t_0 and all shapes c ≠ 0, σ(c) ≤ 1/8 − κ·min(|c|, t)/t. A proof also needs an exact check for t < t_0. The hard part is the mesoscopic regime, between O(1) moves and moves of size εt. That regime needs uniform 7-dimensional lattice local limit theorems with Edgeworth-level control at ties, plus validated numerics and an explicit Berry–Esseen bound for large moves. The Lean cost is prohibitive.

## Independent verification

My own checker (`scripts/vk.py`) is written from the definitions; vor.py was not reused. It implements:

- a direct sum over voters;
- an all-targets sphere-convolution Walsh–Hadamard method in exact int64, safe under wraparound;
- a separate shape enumerator (`scripts/smallmoves.py`).

All three agree exactly wherever they overlap.

- **Equilibria:**
  - n = 8, (2,1⁶): full brute force over every player, target and voter.
  - n = 15, (3,2⁶): all 8 players score 1/8; all 2,916 shapes checked by brute force against convolution; max deviation 19919/163840.
  - n = 22, (4,3⁶): convolution over all 2²² targets, 33 shapes checked by brute force; max deviation 1285389/10485760, at a one-coordinate move.
- **Failures:**
  - uniform t = 1, 2, 3: 17/128, 1057/8192 and 267791/2097152;
  - (5,5,5,1,0,0,0): 32935/262144.

  These are confirmed by brute force at the profitable target.
- **Larger t, small moves:** for t = 4 to 8 (n up to 57), every move with |c| ≤ 2 (t = 4, 5, 7) or |c| ≤ 1 (t = 6, 8) is unprofitable.
- **Invalid and superseded logs:**
  - the t = 10 run **overflowed int64 and is invalid** (`logs/sm_fam1_t10.INVALID.txt`); a guard is now in place;
  - two early logs are marked SUPERSEDED: `gauss_global` (a tie-splitting artifact) and `lattice_coeff` (cross-pair terms omitted).

## Prior art (bounded, 2026-11-03)

I found no k ≥ 5 result and no subspace or linear-code profile in any of the following:

- Stylianou's paper (only v1 is listed);
- the Bristol seminar abstract, which says the question "remains open for every k>4";
- the Rényi seminar abstract;
- Stylianou's PhD thesis abstract (awarded 20 Jan 2026);
- Johnson's 2018 Cambridge talk abstract;
- OpenAlex searches;
- standard web searches.

The Day–Johnson manuscript is unpublished and was not read, so it is unknown whether they examined subspace profiles. No denied route was used. Receipts and hashes are in `downloads/RECEIPTS.json`.

## Resource discipline

- No Lean, lake, SAT/ILP solver or compiled helper was run. The Sol worker's logs were glanced at as unverified diagnostics only.
- I ran 31 capped python3 -I runs through `scripts/run.py`, one at a time. Limits were 2-CPU affinity, CPU 120 s, wall 140 s and RLIMIT_AS 1.75 GiB, with MALLOC_ARENA_MAX=2. The peak sampled RSS was 1.21 GiB and the longest wall time 57 s. No caps were hit, and no background job is left running.
- Everything was written inside this lane. No git, ledger edits, publication or external messages.

## Files

- `PROOF.md`: complete proofs of the exact lemmas, the derived asymptotics and the exact gap.
- `STATEMENT-CORRESPONDENCE.md`: definitions and a Lean statement draft, **UNCOMPILED**.
- `results.json`: structured outcome and file hashes.
- `verify-results.json`: output of the verification bundle.
- `scripts/`: checker and analysis scripts; `logs/`: one log and one receipt per run.
- `downloads/`: prior-art pages and receipts.

## Recommendation to root

The lead stays strong as evidence, and the mechanism is now understood: a Gaussian corner slope plus a ψ-dependent lattice term, both with explicit constants. An exact elementary proof looks unlikely, because B.6 rules out all weight-free arguments. A rigorous refutation is a substantial analytic paper, centred on Missing Lemma M, and Lean formalization is not realistic. I suggest no credit-track Lean work for 371207 unless an analytic proof of M is first obtained and reviewed.
