# DORMANT formal plan — lane expanded-corpus-r534. NOT dispatched; no Lean run in this lane.

Inherited file name only; this lane ran on Claude Opus 5.5. Root decides whether and how to route either target.

## Target A: 368315 (typical orbit, interval-closed rowmotion)
Literal Lean statement needed: for every m≥1, Tendsto (fun n => (#{I : ICS (Fin m × Fin n) | orbit size of Row I = m+n+1} : ℚ)/#ICS) atTop (𝓝 1), with Row the composition of toggles in reverse linear-extension order.
Plan, no whole-Mathlib import (Finset, Nat.choose, Filter.Tendsto, ZMod):
1. ICS, toggle, Row as a fold over a fixed linear extension; invariance under choice of extension (or fix row-then-descending order, equal by commuting toggles).
2. Avoid importing source Theorem 1.1: prove the five transitions (shift, S→B_1/A_1, B_s→B_{s+1}, flip, A_s→A_{s+1}/last) directly by toggles on rows. This is the main formal cost and replaces the only external input.
3. Generic data: marks in ZMod N, Dyck word, matching; lemma W=(W1)W2 ↦ W1(W2).
4. Row^N=id on G_n and exact order; counting: lower bound on G_n via gap-binomial, upper bound on all ICS, O(n^{2m−1}) estimates for fixed m; limit from explicit rational bounds.
Cost: finite combinatorics throughout, no analysis beyond a limit of explicit rationals. Medium-high (toggle transitions and counting). Expect a long Fin/Nat bookkeeping body.
Fidelity risks: source literal "orbit of size m+n+1" exactly; n→∞ for fixed m.

## Target B: 342017 (smooth arithmetical structures)
Literal Lean statement needs a ruling on "grows at the same rate". Recommended: for each m≥1, ∃ c>0, ∃C, ∃n0, ∀n≥n0, c·binom(m+n−1,n) ≤ N(m,n) ≤ C·binom(m+n−1,n), plus the sharper Tendsto (N(m,n)/binom(m+n−1,n)) → α_{m−1}.
Plan: 1. SArith as a finite set of label pairs (bounded by Stern–Brocot length or Lorenzini-style bound from §B1); 2. bijection with coprime pairs, F recursion, word bijection (Nat strong recursion); 3. the eight 2×2 Matrix/ℕ identities (decide/norm_num); 4. automaton as an explicit recursion on (state, words) giving the coefficient recursion in §B5; 5. asymptotics: avoid partial fractions by proving explicit polynomial upper and lower bounds on order-k coefficients by induction on k, with the α recurrence. Direct Nat/ℚ. Cost: medium.

Fidelity risks: choice of reading; the source error (§B6) means Lean controls for m=3 must use the corrected values.

Both packets need: independent adversarial review, source/final check (Integers A68 not read; any core.ac.uk identity HOLD), family comparison against accepted scopes, paper, clean replay and root adjudication.
