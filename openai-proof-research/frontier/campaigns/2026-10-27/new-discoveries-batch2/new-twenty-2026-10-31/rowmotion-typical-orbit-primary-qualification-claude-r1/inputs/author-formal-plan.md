## Target A: 368315 (typical orbit, interval-closed rowmotion)
Literal Lean statement needed: for every m≥1, Tendsto (fun n => (#{I : ICS (Fin m × Fin n) | orbit size of Row I = m+n+1} : ℚ)/#ICS) atTop (𝓝 1), with Row the composition of toggles in reverse linear-extension order.
Plan, no whole-Mathlib import (Finset, Nat.choose, Filter.Tendsto, ZMod):
1. ICS, toggle, Row as a fold over a fixed linear extension; invariance under choice of extension (or fix row-then-descending order, equal by commuting toggles).
2. Avoid importing source Theorem 1.1: prove the five transitions (shift, S→B_1/A_1, B_s→B_{s+1}, flip, A_s→A_{s+1}/last) directly by toggles on rows. This is the main formal cost and replaces the only external input.
3. Generic data: marks in ZMod N, Dyck word, matching; lemma W=(W1)W2 ↦ W1(W2).
4. Row^N=id on G_n and exact order; counting: lower bound on G_n via gap-binomial, upper bound on all ICS, O(n^{2m−1}) estimates for fixed m; limit from explicit rational bounds.
Cost: finite combinatorics throughout, no analysis beyond a limit of explicit rationals. Medium-high (toggle transitions and counting). Expect a long Fin/Nat bookkeeping body.
Fidelity risks: source literal "orbit of size m+n+1" exactly; n→∞ for fixed m.

