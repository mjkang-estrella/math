# Lane progress — pi-algebra-matrix-r1 (batch 2, solo Pi, no children)

Read first: openai-proof-research/AGENTS.md, batch2 AGENTS.md, ledger.json,
prior-campaign-context.json, old lanes pi-matrix-discovery-r6/discovery.md and
pi-algebra-discovery-r2/discovery.md.

## Target dispositions (initial)

1. **372905 (sharp 3-operator Clarkson, p=2.5 blowup) — DISMISSED, no credit possible.**
   The identical source conjecture (Zhang 2602.01463v2 Conjecture 1.20 / 2410.21961v4)
   is already publicly refuted in Lean at p=9/4 (trureturing commit 22c3b6464…,
   recorded in first-batch prior-campaign-context.json exclusion for 372905).
   Any p=2.5 violation would be another instance of an already-refuted conjecture.
   Moreover the p=2.5 blowup itself was already resolved as an optimizer artifact in
   old lane parent-clarkson-r13/FINDINGS.md: "The prior p2.5 blowup is no evidence of
   a counterexample: this run's bounded normalized search at 2.5 found no violation."
   Nothing countable remains here. Do not invest.

2. **352327 (Choudhury–Sivakumar Conjecture 2.9, matrix Shapiro at p=12, 23) — PRIMARY TARGET.**
   Source read (cached 2110.10933.txt, full statement extracted). Novelty screen:
   Semantic Scholar citations API (2026-10-27): only 2 citing papers
   (Zhang–Wang 2504.00005 Nesbitt generalizations — scalar, no matrices;
   Kian–Alomari 2022 trace inequalities for convex functions — unrelated).
   No published resolution found. Open MathDB record + empty solutions NOT treated
   as novelty evidence; the screen is bounded (S2 corpus incomplete, Exa 429).

3. **332493 (Banica–Nechita four-projection trace inequality, 1602.04456v3 Conj 6.6) —
   SECONDARY.** Old lanes: parent-next-screen read source (Prop 6.7 proves S=0 only);
   pi-matrix-discovery-r6 random searches found min margin +4.7e-4 (holds). Refutation
   looks unlikely; a full proof looks deep (operator theory, Halmos two-projection
   analysis with four projections). Held as fallback; not primary.

## Working notes — Shapiro target

Exact source statement (2110.10933v1, Conjecture 2.9, p.7):
For positive definite A_1..A_p in C^{n×n}, F_p = Tr(Σ_i A_i (A_{i+1}+A_{i+2})^{-1})
(cyclic, A_{p+1}=A_1, A_{p+2}=A_2). Conjecture: F_12 ≥ 6n and F_23 ≥ 23n/2.
Known in source: p=3 (Thm 2.5), p=4 (Thm 2.7). Lift: F_{k+2}(A_1..A_k,A_1,A_2) = F_k + n,
so failure at any odd k in 5..21 lifts to 23 and failure at k ∈ {6,8,10} lifts to 12.

Structural findings so far (my derivations, to be verified numerically):
- Second variation at A_i = cI: Q = (1/4) Σ_i [⟨H_i,H_i⟩ − ⟨H_i,H_{i+2}⟩] ≥ 0 by
  Cauchy–Schwarz on step-2 orbits. So the equal point is a local min for EVERY p, n.
- Rank-one boundary family A_i = εI + a_i u_i u_i^T (n=2, real, consecutive lines
  non-parallel): inf over scales a_i of F_p equals p(R+1) for odd p and
  pR + (p/2)(T1+T2) ≥ p for even p, where R = (Π_i sin²(φ_i+φ_{i+1})/Π_i sin²φ_i)^{1/p},
  T± = (D1_even/D1_odd)^{±2/p}. So the rank-one n=2 family can never beat pn/2 = p.
  (Consistent with the old lane's failed p5/p6 searches.) Geometric-programming duality
  used: inf over positive scales of Σ c_k e^{lin(b)} = Σ_j m_j G_j over cycle decomposition.
- Alternating diagonal family (n=2, even p): A_even=diag(b,s), A_odd=diag(s,b) gives
  F_p = pn/2 EXACTLY (non-scalar equality case, commuting).
- All-parallel rank-one: F_p = p(n−1)/2 + Σ a_i/(a_{i+1}+a_{i+2}) ≥ p(n−1)/2 + γ_p.

Next: numerical Hessian at the alternating-diagonal equality family (n=2, even p) as p
grows; multistart searches at p=5..12 (n=2,3) and p=23; verify rank-one formula.
