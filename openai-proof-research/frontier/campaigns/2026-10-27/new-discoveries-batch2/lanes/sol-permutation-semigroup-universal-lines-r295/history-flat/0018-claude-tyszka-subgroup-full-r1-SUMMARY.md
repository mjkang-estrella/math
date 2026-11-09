# claude-tyszka-subgroup-full-r1: Tyszka Conjecture 3 fully resolved by a classical bridge; EXCLUDE, zero credit

**Target.** r214 shortlist #2: arXiv:math/0702558v86 (latest version, 4 Dec 2009; live abs re-fetched and byte-identical to r214's frozen copy), Conjecture 3, printed p21. For every additive subgroup G ⊆ C and every system in n variables of equations xi=1 / xi+xj=xk that is solvable in G^n, there is a solution in (G∩Q)^n with |xj| ≤ 2^(n−1).

**Result: the full literal statement is true** for all G, all n and all such systems. The proof is in discovery.md and has five steps:
1. Smith normal form moves a G-solution to an H=G∩Q solution. The forced transformed coordinates are rationals lying in G; the free ones are set to 0.
2. The coordinates generate a cyclic group (1/q)Z ⊆ H, so scaling by q gives an integer system.
3. Borosh–Flahive–Rubin–Treybig, Proc. AMS 105 (1989) 844–846: an integer-solvable system of rank m has an integer solution bounded by the largest m×m minor of (A,b), with no sign condition. The actual body was read and its proof checked, including an independent shortest-word proof of the Gomory step.
4. The incidence/multilinear lemma bounds every such minor of (A_R, qb_R) by q·2^(m−1). After homogenizing, the row x_{i0}=1 is "simple", so at most m−1 rows double the bound.
5. Dividing by q gives |y_j| ≤ 2^(m−1) ≤ 2^(n−1). The doubling chain shows the bound is sharp.

**Disposition.** This is a routine classical subsumption: the 1989 theorem predates every version of the conjecture. Zero credit. r214's Conjecture 4 bridge and G⊇Q subcase are reused, not recounted. The overlapping 0807.3010v25 conjecture (I) and its p10 integer remark are covered too. In later Tyszka arXiv bodies (1110.3549, 1102.4122, 0901.2093, 1109.3826, 1511.04004) and two web searches we found no public resolution or BFRT citation. The MLQ 2010 version and the citing literature or proof registries were not swept.

**Routes.**
- Route A (BFRT) succeeds.
- Route B (Tyszka's Observation-3 iteration over H) fails as stated. The exact parity obstruction: x4 = 2x2+1 makes {x4=0} Z-infeasible while Q-feasible.
- Route C (approximation in a dense H) is unnecessary.

**Controls.** The capped exact checker passed: checks.json, scripts/checker.py, guard peak RSS about 13.5 MB, wall 0.44 s. Finite controls are not the proof.

Root alone accepts/counts/stages; 9 additional/39 total, next 40, unchanged. No Lean, manuscript, git, posting or MathDB edits.
