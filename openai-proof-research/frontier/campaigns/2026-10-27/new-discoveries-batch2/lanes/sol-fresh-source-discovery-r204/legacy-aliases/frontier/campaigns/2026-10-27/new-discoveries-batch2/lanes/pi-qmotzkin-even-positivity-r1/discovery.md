# discovery.md — pi-qmotzkin-even-positivity-r1

New mathematical findings (all exact-verified; see PROOF.md for proofs):

## D1. Height-sum walk model for M̃† (new statistic for this sequence)
M_n(q) = Σ_{w Motzkin walk 0→0, length n} q^{Σ_{t=1}^{n−1} w_t}.
Proved directly from the recurrence (first-step/excursion decomposition). The source's A.5 uses tunnel
length; the paper's stated obstacle ("the only statistic we can see that results in Cigler's q-Motzkin
number is tunnel length") is bypassed: the height-sum statistic supports LGV-type reasoning.
Verified: (B^i)_{0,0} = M_i for i ≤ 25.

## D2. J-fraction parameters and OP norms
μ_m is the moment sequence of the Jacobi parameters (a_h, b_h) = (q^h, q^{2h+1}); monic OP norms
h_j = q^{j²}; hence Δ_n^{(0)} = ∏_{j<n} q^{j²} = q^{n(n−1)(2n−1)/6} (re-derivation of A.2).

## D3. Claim R (reduction to a walk-matrix minor)
Δ_n^{(r)} = q^{β_n} · det[(B^r)_{[0,n)×[0,n)}], B_{h,h′} = q^{h′}[|h−h′| ≤ 1] (rows h, cols h′).
Verified exactly for r ≤ 7, n ≤ 5. Turns A.4 into: det[(B^{2k})_{n×n}] ∈ Z≥0[q].

## D4. Shift-1 determinant via an elementary tridiagonal recursion (re-derivation of A.3)
det[(B)_{n×n}] obeys d_n = q^{n−1} d_{n−1} − q^{2n−3} d_{n−2}, d_0 = d_1 = 1, giving exactly
κ_n q^{binom n 2} with κ = (1,1,0,−1,−1,0,1,1,0,…) — period-6 sign pattern; matches A.3 exactly (n ≤ 14).

## D5. THEOREM A — the k = 1 case of A.4 (shift 2) is proved, with an explicit monomial formula
Δ_n^{(2)} = q^{β_{n+1}−1}(1+q) + Σ_{2≤j≤n, j≢2 (mod 3)} q^{β_{n+1}−j}.
Via Desnanot–Jacobi + A.2 + A.3 ⟹ Δ_n^{(2)} = q^{n²}Δ_{n−1}^{(2)} + κ_n² q^{n(n−1)(2n+5)/6}.
Exact match to direct determinants n ≤ 14. New: the source conjectures A.4 without proving any k ≥ 1 case.

## D6. Square (Gram) identity and its limits
det[(B^{2k})_{n×n}] = q^{binom n 2} Σ_M det[T_{[0,n),M}]² q^{ΣM}, T = B^k D^{−1} (symmetric).
k = 1: T = K = I+S+Sᵀ has all minors in {0,±1} (biconvex bipartite graph ⟹ total unimodularity)
⟹ second, combinatorial proof of D5. k ≥ 2: mixed-sign minors appear (k=2, n=3, M=(0,1,3)):
positivity then holds only by cross-M cancellation (unexplained).

## D7. Negative structural facts
- The Krylov matrix U_{h,i} = (B^i)_{h,0} is not totally positive over Z≥0[q]
  (179/2940 tested minors negative) — naive Cauchy–Binet fails.
- Odd columns Δ_n^{(2k−1)} have no closed monomial form and irregular signs
  (Δ^{(3)}: +,+,−,−,−,+ at n=1..6) — obstructs the Toda route for k ≥ 2.

## D8. Exact verification envelope (no counterexample)
Δ_n^{(2k)} ∈ Z≥0[q] verified exactly: k=1 n≤14 (proved); k=2,3,4 n≤7. Odd r=3,5 fail at n=3.
