# SUMMARY.md — pi-qmotzkin-even-positivity-r1

**Target:** Oh–Scrimshaw arXiv:1805.00113v1, Appendix A, Conjecture A.4 (MathDB 339078):
det[M_{i+j+2k}(q)]_{i,j=0}^{n−1} ∈ Z≥0[q] for all k, n ≥ 1 (coefficientwise), M per the stated recurrence —
or a genuine exact counterexample.

## Result: PARTIAL — k = 1 (shift 2) fully proved (new); k ≥ 2 open; no counterexample found

### 1. The case k = 1 is completely proved (new result)
**Δ_n^{(2)} = q^{β_{n+1}−1}(1+q) + Σ_{2≤j≤n, j≢2 (mod 3)} q^{β_{n+1}−j}** ∈ Z≥0[q],
an explicit sum of ≤ n+1 distinct monomials (β_m = m(m−1)(2m−1)/6).

Proof (PROOF.md §3): Desnanot–Jacobi (2D Toda) identity on the Hankel array
Δ_{n+1}^{(r−1)}Δ_{n−1}^{(r+1)} = Δ_n^{(r−1)}Δ_n^{(r+1)} − (Δ_n^{(r)})², applied at r = 1, using the two
closed-form columns Δ_n^{(0)} = q^{β_n} (A.2/Cigler) and Δ_n^{(1)} = κ_n q^{n(n²−1)/3} (A.3), yields the
first-order recursion Δ_n^{(2)} = q^{n²}Δ_{n−1}^{(2)} + κ_n² q^{n(n−1)(2n+5)/6}; unrolling and the exponent
identity j(j−1)(2j+5)/6 + Σ_{i=j+1}^n i² = β_{n+1} − j give the formula. The source conjectures A.4 for all
k ≥ 1 without proof and states the LGV obstruction — the k = 1 case was open and is settled here.

Exact verification: closed form ≡ direct fraction-free Hankel determinant for n ≤ 14 (toda2.py).

### 2. Structural results (new, all exactly verified)
- **Walk model:** M_n(q) = Σ_{Motzkin walks 0→0, n steps} q^{Σ_{t=1}^{n−1} w_t} (height-sum statistic;
  proved from the recurrence by first-step decomposition). The source's Prop. A.5 uses tunnel length;
  the two statistics are equidistributed. This evades the LGV obstruction the paper describes.
- **J-fraction:** moments of (a_h, b_h) = (q^h, q^{2h+1}); h_n = q^{n²}.
- **Claim R:** Δ_n^{(r)} = q^{β_n}·det[(B^r)_{[0,n)×[0,n)}], B = KD the half-line walk matrix
  (verified r ≤ 7, n ≤ 5) ⟹ A.4 ⇔ det[(B^{2k})_{n×n}] ∈ Z≥0[q].
- **Square identity:** det[(B^{2k})_{n×n}] = q^{binom n 2} Σ_M det[T_{[0,n),M}]² q^{ΣM}, T = B^kD^{−1}.
  For k = 1, T = K has all minors in {0,±1} (interval/biconvex bipartite graph ⟹ TU) — an independent
  proof of the k = 1 case. For k ≥ 2 the T-minors have mixed signs (first: k = 2, n = 3, M = (0,1,3))
  and positivity holds only via cross-term cancellation — the precise open core.

### 3. Status of k ≥ 2
- Exact positivity verified for k = 2, 3, 4 through n = 7 (and k = 1 through n = 14).
- Toda route to Δ^{(4)} needs the odd column Δ^{(3)}, which has no closed form
  (signs +,+,−,−,−,+ for n = 1..6; Δ_2^{(3)} = q⁷(2q+1), Δ_3^{(3)} = −q^{14}(q⁶+2q³+2q²+1), …).
- Odd shifts r = 3, 5 go negative at n = 3 (exact), matching the source.

### 4. Prior art (checked 2026-10-25, primary fetches)
- MathDB 339078: open, 0 solutions, no progress summary (direct page fetch).
- No resolution in Cigler 2204.09910 / 2309.15557, Chen–Shi 2608.27208 (constant-parameter Catalan-like
  families only), or Krattenthaler–Cigler path-determinant work. First-batch record covers MathDB 339076
  (different problem; does not exclude A.4).

### 5. Deliverables
PROOF.md (full mathematics + proofs + prior art), toda.py/toda2.py/gencheck.py (+ compute.py,
reduce.py, wstudy.py, tp_test.py, tfact.py), lean/AxiomFreeMotzkin.lean + lean/BRIDGE.md + pins
(Lean 4.34.1 / mathlib d13f23b723b8a846827a245b89c10fc7d3f11612; layer 1 sorry-free, compiler-unverified
— no Lean toolchain in sandbox), discovery.md, progress.md, provenance.json.

### 6. Falsifier
`python3 compute.py`-style exact Bareiss determinant: any negative coefficient of Δ_n^{(2k)} refutes A.4.
None found; every even shift tested is positive-coefficient.
