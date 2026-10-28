# Lean bridge — pinned toolchain and roadmap

**Pins (per batch AGENTS.md):**
- Lean toolchain: `leanprover/lean4:v4.34.1` (see `lean-toolchain`)
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612` (see `lakefile.toml` `require` revision)

**Sandbox note:** no elan/lake in this environment; `AxiomFreeMotzkin.lean` is written dependency-free
(bare Lean 4) and must be compiled with the pinned toolchain before being trusted. No `sorry`/`axiom`
anywhere; unproven targets are *not stated as theorems* — they live in this roadmap.

## Layer 1 (this file, done)
`M : Nat → Poly` (List Nat, little-endian) with the exact recurrence
`M (n+1) = M n + Σ_{r<n} q^{r+1}·M r·M (n-1-r)`; sanity `M 0 = 1, M 1 = 1, M 2 = 1+q` by `rfl`.
Representation gives M_n ∈ Z≥0[q].

## Layer 2 — Claim R (next)
Statement to formalize (mathlib):
```
theorem claim_R (r n : ℕ) :
    hankelDet (fun i j => M (r + i + j)) n
      = smul (q^(Σ_{i<n} i^2)) (det (Matrix.blockOf B r r n n))
```
Ingredients: exact polynomial `Ring` on ℤ-coefficient lists (or `Polynomial ℤ`), the walk matrix
`B h h' = q^h' * (if |h-h'| ≤ 1 then 1 else 0)`, Cauchy–Binet (`Matrix.det_mul_blockDiagonal` /
`Matrix.cauchy_binet`-style lemmas), and the time-expanded-graph (meander) LGV argument for the
Krylov minors `det[(B^i)_{h,0}]_S`.

## Layer 3 — Theorem A (k = 1 case)
```
theorem shift2_monomials (n : ℕ) :
    hankelDet (fun i j => M (2 + i + j)) n
      = Σ_{j ∈ [2,n], j % 3 ≠ 2} q^(β(n+1) - j) + q^(β(n+1)-1) * (1 + q)
```
Ingredients: Desnanot–Jacobi (`Matrix.eq_zero_of_... `/ direct Sylvester lemma, mathlib
`Matrix.det_update...`; may need a hand proof), A.2 (Δ_n^{(0)} = q^{β_n}, via product of OP norms
or Claim R), A.3 (Δ_n^{(1)} = κ_n q^{n(n²−1)/3}, via the tridiagonal recursion
d_n = q^{n−1}d_{n−1} − q^{2n−3}d_{n−2} and Claim R), then the induction of PROOF.md §3.

## Layer 4 — falsifier harness
A `#eval`-free exact checker: `NegativeCoeff (hankelDet (2*k) n) : Prop` decidable over ℤ-coefficient
Hankel determinants, to certify any candidate counterexample found by the Python search.
