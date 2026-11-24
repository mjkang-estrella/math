# Lean source appendix (MathDB 366504)

Modules in import order, byte-identical to `src/`. Lean 4.34.1, Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 (see PINS.json).

### `TPDefs.lean`

```lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Transposed Poisson n-Lie algebras and the derivation construction (MathDB 366504)

Literal transcription of the definitions of

* F. Mashurov, *On the transposed Poisson n-Lie algebras*, arXiv:2501.01714,
  Definition 2.1 (n-Lie algebra), Definition 2.4 (transposed Poisson n-Lie algebra),
  Conjecture 1.1 (the derivation construction, with the sign `(-1)^(i-1)`);
* C. Bai, R. Bai, L. Guo, Y. Wu, arXiv:2005.01110, Definition 4.8 and Conjecture 4.9;
* J. Huang, X. Chen, Z. Chen, M. Ding, arXiv:2312.04010, Definition 3.1 (derivation).

Indexing convention: the source indexes arguments `1, …, n`; Lean indexes them by `Fin n`,
i.e. `0, …, n-1`.  Source index `i` is Lean index `i - 1`, so the source sign `(-1)^(i-1)`
becomes `(-1)^(i : ℕ)` for `i : Fin (n+1)`.
-/

namespace TP366504

open Finset

section Defs

variable (K : Type*) [CommRing K] {L : Type*} [AddCommGroup L] [Module K L]

/-- The tuple `(z, y₂, …, yₙ)` of Mashurov's identity (1): position `0` holds `z`, and
position `j ≥ 1` holds the `j`-th entry of `y = (y₂, …, yₙ) : Fin (n - 1) → L`
(Lean index `j - 1`). -/
def headTail {n : ℕ} (z : L) (y : Fin (n - 1) → L) : Fin n → L :=
  fun j => if h : (j : ℕ) = 0 then z else y ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩

/-- **n-Lie algebra** (Mashurov, Def. 2.1; Filippov): an `n`-ary skew-symmetric (multilinear)
bracket `[·, …, ·] : L × ⋯ × L → L` such that for all `x₁, …, xₙ, y₂, …, yₙ`
`[[x₁, …, xₙ], y₂, …, yₙ] = ∑ᵢ [x₁, …, xᵢ₋₁, [xᵢ, y₂, …, yₙ], xᵢ₊₁, …, xₙ]`. -/
structure IsNLie (n : ℕ) (br : (Fin n → L) → L) : Prop where
  /-- the bracket is `K`-linear in each argument -/
  multilinear : ∀ (x : Fin n → L) (i : Fin n) (c : K) (u v : L),
    br (Function.update x i (c • u + v)) =
      c • br (Function.update x i u) + br (Function.update x i v)
  /-- skew-symmetry: exchanging two arguments changes the sign -/
  skew : ∀ (x : Fin n → L) (i j : Fin n), i ≠ j → br (x ∘ Equiv.swap i j) = -br x
  /-- the generalized Jacobi (Filippov) identity, Mashurov (1) -/
  jacobi : ∀ (x : Fin n → L) (y : Fin (n - 1) → L),
    br (headTail (br x) y) = ∑ i, br (Function.update x i (br (headTail (x i) y)))

/-- **Transposed Poisson n-Lie algebra** (Mashurov, Def. 2.4 = Bai–Bai–Guo–Wu, Def. 4.8):
`(L, ·)` is a commutative associative algebra (no unit required), `(L, [·, …, ·])` is an
`n`-Lie algebra, and the Leibniz rule `n h [a₁, …, aₙ] = ∑ᵢ [a₁, …, h aᵢ, …, aₙ]` holds. -/
structure IsTPnLie (n : ℕ) (mul : L →ₗ[K] L →ₗ[K] L) (br : (Fin n → L) → L) : Prop where
  comm : ∀ x y : L, mul x y = mul y x
  assoc : ∀ x y z : L, mul (mul x y) z = mul x (mul y z)
  nLie : IsNLie K n br
  leibniz : ∀ (h : L) (a : Fin n → L),
    (n : K) • mul h (br a) = ∑ i, br (Function.update a i (mul h (a i)))

/-- **Derivation** of `(L, ·)` and of `(L, [·, …, ·])` (Huang–Chen–Chen–Ding, Def. 3.1):
`D(uv) = D(u)v + uD(v)` and `D[x₁, …, xₙ] = ∑ᵢ [x₁, …, D(xᵢ), …, xₙ]`. -/
structure IsDerivation {n : ℕ} (mul : L →ₗ[K] L →ₗ[K] L) (br : (Fin n → L) → L)
    (D : L →ₗ[K] L) : Prop where
  mul_rule : ∀ u v : L, D (mul u v) = mul (D u) v + mul u (D v)
  br_rule : ∀ x : Fin n → L, D (br x) = ∑ i, br (Function.update x i (D (x i)))

/-- The `(n+1)`-ary operation of Mashurov's Conjecture 1.1:
`μ(a₁, …, aₙ₊₁) = ∑ᵢ (-1)^(i-1) D(aᵢ) [a₁, …, âᵢ, …, aₙ₊₁]`.
Here `a ∘ i.succAbove` is the `n`-tuple obtained from `a` by omitting the `i`-th entry. -/
def mu {n : ℕ} (mul : L →ₗ[K] L →ₗ[K] L) (br : (Fin n → L) → L) (D : L →ₗ[K] L) :
    (Fin (n + 1) → L) → L :=
  fun a => ∑ i : Fin (n + 1), ((-1 : K) ^ (i : ℕ)) • mul (D (a i)) (br (a ∘ i.succAbove))

/-- The operation exactly as printed in Bai–Bai–Guo–Wu, Conjecture 4.9 (no sign):
`μₙ₊₁(x₁, …, xₙ₊₁) = ∑ᵢ D(xᵢ) μₙ(x₁, …, x̌ᵢ, …, xₙ₊₁)`. -/
def muUnsigned {n : ℕ} (mul : L →ₗ[K] L →ₗ[K] L) (br : (Fin n → L) → L) (D : L →ₗ[K] L) :
    (Fin (n + 1) → L) → L :=
  fun a => ∑ i : Fin (n + 1), mul (D (a i)) (br (a ∘ i.succAbove))

end Defs

/-- **Derivation construction conjecture** (Mashurov, Conjecture 1.1; MathDB 366504), over a
field `K`: for every `n ≥ 2`, every transposed Poisson `n`-Lie algebra `(L, ·, [·, …, ·])` and
every derivation `D` of `(L, ·)` and `(L, [·, …, ·])`, the triple `(L, ·, μ)` is a transposed
Poisson `(n+1)`-Lie algebra. -/
def DerivationConstructionConjecture (K : Type) [Field K] : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ (L : Type) [AddCommGroup L] [Module K L]
    (mul : L →ₗ[K] L →ₗ[K] L) (br : (Fin n → L) → L), IsTPnLie K n mul br →
    ∀ D : L →ₗ[K] L, IsDerivation K mul br D → IsTPnLie K (n + 1) mul (mu K mul br D)

/-- The same statement with the operation exactly as printed in Bai–Bai–Guo–Wu,
Conjecture 4.9 (without the sign `(-1)^(i-1)`). -/
def DerivationConstructionConjectureUnsigned (K : Type) [Field K] : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ (L : Type) [AddCommGroup L] [Module K L]
    (mul : L →ₗ[K] L →ₗ[K] L) (br : (Fin n → L) → L), IsTPnLie K n mul br →
    ∀ D : L →ₗ[K] L, IsDerivation K mul br D → IsTPnLie K (n + 1) mul (muUnsigned K mul br D)

/-! ### Unfolding lemmas that display the indexing (fidelity checks) -/

section Unfold

variable {K : Type*} [CommRing K] {L : Type*} [AddCommGroup L] [Module K L]

omit [AddCommGroup L] in
theorem headTail_three (z : L) (y : Fin 2 → L) : headTail (n := 3) z y = ![z, y 0, y 1] := by
  funext j; fin_cases j <;> rfl

omit [AddCommGroup L] in
theorem headTail_four (z : L) (y : Fin 3 → L) :
    headTail (n := 4) z y = ![z, y 0, y 1, y 2] := by
  funext j; fin_cases j <;> rfl

/-- Mashurov's identity (1) for `n = 3`, written out. -/
theorem jacobi_three_iff (br : (Fin 3 → L) → L) :
    (∀ (x : Fin 3 → L) (y : Fin (3 - 1) → L),
      br (headTail (br x) y) = ∑ i, br (Function.update x i (br (headTail (x i) y)))) ↔
    ∀ x₁ x₂ x₃ y₂ y₃ : L,
      br ![br ![x₁, x₂, x₃], y₂, y₃] =
        br ![br ![x₁, y₂, y₃], x₂, x₃] + br ![x₁, br ![x₂, y₂, y₃], x₃] +
          br ![x₁, x₂, br ![x₃, y₂, y₃]] := by
  have hu : ∀ (x : Fin 3 → L) (i : Fin 3) (w : L),
      Function.update x i w = ![if i = 0 then w else x 0, if i = 1 then w else x 1,
        if i = 2 then w else x 2] := by
    intro x i w; funext j; fin_cases i <;> fin_cases j <;> rfl
  constructor
  · intro h x₁ x₂ x₃ y₂ y₃
    have := h ![x₁, x₂, x₃] ![y₂, y₃]
    simpa [headTail_three, Fin.sum_univ_three, hu] using this
  · intro h x y
    have hx : x = ![x 0, x 1, x 2] := by funext j; fin_cases j <;> rfl
    rw [Fin.sum_univ_three, headTail_three, headTail_three, headTail_three, headTail_three,
      hu, hu, hu]
    conv_lhs => rw [hx]
    simpa using h (x 0) (x 1) (x 2) (y 0) (y 1)

/-- Mashurov's identity (1) for `n = 4`, written out. -/
theorem jacobi_four_iff (br : (Fin 4 → L) → L) :
    (∀ (x : Fin 4 → L) (y : Fin (4 - 1) → L),
      br (headTail (br x) y) = ∑ i, br (Function.update x i (br (headTail (x i) y)))) ↔
    ∀ x₁ x₂ x₃ x₄ y₂ y₃ y₄ : L,
      br ![br ![x₁, x₂, x₃, x₄], y₂, y₃, y₄] =
        br ![br ![x₁, y₂, y₃, y₄], x₂, x₃, x₄] + br ![x₁, br ![x₂, y₂, y₃, y₄], x₃, x₄] +
          br ![x₁, x₂, br ![x₃, y₂, y₃, y₄], x₄] + br ![x₁, x₂, x₃, br ![x₄, y₂, y₃, y₄]] := by
  have hu : ∀ (x : Fin 4 → L) (i : Fin 4) (w : L),
      Function.update x i w = ![if i = 0 then w else x 0, if i = 1 then w else x 1,
        if i = 2 then w else x 2, if i = 3 then w else x 3] := by
    intro x i w; funext j; fin_cases i <;> fin_cases j <;> rfl
  constructor
  · intro h x₁ x₂ x₃ x₄ y₂ y₃ y₄
    have := h ![x₁, x₂, x₃, x₄] ![y₂, y₃, y₄]
    simpa [headTail_four, Fin.sum_univ_four, hu] using this
  · intro h x y
    have hx : x = ![x 0, x 1, x 2, x 3] := by funext j; fin_cases j <;> rfl
    rw [Fin.sum_univ_four, headTail_four, headTail_four, headTail_four, headTail_four,
      headTail_four, hu, hu, hu, hu]
    conv_lhs => rw [hx]
    simpa using h (x 0) (x 1) (x 2) (x 3) (y 0) (y 1) (y 2)

/-- The operation `μ` for `n = 3`, written out:
`μ(a₁,a₂,a₃,a₄) = D(a₁)[a₂,a₃,a₄] - D(a₂)[a₁,a₃,a₄] + D(a₃)[a₁,a₂,a₄] - D(a₄)[a₁,a₂,a₃]`. -/
theorem mu_three_apply (mul : L →ₗ[K] L →ₗ[K] L) (br : (Fin 3 → L) → L) (D : L →ₗ[K] L)
    (a : Fin 4 → L) :
    mu K mul br D a =
      mul (D (a 0)) (br ![a 1, a 2, a 3]) - mul (D (a 1)) (br ![a 0, a 2, a 3]) +
        mul (D (a 2)) (br ![a 0, a 1, a 3]) - mul (D (a 3)) (br ![a 0, a 1, a 2]) := by
  have h0 : a ∘ (0 : Fin 4).succAbove = ![a 1, a 2, a 3] := by
    funext j; fin_cases j <;> rfl
  have h1 : a ∘ (1 : Fin 4).succAbove = ![a 0, a 2, a 3] := by
    funext j; fin_cases j <;> rfl
  have h2 : a ∘ (2 : Fin 4).succAbove = ![a 0, a 1, a 3] := by
    funext j; fin_cases j <;> rfl
  have h3 : a ∘ (3 : Fin 4).succAbove = ![a 0, a 1, a 2] := by
    funext j; fin_cases j <;> rfl
  show ∑ i : Fin 4, ((-1 : K) ^ (i : ℕ)) • mul (D (a i)) (br (a ∘ i.succAbove)) = _
  rw [Fin.sum_univ_four, h0, h1, h2, h3]
  norm_num [sub_eq_add_neg, neg_smul]

/-- The unsigned operation for `n = 3`, written out. -/
theorem muUnsigned_three_apply (mul : L →ₗ[K] L →ₗ[K] L) (br : (Fin 3 → L) → L)
    (D : L →ₗ[K] L) (a : Fin 4 → L) :
    muUnsigned K mul br D a =
      mul (D (a 0)) (br ![a 1, a 2, a 3]) + mul (D (a 1)) (br ![a 0, a 2, a 3]) +
        mul (D (a 2)) (br ![a 0, a 1, a 3]) + mul (D (a 3)) (br ![a 0, a 1, a 2]) := by
  have h0 : a ∘ (0 : Fin 4).succAbove = ![a 1, a 2, a 3] := by
    funext j; fin_cases j <;> rfl
  have h1 : a ∘ (1 : Fin 4).succAbove = ![a 0, a 2, a 3] := by
    funext j; fin_cases j <;> rfl
  have h2 : a ∘ (2 : Fin 4).succAbove = ![a 0, a 1, a 3] := by
    funext j; fin_cases j <;> rfl
  have h3 : a ∘ (3 : Fin 4).succAbove = ![a 0, a 1, a 2] := by
    funext j; fin_cases j <;> rfl
  show ∑ i : Fin 4, mul (D (a i)) (br (a ∘ i.succAbove)) = _
  rw [Fin.sum_univ_four, h0, h1, h2, h3]

end Unfold

end TP366504
```

### `TPM3.lean`

```lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Module.Pi

/-!
# The 15-dimensional transposed Poisson 3-Lie algebra `M₃` over an arbitrary commutative ring

`M₃` is the algebra of Proposition 3 of the proof (lane t1-pool096-proof-opus55-20261120-r1,
table `out/M3int.json`).  An element is a coordinate vector `Fin 15 → R` in the basis
`f₀, …, f₁₄`.  The definitions below were generated from the integer table by
`scripts/gen_m3.py`; every defining identity is a polynomial identity in the coordinates, proved by `ring`
over an arbitrary commutative ring `R`.
-/

namespace TP366504

variable {R : Type*} [CommRing R]

/-- The `3 × 3` minor of the `3 × 15` matrix with rows `u, v, w` on the columns `i, j, k`. -/
def det3 (u v w : Fin 15 → R) (i j k : Fin 15) : R :=
  u i * (v j * w k - v k * w j) - u j * (v i * w k - v k * w i) + u k * (v i * w j - v j * w i)

/-- The commutative product of `M₃` (coordinates in the basis `f₀, …, f₁₄`). -/
def mulR (u v : Fin 15 → R) : Fin 15 → R :=
  ![0,
    0,
    (u 0 * v 1 + u 1 * v 0),
    0,
    (u 1 * v 3 + u 3 * v 1),
    0,
    -(u 1 * v 5 + u 5 * v 1),
    (u 3 * v 3),
    (u 3 * v 5 + u 5 * v 3),
    0,
    0,
    0,
    (u 1 * v 11 + u 11 * v 1) - (u 3 * v 9 + u 9 * v 3),
    0,
    (u 1 * v 13 + u 13 * v 1) - (u 3 * v 10 + u 10 * v 3) - (u 5 * v 9 + u 9 * v 5)]

/-- The ternary bracket of `M₃`: `[u, v, w] = ∑ c_{ijk}^o det(u,v,w; i,j,k) f_o`. -/
def brR (u v w : Fin 15 → R) : Fin 15 → R :=
  ![0,
    0,
    0,
    0,
    0,
    -det3 u v w 0 1 3,
    -(3 * det3 u v w 1 2 3),
    0,
    -(3 * det3 u v w 0 1 7),
    -det3 u v w 1 3 4,
    -det3 u v w 0 1 9 + det3 u v w 1 3 6 + det3 u v w 1 4 5,
    -det3 u v w 1 3 7,
    -(3 * det3 u v w 1 4 7),
    -(4 * det3 u v w 0 1 11) - det3 u v w 1 3 8 - det3 u v w 1 5 7,
    -(3 * det3 u v w 0 1 12) + 9 * det3 u v w 1 2 11 - (3 * det3 u v w 1 4 8) + 3 * det3 u v w 1 6 7]

theorem mulR_comm (u v : Fin 15 → R) : mulR u v = mulR v u := by
  funext o; fin_cases o <;> simp [mulR] <;> ring

theorem mulR_assoc (u v w : Fin 15 → R) : mulR (mulR u v) w = mulR u (mulR v w) := by
  funext o; fin_cases o <;> simp [mulR]

theorem mulR_left (r : R) (u u' v : Fin 15 → R) :
    mulR (r • u + u') v = r • mulR u v + mulR u' v := by
  funext o; fin_cases o <;> simp [mulR] <;> ring

theorem mulR_right (r : R) (u v v' : Fin 15 → R) :
    mulR u (r • v + v') = r • mulR u v + mulR u v' := by
  funext o; fin_cases o <;> simp [mulR] <;> ring

theorem brR_first (r : R) (u u' v w : Fin 15 → R) :
    brR (r • u + u') v w = r • brR u v w + brR u' v w := by
  funext o; fin_cases o <;> simp [brR, det3] <;> ring

theorem brR_second (r : R) (u v v' w : Fin 15 → R) :
    brR u (r • v + v') w = r • brR u v w + brR u v' w := by
  funext o; fin_cases o <;> simp [brR, det3] <;> ring

theorem brR_third (r : R) (u v w w' : Fin 15 → R) :
    brR u v (r • w + w') = r • brR u v w + brR u v w' := by
  funext o; fin_cases o <;> simp [brR, det3] <;> ring

theorem mulR_zero_left (v : Fin 15 → R) : mulR 0 v = 0 := by
  funext o; fin_cases o <;> simp [mulR]

theorem mulR_zero_right (u : Fin 15 → R) : mulR u 0 = 0 := by
  funext o; fin_cases o <;> simp [mulR]

theorem brR_zero_first (v w : Fin 15 → R) : brR 0 v w = 0 := by
  funext o; fin_cases o <;> simp [brR, det3]

theorem brR_zero_second (u w : Fin 15 → R) : brR u 0 w = 0 := by
  funext o; fin_cases o <;> simp [brR, det3]

theorem brR_zero_third (u v : Fin 15 → R) : brR u v 0 = 0 := by
  funext o; fin_cases o <;> simp [brR, det3]

theorem brR_swap12 (u v w : Fin 15 → R) : brR v u w = -brR u v w := by
  funext o; fin_cases o <;> simp [brR, det3] <;> ring

theorem brR_swap13 (u v w : Fin 15 → R) : brR w v u = -brR u v w := by
  funext o; fin_cases o <;> simp [brR, det3] <;> ring

theorem brR_swap23 (u v w : Fin 15 → R) : brR u w v = -brR u v w := by
  funext o; fin_cases o <;> simp [brR, det3] <;> ring

/-- The transposed Poisson Leibniz rule with `n = 3`. -/
theorem brR_leibniz (h u v w : Fin 15 → R) :
    (3 : R) • mulR h (brR u v w) = brR (mulR h u) v w + brR u (mulR h v) w + brR u v (mulR h w) := by
  funext o; fin_cases o <;> simp [mulR, brR, det3] <;> ring

end TP366504
```

### `TPM3Jacobi.lean`

```lean
import TPM3

/-!
# The Filippov identity of `M₃`

`[[a, b, c], d, e] = [[a, d, e], b, c] + [a, [b, d, e], c] + [a, b, [c, d, e]]`,
a polynomial identity in the `5 × 15` coordinates, proved by `ring` over an arbitrary
commutative ring.
-/

namespace TP366504

variable {R : Type*} [CommRing R]

theorem brR_jacobi (a b c d e : Fin 15 → R) :
    brR (brR a b c) d e = brR (brR a d e) b c + brR a (brR b d e) c + brR a b (brR c d e) := by
  funext o; fin_cases o <;> simp [brR, det3] <;> ring

end TP366504
```

### `TPWitness.lean`

```lean
import TPDefs
import TPM3Jacobi
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.BilinearMap

/-!
# The witness `L = M₃ ⊗ K[t]` with `D = d/dt`

For a commutative ring `K`, the `K`-module `L = Fin 15 → K[t]` carries the product `mulL` and the
ternary bracket `brL` of `M₃`, extended `K[t]`-multilinearly, and the derivation `Dl`, the
coordinatewise formal derivative `d/dt`.  We prove that `(L, mulL, brL)` is a transposed Poisson
3-Lie algebra over `K` (`witness_isTP`) and that `Dl` is a derivation of both operations
(`witness_isDerivation`), in the sense of the definitions of `TPDefs`.
-/

namespace TP366504

open Polynomial

variable (K : Type*) [CommRing K]

theorem smul_eq_C_smul (c : K) (u : Fin 15 → K[X]) : c • u = (C c) • u := by
  funext j; simp [smul_eq_C_mul]

/-- The product of `L = M₃ ⊗ K[t]`, a `K`-bilinear map. -/
noncomputable def mulL : (Fin 15 → K[X]) →ₗ[K] (Fin 15 → K[X]) →ₗ[K] (Fin 15 → K[X]) :=
  LinearMap.mk₂ K mulR
    (fun u u' v => by simpa using mulR_left (1 : K[X]) u u' v)
    (fun c u v => by
      simpa [smul_eq_C_smul, mulR_zero_left] using mulR_left (C c) u 0 v)
    (fun u v v' => by simpa using mulR_right (1 : K[X]) u v v')
    (fun c u v => by
      simpa [smul_eq_C_smul, mulR_zero_right] using mulR_right (C c) u v 0)

/-- The ternary bracket of `L = M₃ ⊗ K[t]`. -/
noncomputable def brL : (Fin 3 → (Fin 15 → K[X])) → (Fin 15 → K[X]) :=
  fun x => brR (x 0) (x 1) (x 2)

/-- The derivation `D = d/dt` of `L = M₃ ⊗ K[t]`, applied coordinatewise. -/
noncomputable def Dl : (Fin 15 → K[X]) →ₗ[K] (Fin 15 → K[X]) where
  toFun v := fun j => derivative (v j)
  map_add' u v := by funext j; simp
  map_smul' c v := by funext j; simp

variable {K}

theorem mulL_apply (u v : Fin 15 → K[X]) : mulL K u v = mulR u v := rfl

theorem brL_vec (u v w : Fin 15 → K[X]) : brL K ![u, v, w] = brR u v w := rfl

theorem Dl_apply (v : Fin 15 → K[X]) (j : Fin 15) : Dl K v j = derivative (v j) := rfl

theorem brL_update0 (x : Fin 3 → (Fin 15 → K[X])) (w : Fin 15 → K[X]) :
    brL K (Function.update x 0 w) = brR w (x 1) (x 2) := rfl

theorem brL_update1 (x : Fin 3 → (Fin 15 → K[X])) (w : Fin 15 → K[X]) :
    brL K (Function.update x 1 w) = brR (x 0) w (x 2) := rfl

theorem brL_update2 (x : Fin 3 → (Fin 15 → K[X])) (w : Fin 15 → K[X]) :
    brL K (Function.update x 2 w) = brR (x 0) (x 1) w := rfl

theorem brR_first' (c : K) (u u' v w : Fin 15 → K[X]) :
    brR (c • u + u') v w = c • brR u v w + brR u' v w := by
  rw [smul_eq_C_smul, smul_eq_C_smul, brR_first]

theorem brR_second' (c : K) (u v v' w : Fin 15 → K[X]) :
    brR u (c • v + v') w = c • brR u v w + brR u v' w := by
  rw [smul_eq_C_smul, smul_eq_C_smul, brR_second]

theorem brR_third' (c : K) (u v w w' : Fin 15 → K[X]) :
    brR u v (c • w + w') = c • brR u v w + brR u v w' := by
  rw [smul_eq_C_smul, smul_eq_C_smul, brR_third]

/-- `(L, mulL, brL)` is an `n`-Lie algebra for `n = 3` (Mashurov, Def. 2.1). -/
theorem witness_isNLie : IsNLie K 3 (brL K) where
  multilinear x i c u v := by
    fin_cases i
    · exact brR_first' c u v (x 1) (x 2)
    · exact brR_second' c (x 0) u v (x 2)
    · exact brR_third' c (x 0) (x 1) u v
  skew x i j hij := by
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact brR_swap12 (x 0) (x 1) (x 2)
    · exact brR_swap13 (x 0) (x 1) (x 2)
    · exact brR_swap12 (x 0) (x 1) (x 2)
    · exact absurd rfl hij
    · exact brR_swap23 (x 0) (x 1) (x 2)
    · exact brR_swap13 (x 0) (x 1) (x 2)
    · exact brR_swap23 (x 0) (x 1) (x 2)
    · exact absurd rfl hij
  jacobi := (jacobi_three_iff (brL K)).2 (fun a b c d e => brR_jacobi a b c d e)

/-- `(L, mulL, brL)` is a transposed Poisson 3-Lie algebra (Mashurov, Def. 2.4). -/
theorem witness_isTP : IsTPnLie K 3 (mulL K) (brL K) where
  comm x y := mulR_comm x y
  assoc x y z := mulR_assoc x y z
  nLie := witness_isNLie
  leibniz h a := by
    rw [Fin.sum_univ_three, brL_update0, brL_update1, brL_update2]
    simp only [mulL_apply]
    rw [smul_eq_C_smul]
    have h3 : (C ((3 : ℕ) : K) : K[X]) = 3 := by rw [C_eq_natCast]; norm_num
    rw [h3]
    exact brR_leibniz h (a 0) (a 1) (a 2)

theorem derivative_mulR (u v : Fin 15 → K[X]) :
    (fun j => derivative (mulR u v j)) =
      mulR (fun j => derivative (u j)) v + mulR u (fun j => derivative (v j)) := by
  funext o
  fin_cases o <;> simp [mulR, derivative_mul] <;> ring

theorem derivative_brR (u v w : Fin 15 → K[X]) :
    (fun j => derivative (brR u v w j)) =
      brR (fun j => derivative (u j)) v w + brR u (fun j => derivative (v j)) w +
        brR u v (fun j => derivative (w j)) := by
  funext o
  fin_cases o <;> simp [brR, det3, derivative_mul] <;> ring

/-- `D = d/dt` is a derivation of `(L, mulL)` and of `(L, brL)` (Huang et al., Def. 3.1). -/
theorem witness_isDerivation : IsDerivation K (mulL K) (brL K) (Dl K) where
  mul_rule u v := derivative_mulR u v
  br_rule x := by
    rw [Fin.sum_univ_three, brL_update0, brL_update1, brL_update2]
    exact derivative_brR (x 0) (x 1) (x 2)

end TP366504
```

### `TPEval.lean`

```lean
import TPWitness

/-!
# Evaluation of `μ` at the witness points (MathDB 366504)

Values of the product, the bracket and `D` on the basis vectors that occur, and the ten values
of `μ` needed for the Filippov defect.  The text below describes the whole argument.

In `L = M₃ ⊗ K[t]` with `D = d/dt` the test vectors are `a = f₃`, `b = f₁`, `c = f₀`,
`a t = f₃ ⊗ t` and `b t = f₁ ⊗ t`.
-/

namespace TP366504

open Polynomial

noncomputable section

variable {K : Type*} [CommRing K]

/-- `a = f₃`. -/
def ea : Fin 15 → K[X] := Pi.single 3 1
/-- `b = f₁`. -/
def eb : Fin 15 → K[X] := Pi.single 1 1
/-- `c = f₀`. -/
def ec : Fin 15 → K[X] := Pi.single 0 1
/-- `a t = f₃ ⊗ t`. -/
def eat : Fin 15 → K[X] := Pi.single 3 X
/-- `b t = f₁ ⊗ t`. -/
def ebt : Fin 15 → K[X] := Pi.single 1 X

variable (K) in
/-- The operation `μ` of the conjecture on the witness. -/
abbrev muW : (Fin (3 + 1) → (Fin 15 → K[X])) → (Fin 15 → K[X]) :=
  mu K (mulL K) (brL K) (Dl K)

variable (K) in
/-- The unsigned operation of Bai–Bai–Guo–Wu on the witness. -/
abbrev muUW : (Fin (3 + 1) → (Fin 15 → K[X])) → (Fin 15 → K[X]) :=
  muUnsigned K (mulL K) (brL K) (Dl K)

/-- `μ` on the witness, written out with the bracket and product of `M₃`. -/
theorem muW_apply (x₁ x₂ x₃ x₄ : Fin 15 → K[X]) :
    muW K ![x₁, x₂, x₃, x₄] =
      mulR (Dl K x₁) (brR x₂ x₃ x₄) - mulR (Dl K x₂) (brR x₁ x₃ x₄) +
        mulR (Dl K x₃) (brR x₁ x₂ x₄) - mulR (Dl K x₄) (brR x₁ x₂ x₃) := by
  rw [muW, mu_three_apply]; rfl

/-- The unsigned operation on the witness, written out. -/
theorem muUW_apply (x₁ x₂ x₃ x₄ : Fin 15 → K[X]) :
    muUW K ![x₁, x₂, x₃, x₄] =
      mulR (Dl K x₁) (brR x₂ x₃ x₄) + mulR (Dl K x₂) (brR x₁ x₃ x₄) +
        mulR (Dl K x₃) (brR x₁ x₂ x₄) + mulR (Dl K x₄) (brR x₁ x₂ x₃) := by
  rw [muUW, muUnsigned_three_apply]; rfl

/-! ### `D` on the basis vectors -/

theorem Dl_single_one (i : Fin 15) : Dl K (Pi.single i 1) = 0 := by
  funext j; by_cases h : j = i
  · subst h; simp [Dl_apply]
  · simp [Dl_apply, h]

theorem Dl_single_X (i : Fin 15) : Dl K (Pi.single i X) = Pi.single i 1 := by
  funext j; by_cases h : j = i
  · subst h; simp [Dl_apply]
  · simp [Dl_apply, h]

theorem Dl_ea : Dl K (ea (K := K)) = 0 := Dl_single_one 3
theorem Dl_eb : Dl K (eb (K := K)) = 0 := Dl_single_one 1
theorem Dl_ec : Dl K (ec (K := K)) = 0 := Dl_single_one 0
theorem Dl_eat : Dl K (eat (K := K)) = ea := Dl_single_X 3
theorem Dl_ebt : Dl K (ebt (K := K)) = eb := Dl_single_X 1
theorem Dl_f8 : Dl K (Pi.single 8 1 : Fin 15 → K[X]) = 0 := Dl_single_one 8
theorem Dl_f6 : Dl K (Pi.single 6 1 : Fin 15 → K[X]) = 0 := Dl_single_one 6
theorem Dl_zero : Dl K (0 : Fin 15 → K[X]) = 0 := map_zero _

/-! ### Brackets and products of basis vectors -/

/-- Evaluate one bracket or product of explicit sparse vectors coordinatewise. -/
macro "eval_basis" : tactic =>
  `(tactic| (funext o; fin_cases o <;>
    simp [mulR, brR, det3, Pi.single_apply, ea, eb, ec, eat, ebt]))

/-- `[a, b, c] = [f₃, f₁, f₀] = f₅`. -/
theorem br_abc : brR (ea (K := K)) eb ec = Pi.single 5 1 := by eval_basis
/-- `[f₈, a, b] = f₁₃`. -/
theorem br_f8ab : brR (Pi.single 8 1 : Fin 15 → K[X]) ea eb = Pi.single 13 1 := by eval_basis
theorem br_aab : brR (ea (K := K)) ea eb = 0 := by eval_basis
theorem br_bab : brR (eb (K := K)) ea eb = 0 := by eval_basis
theorem br_atab : brR (eat (K := K)) ea eb = 0 := by eval_basis
theorem br_btab : brR (ebt (K := K)) ea eb = 0 := by eval_basis
/-- `[c, a, b] = [f₀, f₃, f₁] = f₅`. -/
theorem br_cab : brR (ec (K := K)) ea eb = Pi.single 5 1 := by eval_basis
/-- `[a, b, f₆] = -f₁₀`. -/
theorem br_abf6 : brR (ea (K := K)) eb (Pi.single 6 1) = -Pi.single 10 1 := by eval_basis
/-- `[c, b, a] = -f₅`. -/
theorem br_cba : brR (ec (K := K)) eb ea = -Pi.single 5 1 := by eval_basis

/-- `a · f₅ = f₈`. -/
theorem mul_af5 : mulR (ea (K := K)) (Pi.single 5 1) = Pi.single 8 1 := by eval_basis
/-- `b · f₁₃ = f₁₄`. -/
theorem mul_bf13 : mulR (eb (K := K)) (Pi.single 13 1) = Pi.single 14 1 := by eval_basis
/-- `b · f₅ = -f₆`. -/
theorem mul_bf5 : mulR (eb (K := K)) (Pi.single 5 1) = -Pi.single 6 1 := by eval_basis
/-- `a · (-f₁₀) = f₁₄`. -/
theorem mul_anf10 : mulR (ea (K := K)) (-Pi.single 10 1) = Pi.single 14 1 := by eval_basis
/-- `b · (-f₅) = f₆`. -/
theorem mul_bnf5 : mulR (eb (K := K)) (-Pi.single 5 1) = Pi.single 6 1 := by eval_basis

/-! ### The ten values of `μ` -/

/-- Rewrite with the basis values, then clean up the zero terms. -/
macro "eval_mu" : tactic =>
  `(tactic| (rw [muW_apply]; simp only [Dl_ea, Dl_eb, Dl_ec, Dl_eat, Dl_ebt, Dl_f8, Dl_f6, Dl_zero,
    mulR_zero_left, br_abc, br_f8ab, br_aab, br_bab, br_atab, br_btab, br_cab, br_abf6,
    mul_af5, mul_bf13, mul_bf5, mul_anf10, mulR_zero_right, brR_zero_first, brR_zero_second,
    brR_zero_third, sub_zero, zero_sub, add_zero, zero_add, neg_neg, neg_zero]))

theorem mu_x : muW K ![ea, eb, eat, ec] = Pi.single 8 1 := by eval_mu
theorem mu_lhs : muW K ![Pi.single 8 1, ebt, ea, eb] = -Pi.single 14 1 := by eval_mu
theorem mu_r0 : muW K ![ea, ebt, ea, eb] = 0 := by eval_mu
theorem mu_r1 : muW K ![eb, ebt, ea, eb] = 0 := by eval_mu
theorem mu_r2 : muW K ![eat, ebt, ea, eb] = 0 := by eval_mu
theorem mu_r3 : muW K ![ec, ebt, ea, eb] = Pi.single 6 1 := by eval_mu
theorem mu_s0 : muW K ![0, eb, eat, ec] = 0 := by eval_mu
theorem mu_s1 : muW K ![ea, 0, eat, ec] = 0 := by eval_mu
theorem mu_s2 : muW K ![ea, eb, 0, ec] = 0 := by eval_mu
theorem mu_s3 : muW K ![ea, eb, eat, Pi.single 6 1] = Pi.single 14 1 := by eval_mu

/-! ### The unsigned operation -/

theorem muU_x : muUW K ![ec, ebt, eb, ea] = Pi.single 6 1 := by
  rw [muUW_apply]; simp only [Dl_ea, Dl_eb, Dl_ec, Dl_ebt, mulR_zero_left, br_cba, mul_bnf5,
    add_zero, zero_add]

theorem muU_swap : muUW K ![ebt, ec, eb, ea] = Pi.single 6 1 := by
  rw [muUW_apply]; simp only [Dl_ea, Dl_eb, Dl_ec, Dl_ebt, mulR_zero_left, br_cba, mul_bnf5,
    add_zero]

end

end TP366504
```

### `TPCounterexample.lean`

```lean
import TPEval
import Mathlib.Algebra.Field.Rat
import Mathlib.Basic.Complex.Basic

/-!
# The derivation construction conjecture is false (MathDB 366504)

In `L = M₃ ⊗ K[t]` with `D = d/dt` put `a = f₃`, `b = f₁`, `c = f₀`.  At
`x = (a, b, a t, c)`, `y = (b t, a, b)` the operation `μ` of Mashurov's Conjecture 1.1 has
4-ary Filippov defect `-2 f₁₄ ≠ 0` (`filippov_defect`).  Hence `(L, ·, μ)` is not a
`4`-Lie algebra, although `(L, ·, [·,·,·])` is a transposed Poisson 3-Lie algebra and `D` is a
derivation of both operations.  The main endpoint is `not_derivationConstructionConjecture`
(any field of characteristic zero), with the cases `ℚ` and `ℂ` stated separately.
The unsigned operation printed in Bai–Bai–Guo–Wu, Conjecture 4.9, fails already to be
skew-symmetric on the same algebra (`not_derivationConstructionConjectureUnsigned`).
-/

namespace TP366504

open Polynomial

noncomputable section

variable {K : Type*} [CommRing K]

/-- **The Filippov defect.** At `x = (a, b, a t, c)` and `y = (b t, a, b)`,
`μ(μ(x₁,x₂,x₃,x₄), y₂,y₃,y₄) - ∑ᵢ μ(x₁, …, μ(xᵢ,y₂,y₃,y₄), …, x₄) = -2 f₁₄`. -/
theorem filippov_defect :
    muW K ![muW K ![ea, eb, eat, ec], ebt, ea, eb] -
      (muW K ![muW K ![ea, ebt, ea, eb], eb, eat, ec] +
        muW K ![ea, muW K ![eb, ebt, ea, eb], eat, ec] +
        muW K ![ea, eb, muW K ![eat, ebt, ea, eb], ec] +
        muW K ![ea, eb, eat, muW K ![ec, ebt, ea, eb]]) = Pi.single 14 (-2) := by
  rw [mu_x, mu_lhs, mu_r0, mu_r1, mu_r2, mu_r3, mu_s0, mu_s1, mu_s2, mu_s3]
  funext o
  by_cases h : o = 14
  · subst h; simp; norm_num
  · simp [h]

/-- The defect is nonzero: its coordinate `14` is `-2`. -/
theorem filippov_defect_ne_zero [CharZero K] :
    muW K ![muW K ![ea, eb, eat, ec], ebt, ea, eb] -
      (muW K ![muW K ![ea, ebt, ea, eb], eb, eat, ec] +
        muW K ![ea, muW K ![eb, ebt, ea, eb], eat, ec] +
        muW K ![ea, eb, muW K ![eat, ebt, ea, eb], ec] +
        muW K ![ea, eb, eat, muW K ![ec, ebt, ea, eb]]) ≠ 0 := by
  rw [filippov_defect]
  intro h
  have := congrFun h 14
  simp at this

/-- `μ` on the witness is not a 4-Lie algebra: Mashurov's identity (1) fails for `n = 4`. -/
theorem mu_not_jacobi [CharZero K] :
    ¬ ∀ (x : Fin (3 + 1) → (Fin 15 → K[X])) (y : Fin (3 + 1 - 1) → (Fin 15 → K[X])),
      muW K (headTail (muW K x) y) =
        ∑ i, muW K (Function.update x i (muW K (headTail (x i) y))) := by
  intro h
  have hj := (jacobi_four_iff (muW K)).1 h ea eb eat ec ebt ea eb
  exact filippov_defect_ne_zero (sub_eq_zero.2 hj)

/-- **Main theorem (MathDB 366504).** Over every field of characteristic zero the derivation
construction conjecture (Mashurov, Conjecture 1.1) is false: it fails for `n = 3`. -/
theorem not_derivationConstructionConjecture (K : Type) [Field K] [CharZero K] :
    ¬ DerivationConstructionConjecture K := by
  intro h
  have hTP := h 3 (by norm_num) (Fin 15 → K[X]) (mulL K) (brL K) witness_isTP (Dl K)
    witness_isDerivation
  exact mu_not_jacobi hTP.nLie.jacobi

/-- The case `K = ℚ`. -/
theorem mathdb366504_rat : ¬ DerivationConstructionConjecture ℚ :=
  not_derivationConstructionConjecture ℚ

/-- The case `K = ℂ` (Mashurov works over `ℂ`). -/
theorem mathdb366504_complex : ¬ DerivationConstructionConjecture ℂ :=
  not_derivationConstructionConjecture ℂ

/-! ### The operation as printed in Bai–Bai–Guo–Wu (no sign) -/

/-- The unsigned operation is not skew-symmetric on the witness:
`μ'(b t, c, b, a) = μ'(c, b t, b, a) = f₆ ≠ 0`. -/
theorem muU_not_skew [CharZero K] :
    ¬ ∀ (x : Fin (3 + 1) → (Fin 15 → K[X])) (i j : Fin (3 + 1)), i ≠ j →
      muUW K (x ∘ Equiv.swap i j) = -muUW K x := by
  intro h
  have hs := h ![ec, ebt, eb, ea] 0 1 (by decide)
  have hx : (![ec, ebt, eb, ea] : Fin (3 + 1) → (Fin 15 → K[X])) ∘ Equiv.swap 0 1 =
      ![ebt, ec, eb, ea] := by
    funext j; fin_cases j <;> rfl
  rw [hx, muU_x, muU_swap] at hs
  have := congrFun hs 6
  simp at this
  norm_num at this

/-- The statement with the unsigned operation printed in Bai–Bai–Guo–Wu, Conjecture 4.9, is
also false over every field of characteristic zero. -/
theorem not_derivationConstructionConjectureUnsigned (K : Type) [Field K] [CharZero K] :
    ¬ DerivationConstructionConjectureUnsigned K := by
  intro h
  have hTP := h 3 (by norm_num) (Fin 15 → K[X]) (mulL K) (brL K) witness_isTP (Dl K)
    witness_isDerivation
  exact muU_not_skew hTP.nLie.skew

end

end TP366504

/-! ### Endpoint statements, definitions and their dependencies -/

#print TP366504.DerivationConstructionConjecture
#print TP366504.DerivationConstructionConjectureUnsigned
#print TP366504.IsTPnLie
#print TP366504.IsNLie
#print TP366504.IsDerivation
#print TP366504.mu
#print TP366504.muUnsigned
#print TP366504.headTail
#check @TP366504.not_derivationConstructionConjecture
#check @TP366504.mathdb366504_rat
#check @TP366504.mathdb366504_complex
#check @TP366504.not_derivationConstructionConjectureUnsigned
#check @TP366504.witness_isTP
#check @TP366504.witness_isDerivation
#check @TP366504.filippov_defect
#check @TP366504.filippov_defect_ne_zero
#check @TP366504.jacobi_three_iff
#check @TP366504.jacobi_four_iff
#check @TP366504.mu_three_apply
#print axioms TP366504.not_derivationConstructionConjecture
#print axioms TP366504.mathdb366504_rat
#print axioms TP366504.mathdb366504_complex
#print axioms TP366504.not_derivationConstructionConjectureUnsigned
#print axioms TP366504.witness_isTP
#print axioms TP366504.witness_isDerivation
#print axioms TP366504.filippov_defect
#print axioms TP366504.filippov_defect_ne_zero
#print axioms TP366504.jacobi_three_iff
#print axioms TP366504.jacobi_four_iff
#print axioms TP366504.mu_three_apply
```

