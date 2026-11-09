import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
/-!
# Polynexus: the exact ordered-pair count, MathDB 352496

Source semantics (Fikioris--Fikioris, *A subsemigroup of the rook monoid*,
Sections 3-4, 8): the nonzero matrices of `M_n` are exactly the blocks with
ones `x[i,j] = 1` iff `k <= i <= m` and `j = i + d`; 0-based this is: rows
`a..a+e`, columns `b..b+e`, with `a+e+1 <= n` and `b+e+1 <= n`.
Multiplication is ordinary matrix multiplication.

Part 1: the actual matrix model and the algebraic bridge (the product of
two blocks is nonzero iff the column interval of the first meets the row
interval of the second).
-/
set_option linter.unusedVariables false

/-- The matrix type: `Fin n → Fin n → ℕ`, entries in `Nat`. -/
def pxMat (n : ℕ) := Fin n → Fin n → ℕ

/-- The zero matrix. -/
def pxZero (n : ℕ) : pxMat n := fun _ _ => 0

/-- The block with rows `a..a+e` and columns `b..b+e`; length `e+1 ≥ 1`. -/
def pxBlk (n a b e : ℕ) : pxMat n := fun i j =>
  if a ≤ (i : ℕ) ∧ (i : ℕ) ≤ a + e ∧ b ≤ (j : ℕ) ∧ (j : ℕ) ≤ b + e then 1 else 0

/-- Ordinary matrix multiplication: `(AB) i h = ∑ k, A i k * B k h`. -/
def pxMul {n : ℕ} (A B : pxMat n) : pxMat n := fun i h => ∑ k, A i k * B k h

theorem pxBlk_one {n a b e : ℕ} {i j : Fin n}
    (h1 : a ≤ (i : ℕ)) (h2 : (i : ℕ) ≤ a + e) (h3 : b ≤ (j : ℕ)) (h4 : (j : ℕ) ≤ b + e) :
    pxBlk n a b e i j = 1 := by
  simp [pxBlk, h1, h2, h3, h4]

theorem pxBlk_eq {n a b e : ℕ} {i j : Fin n} (h : pxBlk n a b e i j = 1) :
    a ≤ (i : ℕ) ∧ (i : ℕ) ≤ a + e ∧ b ≤ (j : ℕ) ∧ (j : ℕ) ≤ b + e := by
  by_cases hc : a ≤ (i : ℕ) ∧ (i : ℕ) ≤ a + e ∧ b ≤ (j : ℕ) ∧ (j : ℕ) ≤ b + e
  · exact hc
  · exfalso
    have h0 : pxBlk n a b e i j = 0 := by simp [pxBlk, hc]
    omega

/-- Nonzero entry: the index is in the block and the value is `1`. -/
theorem pxBlk_one_of_ne_zero {n a b e : ℕ} {i j : Fin n} (h : pxBlk n a b e i j ≠ 0) :
    a ≤ (i : ℕ) ∧ (i : ℕ) ≤ a + e ∧ b ≤ (j : ℕ) ∧ (j : ℕ) ≤ b + e ∧
      pxBlk n a b e i j = 1 := by
  by_cases hc : a ≤ (i : ℕ) ∧ (i : ℕ) ≤ a + e ∧ b ≤ (j : ℕ) ∧ (j : ℕ) ≤ b + e
  · exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, by simp [pxBlk, hc]⟩
  · exfalso
    have h0 : pxBlk n a b e i j = 0 := by simp [pxBlk, hc]
    omega

/-- Legal triples: the block lies in the `n × n` box. -/
def pxLeg (n : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  Finset.filter
    (fun p : (ℕ × ℕ) × ℕ => p.1.1 + p.2 + 1 ≤ n ∧ p.1.2 + p.2 + 1 ≤ n)
    ((Finset.range n ×ˢ Finset.range n) ×ˢ Finset.range n)

/-- A single nonnegative summand is at most the whole sum. -/
theorem pxSum_ge {n : ℕ} (g : Fin n → ℕ) (k : Fin n) : g k ≤ ∑ i, g i :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)

/-- A single entry of a product is at most the product entry. -/
theorem pxSingleLower {n : ℕ} (X Y : pxMat n) (i j k : Fin n) :
    X i k * Y k j ≤ ∑ t, X i t * Y t j := by
  refine le_trans ?_ (pxSum_ge (fun t => X i t * Y t j) k)
  exact le_rfl

/-- A legal block is not the zero matrix: its `(a, b)` entry is `1`. -/
theorem pxBlk_ne_zero {n a b e : ℕ} (h : a + e + 1 ≤ n) (hb : b + e + 1 ≤ n) :
    (pxBlk n a b e : pxMat n) ≠ pxZero n := by
  intro hz
  have h1 : pxBlk n a b e ⟨a, by omega⟩ ⟨b, by omega⟩ = 1 :=
    pxBlk_one (by omega) (by omega) (by omega) (by omega)
  have h2 := congrFun (congrFun hz ⟨a, by omega⟩) ⟨b, by omega⟩
  rw [h1] at h2
  simp [pxZero] at h2

/-- Blocks are injective on the legal box: row supports `a..a+e` and column
supports `b..b+e` are read off the matrix. -/
theorem pxBlk_inj {n : ℕ} : ∀ ⦃x y : (ℕ × ℕ) × ℕ⦄, x ∈ pxLeg n → y ∈ pxLeg n →
    pxBlk n x.1.1 x.1.2 x.2 = pxBlk n y.1.1 y.1.2 y.2 → x = y := by
  rintro ⟨⟨a, b⟩, e⟩ ⟨⟨c, d⟩, f⟩ hx hy hEq
  obtain ⟨ha, hb⟩ := (Finset.mem_filter.1 hx).2
  obtain ⟨hc, hd⟩ := (Finset.mem_filter.1 hy).2
  have hE : ∀ i j : Fin n, pxBlk n a b e i j = pxBlk n c d f i j :=
    fun i j => congrFun hEq i j
  have h1 : pxBlk n c d f ⟨a, by omega⟩ ⟨b, by omega⟩ = 1 := by
    have h := hE ⟨a, by omega⟩ ⟨b, by omega⟩
    rw [pxBlk_one (by omega) (by omega) (by omega) (by omega)] at h
    exact h
  obtain ⟨h11, h12, h13, h14⟩ := pxBlk_eq h1
  have h2 : pxBlk n a b e ⟨c, by omega⟩ ⟨d, by omega⟩ = 1 := by
    have h := hE ⟨c, by omega⟩ ⟨d, by omega⟩
    rw [pxBlk_one (by omega) (by omega) (by omega) (by omega)] at h
    exact h.symm
  obtain ⟨h21, h22, h23, h24⟩ := pxBlk_eq h2
  have hac : a = c := le_antisymm h21 h11
  have h3 : pxBlk n a b e ⟨a, by omega⟩ ⟨d, by omega⟩ = 1 := by
    have h := hE ⟨a, by omega⟩ ⟨d, by omega⟩
    rw [pxBlk_one (by omega) (by omega) (by omega) (by omega)] at h
    exact h.symm
  obtain ⟨_, _, h33, _⟩ := pxBlk_eq h3
  have h4 : pxBlk n a b e ⟨a, by omega⟩ ⟨b + e, by omega⟩ = 1 :=
    pxBlk_one (by omega) (by omega) (by omega) (by omega)
  have h5 : pxBlk n c d f ⟨a, by omega⟩ ⟨b + e, by omega⟩ = 1 := by
    have h := hE ⟨a, by omega⟩ ⟨b + e, by omega⟩
    rw [h4] at h
    exact h.symm
  obtain ⟨_, _, _, h54⟩ := pxBlk_eq h5
  have hbd : b = d := by omega
  have h6 : pxBlk n c d f ⟨a, by omega⟩ ⟨b + f, by omega⟩ = 1 := by
    refine pxBlk_one ?_ ?_ ?_ ?_ <;> omega
  have h7 : pxBlk n a b e ⟨a, by omega⟩ ⟨b + f, by omega⟩ = 1 := by
    have h := hE ⟨a, by omega⟩ ⟨b + f, by omega⟩
    rw [h6] at h
    exact h.symm
  obtain ⟨_, _, _, h74⟩ := pxBlk_eq h7
  have hfe : f = e := by omega
  simp [hac, hbd, hfe]

theorem pxMul_apply {n : ℕ} (A B : pxMat n) (i j : Fin n) :
    pxMul A B i j = ∑ k, A i k * B k j :=
  rfl

/-- The algebraic bridge: for legal blocks, the ordinary product is nonzero
iff the column interval `b..b+e` of the first meets the row interval
`c..c+f` of the second (source Theorem 3, transported). -/
theorem pxMul_ne_zero_iff {n a b e c d f : ℕ}
    (ha : a + e + 1 ≤ n) (hb : b + e + 1 ≤ n) (hc : c + f + 1 ≤ n) (hd : d + f + 1 ≤ n) :
    (pxMul (pxBlk n a b e) (pxBlk n c d f)) ≠ pxZero n ↔ b ≤ c + f ∧ c ≤ b + e := by
  constructor
  · -- a nonzero product has a nonzero entry, whose index lies in both intervals
    intro hprod
    by_contra hcon
    have hdisj : c + f < b ∨ b + e < c := by
      rcases Nat.lt_or_ge (c + f) b with h | h
      · exact Or.inl h
      · refine Or.inr ?_
        have hnc : ¬ (c ≤ b + e) := fun h' => hcon ⟨h, h'⟩
        omega
    have hall : ∀ i j : Fin n, pxMul (pxBlk n a b e) (pxBlk n c d f) i j = 0 := by
      intro i j
      show ∑ k, pxBlk n a b e i k * pxBlk n c d f k j = 0
      apply Finset.sum_eq_zero
      intro k _
      by_cases hX : pxBlk n a b e i k = 0
      · simp [hX]
      · obtain ⟨hi1, hi2, hk1, hk2, hX1⟩ := pxBlk_one_of_ne_zero hX
        by_cases hY : pxBlk n c d f k j = 0
        · simp [hY]
        · obtain ⟨hk1', hk2', hj1, hj2, hY1⟩ := pxBlk_one_of_ne_zero hY
          exfalso
          omega
    exact hprod (funext fun i => funext fun j => hall i j)
  · -- overlapping intervals make the (a, d) entry equal to one
    rintro ⟨hov1, hov2⟩
    have hk : max b c < n := by omega
    have hXk : pxBlk n a b e ⟨a, by omega⟩ ⟨max b c, by omega⟩ = 1 :=
      pxBlk_one (by omega) (by omega) (by omega) (by omega)
    have hYk : pxBlk n c d f ⟨max b c, by omega⟩ ⟨d, by omega⟩ = 1 :=
      pxBlk_one (by omega) (by omega) (by omega) (by omega)
    intro hz
    have hkey : pxBlk n a b e ⟨a, by omega⟩ (⟨max b c, hk⟩ : Fin n) *
        pxBlk n c d f (⟨max b c, hk⟩ : Fin n) ⟨d, by omega⟩ = 1 := by
      rw [hXk, hYk]; ring
    have hbound : pxBlk n a b e ⟨a, by omega⟩ (⟨max b c, hk⟩ : Fin n) *
        pxBlk n c d f (⟨max b c, hk⟩ : Fin n) ⟨d, by omega⟩ ≤
        ∑ t : Fin n, pxBlk n a b e ⟨a, by omega⟩ t * pxBlk n c d f t ⟨d, by omega⟩ :=
      pxSingleLower _ _ _ _ _
    have h0 : (pxMul (pxBlk n a b e) (pxBlk n c d f)) ⟨a, by omega⟩ ⟨d, by omega⟩ = 0 := by
      have h1 := congrFun (congrFun hz ⟨a, by omega⟩) ⟨d, by omega⟩
      rw [h1]; simp [pxZero]
    rw [pxMul_apply] at h0
    omega
