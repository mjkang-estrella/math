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

/-- Unfolded entry at explicit natural indices: no `Fin` cast appears in
any side condition. -/
theorem pxBlk_apply_nat {n a b e i j : ℕ} (hi : i < n) (hj : j < n) :
    pxBlk n a b e (⟨i, hi⟩ : Fin n) (⟨j, hj⟩ : Fin n) =
      if a ≤ i ∧ i ≤ a + e ∧ b ≤ j ∧ j ≤ b + e then 1 else 0 := by
  simp [pxBlk]

/-- Entry `1` at natural indices. -/
theorem pxBlk_one_nat {n a b e i j : ℕ} (hi : i < n) (hj : j < n)
    (h1 : a ≤ i) (h2 : i ≤ a + e) (h3 : b ≤ j) (h4 : j ≤ b + e) :
    pxBlk n a b e (⟨i, hi⟩ : Fin n) (⟨j, hj⟩ : Fin n) = 1 := by
  rw [pxBlk_apply_nat hi hj, if_pos ⟨h1, h2, h3, h4⟩]

/-- The entry condition is necessary for entry `1`, at natural indices. -/
theorem pxBlk_eq_nat {n a b e i j : ℕ} (hi : i < n) (hj : j < n)
    (h : pxBlk n a b e (⟨i, hi⟩ : Fin n) (⟨j, hj⟩ : Fin n) = 1) :
    a ≤ i ∧ i ≤ a + e ∧ b ≤ j ∧ j ≤ b + e := by
  by_cases hc : a ≤ i ∧ i ≤ a + e ∧ b ≤ j ∧ j ≤ b + e
  · exact hc
  · exfalso
    rw [pxBlk_apply_nat hi hj, if_neg hc] at h
    omega

theorem pxZero_apply (n : ℕ) (i j : Fin n) : pxZero n i j = 0 := rfl

/-- A legal block is not the zero matrix: its `(a, b)` entry is `1`. -/
theorem pxBlk_ne_zero {n a b e : ℕ} (h : a + e + 1 ≤ n) (hb : b + e + 1 ≤ n) :
    (pxBlk n a b e : pxMat n) ≠ pxZero n := by
  intro hz
  have hAn : a < n := by omega
  have hBn : b < n := by omega
  have h1 : pxBlk n a b e ⟨a, hAn⟩ ⟨b, hBn⟩ = 1 :=
    pxBlk_one_nat hAn hBn (by omega) (by omega) (by omega) (by omega)
  have h2 := congrFun (congrFun hz ⟨a, hAn⟩) ⟨b, hBn⟩
  rw [h1, pxZero_apply] at h2
  omega

/-- Blocks are injective on the legal box: row supports `a..a+e` and column
supports `b..b+e` are read off the matrix. -/
theorem pxBlk_inj {n : ℕ} : ∀ ⦃x y : (ℕ × ℕ) × ℕ⦄, x ∈ pxLeg n → y ∈ pxLeg n →
    pxBlk n x.1.1 x.1.2 x.2 = pxBlk n y.1.1 y.1.2 y.2 → x = y := by
  rintro ⟨⟨a, b⟩, e⟩ ⟨⟨c, d⟩, f⟩ hx hy hEq
  obtain ⟨ha, hb⟩ := (Finset.mem_filter.1 hx).2
  obtain ⟨hc, hd⟩ := (Finset.mem_filter.1 hy).2
  have hEq' : pxBlk n a b e = pxBlk n c d f := hEq
  have hE : ∀ i j : Fin n, pxBlk n a b e i j = pxBlk n c d f i j :=
    fun i j => congrFun (congrFun hEq' i) j
  have hAn : a < n := by omega
  have hBn : b < n := by omega
  have hCn : c < n := by omega
  have hDn : d < n := by omega
  -- the (a, b) entry of the second block and the (c, d) entry of the first are one
  have yAb : pxBlk n c d f ⟨a, hAn⟩ ⟨b, hBn⟩ = 1 := by
    rw [← hE ⟨a, hAn⟩ ⟨b, hBn⟩]
    exact pxBlk_one_nat hAn hBn (by omega) (by omega) (by omega) (by omega)
  have xCd : pxBlk n a b e ⟨c, hCn⟩ ⟨d, hDn⟩ = 1 := by
    rw [hE ⟨c, hCn⟩ ⟨d, hDn⟩]
    exact pxBlk_one_nat hCn hDn (by omega) (by omega) (by omega) (by omega)
  obtain ⟨h11, h12, h13, h14⟩ := pxBlk_eq_nat hAn hBn yAb
  obtain ⟨h21, h22, h23, h24⟩ := pxBlk_eq_nat hCn hDn xCd
  have hac : a = c := le_antisymm h21 h11
  have hbd : b = d := le_antisymm h23 h13
  -- the row extents agree: the entry one row past each block's rows
  have hAEn : a + e < n := by omega
  have xAEn : pxBlk n a b e ⟨a + e, hAEn⟩ ⟨b, hBn⟩ = 1 :=
    pxBlk_one_nat hAEn hBn (by omega) (by omega) (by omega) (by omega)
  have yAEn : pxBlk n c d f ⟨a + e, hAEn⟩ ⟨b, hBn⟩ = 1 := by
    rw [← hE ⟨a + e, hAEn⟩ ⟨b, hBn⟩]
    exact xAEn
  obtain ⟨_, hAF1, _, _⟩ := pxBlk_eq_nat hAEn hBn yAEn
  -- hAF1 : a + e ≤ c + f
  have hAFn : a + f < n := by omega
  have yAF : pxBlk n c d f ⟨a + f, hAFn⟩ ⟨d, hDn⟩ = 1 :=
    pxBlk_one_nat hAFn hDn (by omega) (by omega) (by omega) (by omega)
  have xAF : pxBlk n a b e ⟨a + f, hAFn⟩ ⟨d, hDn⟩ = 1 := by
    rw [hE ⟨a + f, hAFn⟩ ⟨d, hDn⟩]
    exact yAF
  obtain ⟨_, hAE1, _, _⟩ := pxBlk_eq_nat hAFn hDn xAF
  -- hAE1 : a + f ≤ a + e
  have eLeF : e ≤ f := by omega
  have fLeE : f ≤ e := by omega
  have hfe : f = e := le_antisymm fLeE eLeF
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
  · -- overlapping intervals give a common index with a nonzero product entry
    rintro ⟨hov1, hov2⟩
    have hAn : a < n := by omega
    have hDn : d < n := by omega
    have hKn : max b c < n := by omega
    have hXk : pxBlk n a b e ⟨a, hAn⟩ ⟨max b c, hKn⟩ = 1 :=
      pxBlk_one_nat hAn hKn (by omega) (by omega) (by omega) (by omega)
    have hYk : pxBlk n c d f ⟨max b c, hKn⟩ ⟨d, hDn⟩ = 1 :=
      pxBlk_one_nat hKn hDn (by omega) (by omega) (by omega) (by omega)
    intro hz
    have h0 : ∑ k : Fin n, pxBlk n a b e ⟨a, hAn⟩ k * pxBlk n c d f k ⟨d, hDn⟩ = 0 := by
      have h0' := congrFun (congrFun hz ⟨a, hAn⟩) ⟨d, hDn⟩
      rw [pxMul_apply, pxZero_apply] at h0'
      exact h0'
    have h2 := pxSingleLower (pxBlk n a b e) (pxBlk n c d f) ⟨a, hAn⟩ ⟨d, hDn⟩ ⟨max b c, hKn⟩
    rw [hXk, hYk] at h2
    omega
