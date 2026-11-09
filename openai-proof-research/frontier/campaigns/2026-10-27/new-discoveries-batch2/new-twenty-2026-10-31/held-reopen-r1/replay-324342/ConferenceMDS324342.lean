import Mathlib

/-!
# MathDB 324342: the conference-matrix MDS conjecture is false

Source: T. Etzion, A. Vardy, E. Yaakobi, "Coding for the Lee and Manhattan metrics with weighing
matrices", arXiv:1210.5725 (v1 21 Oct 2012, v2 11 Dec 2012), Conjecture 5 (ISIT 2013 version:
Conjecture 1):

  "If C is a code of length p + 1 constructed from a generator matrix which is a conference matrix
   then C is an MDS code of dimension (p+1)/2 and minimum Hamming distance (p+3)/2."

Source definitions (§I): a weighing matrix `W_{n,w}` of order `n` and weight `w` is an `n × n`
matrix over `{0, 1, -1}` with exactly `w` nonzero entries in each row and in each column and
`W Wᵀ = w I_n`; conference matrices are the weighing matrices with `w = n - 1`.  The code is the
`ℤ_p = 𝔽_p` span of the rows (equivalently, Theorem 1, the reduction mod `p` of the lattice
`Λ(W)` spanned over `ℤ` by the rows; this equivalence is proved below for every `p`, `n`, `W`).
Minimum Hamming distance is the least Hamming distance between two distinct codewords, and an
`[n, k, d]` linear code is MDS when it meets the Singleton bound, `d = n - k + 1`.

We give a skew conference matrix of order 20 whose row code over `ℤ_19` has dimension 10 and
contains a nonzero word of Hamming weight 9 < 11 = (19 + 3) / 2, so it is not MDS.
-/

namespace ConferenceMDS

open Matrix

/-! ## Definitions, stated for arbitrary `n`, `p` -/

/-- Weighing matrix of order `n` and weight `w` (source definition). -/
def IsWeighingMatrix {n : ℕ} (w : ℕ) (W : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∀ i j, W i j = 0 ∨ W i j = 1 ∨ W i j = -1) ∧
  (∀ i, (Finset.univ.filter fun j => W i j ≠ 0).card = w) ∧
  (∀ j, (Finset.univ.filter fun i => W i j ≠ 0).card = w) ∧
  W * Wᵀ = (w : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)

/-- Conference matrix of order `n`: a weighing matrix of weight `n - 1` (source definition). -/
def IsConferenceMatrix {n : ℕ} (W : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  IsWeighingMatrix (n - 1) W

/-- The usual textbook definition of a conference matrix: zero diagonal, `±1` off the diagonal,
`W Wᵀ = (n - 1) I`.  (Not used by the source; refuted as well for robustness.) -/
def IsStdConferenceMatrix {n : ℕ} (W : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∀ i, W i i = 0) ∧ (∀ i j, i ≠ j → W i j = 1 ∨ W i j = -1) ∧
  W * Wᵀ = ((n : ℤ) - 1) • (1 : Matrix (Fin n) (Fin n) ℤ)

/-- Row `i` of `W`, reduced mod `p`. -/
def rowVecs (p : ℕ) {n : ℕ} (W : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : Fin n → ZMod p :=
  fun j => ((W i j : ℤ) : ZMod p)

/-- The linear code over `ℤ_p` with generator matrix `W`: the span of its rows. -/
def rowCode (p : ℕ) {n : ℕ} (W : Matrix (Fin n) (Fin n) ℤ) :
    Submodule (ZMod p) (Fin n → ZMod p) :=
  Submodule.span (ZMod p) (Set.range (rowVecs p W))

/-- The code over `ℤ_p` reduced from the lattice `Λ(W)` (integer row span), as in the source's
Theorem 1: reduce every lattice point coordinatewise mod `p`. -/
def latticeCode (p : ℕ) {n : ℕ} (W : Matrix (Fin n) (Fin n) ℤ) : Set (Fin n → ZMod p) :=
  (fun x : Fin n → ℤ => fun j => ((x j : ℤ) : ZMod p)) ''
    (Submodule.span ℤ (Set.range fun i : Fin n => W i) : Set (Fin n → ℤ))

/-- Minimum Hamming distance: least distance between two distinct codewords (`0` if none). -/
noncomputable def minDistance {p n : ℕ} (C : Submodule (ZMod p) (Fin n → ZMod p)) : ℕ :=
  sInf {d | ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ hammingDist x y = d}

/-- Minimum Hamming weight of a nonzero codeword (`0` if none). -/
noncomputable def minWeight {p n : ℕ} (C : Submodule (ZMod p) (Fin n → ZMod p)) : ℕ :=
  sInf {d | ∃ x ∈ C, x ≠ 0 ∧ hammingNorm x = d}

/-- MDS: the `[n, k, d]` code meets the Singleton bound `d = n - k + 1`. -/
def IsMDS {p n : ℕ} (C : Submodule (ZMod p) (Fin n → ZMod p)) : Prop :=
  minDistance C = n - Module.finrank (ZMod p) C + 1

/-- Conjecture 5 of arXiv:1210.5725, literally (source definition of conference matrix). -/
def Conjecture5 : Prop :=
  ∀ p : ℕ, p.Prime → ∀ W : Matrix (Fin (p + 1)) (Fin (p + 1)) ℤ, IsConferenceMatrix W →
    IsMDS (rowCode p W) ∧ Module.finrank (ZMod p) (rowCode p W) = (p + 1) / 2 ∧
      minDistance (rowCode p W) = (p + 3) / 2

/-- The same statement with the textbook definition of conference matrix. -/
def Conjecture5Std : Prop :=
  ∀ p : ℕ, p.Prime → ∀ W : Matrix (Fin (p + 1)) (Fin (p + 1)) ℤ, IsStdConferenceMatrix W →
    IsMDS (rowCode p W) ∧ Module.finrank (ZMod p) (rowCode p W) = (p + 1) / 2 ∧
      minDistance (rowCode p W) = (p + 3) / 2

/-! ## Bridge: the lattice-reduced code is the `ℤ_p` row span (all `p`, `n`, `W`) -/

theorem latticeCode_eq_rowCode (p : ℕ) {n : ℕ} (W : Matrix (Fin n) (Fin n) ℤ) :
    latticeCode p W = (rowCode p W : Set (Fin n → ZMod p)) := by
  let π : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ZMod p) :=
    LinearMap.compLeft (Int.castRingHom (ZMod p)).toAddMonoidHom.toIntLinearMap (Fin n)
  have himg : π '' Set.range (fun i : Fin n => W i) = Set.range (rowVecs p W) := by
    rw [← Set.range_comp]
    rfl
  have hsur : Function.Surjective (algebraMap ℤ (ZMod p)) := fun x =>
    ⟨x.cast, by simp⟩
  have h1 : latticeCode p W =
      ((Submodule.span ℤ (Set.range fun i : Fin n => W i)).map π : Set (Fin n → ZMod p)) := by
    rw [Submodule.map_coe]
    rfl
  rw [h1, Submodule.map_span, himg, rowCode, ← Submodule.restrictScalars_span ℤ (ZMod p) hsur,
    Submodule.coe_restrictScalars]

/-! ## The order-20 matrix -/

def Wrows : List (List ℤ) := [
    [0, 1, 1, -1, -1, -1, 1, 1, 1, 1, -1, 1, 1, 1, 1, -1, 1, -1, 1, 1],
    [-1, 0, 1, 1, -1, 1, 1, 1, 1, -1, 1, 1, 1, 1, -1, 1, -1, 1, 1, -1],
    [-1, -1, 0, 1, 1, 1, 1, 1, -1, 1, 1, 1, 1, -1, 1, -1, 1, 1, -1, 1],
    [1, -1, -1, 0, 1, 1, 1, -1, 1, 1, 1, 1, -1, 1, 1, 1, 1, -1, 1, -1],
    [1, 1, -1, -1, 0, 1, -1, 1, 1, 1, 1, -1, 1, 1, 1, 1, -1, 1, -1, 1],
    [1, -1, -1, -1, -1, 0, 1, 1, -1, -1, 1, -1, 1, -1, 1, -1, -1, -1, 1, -1],
    [-1, -1, -1, -1, 1, -1, 0, 1, 1, -1, -1, 1, -1, 1, 1, -1, -1, 1, -1, -1],
    [-1, -1, -1, 1, -1, -1, -1, 0, 1, 1, 1, -1, 1, 1, -1, -1, 1, -1, -1, -1],
    [-1, -1, 1, -1, -1, 1, -1, -1, 0, 1, -1, 1, 1, -1, 1, 1, -1, -1, -1, -1],
    [-1, 1, -1, -1, -1, 1, 1, -1, -1, 0, 1, 1, -1, 1, -1, -1, -1, -1, -1, 1],
    [1, -1, -1, -1, -1, -1, 1, -1, 1, -1, 0, 1, 1, -1, -1, 1, 1, 1, -1, 1],
    [-1, -1, -1, -1, 1, 1, -1, 1, -1, -1, -1, 0, 1, 1, -1, 1, 1, -1, 1, 1],
    [-1, -1, -1, 1, -1, -1, 1, -1, -1, 1, -1, -1, 0, 1, 1, 1, -1, 1, 1, 1],
    [-1, -1, 1, -1, -1, 1, -1, -1, 1, -1, 1, -1, -1, 0, 1, -1, 1, 1, 1, 1],
    [-1, 1, -1, -1, -1, -1, -1, 1, -1, 1, 1, 1, -1, -1, 0, 1, 1, 1, 1, -1],
    [1, -1, 1, -1, -1, 1, 1, 1, -1, 1, -1, -1, -1, 1, -1, 0, 1, 1, -1, -1],
    [-1, 1, -1, -1, 1, 1, 1, -1, 1, 1, -1, -1, 1, -1, -1, -1, 0, 1, 1, -1],
    [1, -1, -1, 1, -1, 1, -1, 1, 1, 1, -1, 1, -1, -1, -1, -1, -1, 0, 1, 1],
    [-1, -1, 1, -1, 1, -1, 1, 1, 1, 1, 1, -1, -1, -1, -1, 1, -1, -1, 0, 1],
    [-1, 1, -1, 1, -1, 1, 1, 1, 1, -1, -1, -1, -1, -1, 1, 1, 1, -1, -1, 0]]

def W20 : Matrix (Fin 20) (Fin 20) ℤ := fun i j => (Wrows.getD i.1 []).getD j.1 0

theorem W20_entries : ∀ i j, W20 i j = 0 ∨ W20 i j = 1 ∨ W20 i j = -1 := by
  have h : ∀ q : Fin 20 × Fin 20, W20 q.1 q.2 = 0 ∨ W20 q.1 q.2 = 1 ∨ W20 q.1 q.2 = -1 := by
    decide +kernel
  exact fun i j => h (i, j)

theorem W20_rows : ∀ i, (Finset.univ.filter fun j => W20 i j ≠ 0).card = 20 - 1 := by
  decide +kernel

theorem W20_cols : ∀ j, (Finset.univ.filter fun i => W20 i j ≠ 0).card = 20 - 1 := by
  decide +kernel

theorem W20_gram_entries :
    ∀ q : Fin 20 × Fin 20, (W20 * W20ᵀ) q.1 q.2 = if q.1 = q.2 then 19 else 0 := by
  decide +kernel

theorem W20_gram : W20 * W20ᵀ = ((20 - 1 : ℕ) : ℤ) • (1 : Matrix (Fin 20) (Fin 20) ℤ) := by
  ext i j
  have h := W20_gram_entries (i, j)
  simp only at h
  rw [h, Matrix.smul_apply, Matrix.one_apply]
  split_ifs <;> norm_num

theorem W20_conference : IsConferenceMatrix W20 :=
  ⟨W20_entries, W20_rows, W20_cols, W20_gram⟩

theorem W20_std_conference : IsStdConferenceMatrix W20 := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · have h : ∀ q : Fin 20 × Fin 20, q.1 ≠ q.2 → W20 q.1 q.2 = 1 ∨ W20 q.1 q.2 = -1 := by
      decide +kernel
    exact fun i j hij => h (i, j) hij
  · rw [show ((20 : ℕ) : ℤ) - 1 = ((20 - 1 : ℕ) : ℤ) by norm_num]
    exact W20_gram

theorem W20_skew : W20ᵀ = -W20 := by
  have h : ∀ q : Fin 20 × Fin 20, W20 q.2 q.1 = -W20 q.1 q.2 := by decide +kernel
  ext i j
  exact h (i, j)

/-! ## A codeword of Hamming weight 9 -/

def coeff : Fin 20 → ZMod 19 := fun i =>
  ([5, 7, 13, 9, 0, 15, 14, 2, 8, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List (ZMod 19)).getD i.1 0

def word : Fin 20 → ZMod 19 := fun j =>
  ([0, 0, 0, 0, 0, 15, 0, 0, 10, 1, 18, 0, 9, 0, 18, 14, 5, 15, 0, 0] : List (ZMod 19)).getD j.1 0

theorem word_eq_comb : word = ∑ i : Fin 20, coeff i • rowVecs 19 W20 i := by
  have h : ∀ j : Fin 20, word j = ∑ i : Fin 20, coeff i * rowVecs 19 W20 i j := by
    decide +kernel
  funext j
  rw [Finset.sum_apply, h j]
  rfl

theorem word_mem : word ∈ rowCode 19 W20 := by
  rw [word_eq_comb]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem word_ne_zero : word ≠ 0 := by
  intro h
  have h9 := congrFun h 9
  revert h9
  decide +kernel

theorem word_weight : hammingNorm word = 9 := by
  decide +kernel

theorem minDistance_le : minDistance (rowCode 19 W20) ≤ 9 := by
  apply Nat.sInf_le
  exact ⟨word, word_mem, 0, Submodule.zero_mem _, word_ne_zero,
    by rw [hammingDist_zero_right, word_weight]⟩

theorem minWeight_le : minWeight (rowCode 19 W20) ≤ 9 :=
  Nat.sInf_le ⟨word, word_mem, word_ne_zero, word_weight⟩

/-! ## The row code has dimension exactly 10 -/

instance fact_prime_19 : Fact (Nat.Prime 19) := ⟨by norm_num⟩

def basisVec (t : Fin 10) : Fin 20 → ZMod 19 := rowVecs 19 W20 (Fin.castLE (by norm_num) t)

def Am : Matrix (Fin 10) (Fin 10) (ZMod 19) := fun t s => basisVec t (Fin.castLE (by norm_num) s)

def Blist : List (List (ZMod 19)) := [
    [0, 4, 3, 16, 15, 1, 5, 7, 7, 5],
    [15, 0, 4, 3, 16, 5, 7, 7, 5, 1],
    [16, 15, 0, 4, 3, 7, 7, 5, 1, 5],
    [3, 16, 15, 0, 4, 7, 5, 1, 5, 7],
    [4, 3, 16, 15, 0, 5, 1, 5, 7, 7],
    [18, 14, 12, 12, 14, 0, 4, 3, 16, 15],
    [14, 12, 12, 14, 18, 15, 0, 4, 3, 16],
    [12, 12, 14, 18, 14, 16, 15, 0, 4, 3],
    [12, 14, 18, 14, 12, 3, 16, 15, 0, 4],
    [14, 18, 14, 12, 12, 4, 3, 16, 15, 0]]

def Bm : Matrix (Fin 10) (Fin 10) (ZMod 19) := fun i j => (Blist.getD i.1 []).getD j.1 0

def Dlist : List (List (ZMod 19)) := [
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    [1, 9, 15, 18, 1, 13, 17, 8, 14, 6],
    [17, 7, 14, 1, 5, 17, 15, 10, 10, 6],
    [11, 3, 12, 1, 17, 8, 10, 17, 2, 2],
    [3, 16, 9, 9, 7, 14, 10, 2, 9, 4],
    [12, 9, 13, 15, 14, 6, 6, 2, 4, 2],
    [2, 4, 2, 6, 6, 4, 5, 7, 10, 6],
    [8, 14, 6, 13, 17, 1, 18, 18, 10, 4],
    [10, 10, 6, 17, 15, 18, 14, 2, 12, 5],
    [17, 2, 2, 8, 10, 18, 2, 8, 16, 7],
    [2, 9, 4, 14, 10, 10, 12, 16, 3, 10]]

def Dm : Fin 20 → Fin 10 → ZMod 19 := fun r t => (Dlist.getD r.1 []).getD t.1 0

theorem Am_mul_Bm : Am * Bm = 1 := by
  have h : ∀ q : Fin 10 × Fin 10, (Am * Bm) q.1 q.2 = if q.1 = q.2 then 1 else 0 := by
    decide +kernel
  ext i j
  rw [h (i, j), one_apply]

theorem Bm_mul_Am : Bm * Am = 1 := by
  have h : ∀ q : Fin 10 × Fin 10, (Bm * Am) q.1 q.2 = if q.1 = q.2 then 1 else 0 := by
    decide +kernel
  ext i j
  rw [h (i, j), one_apply]

theorem Am_isUnit : IsUnit Am := ⟨⟨Am, Bm, Am_mul_Bm, Bm_mul_Am⟩, rfl⟩

def proj : (Fin 20 → ZMod 19) →ₗ[ZMod 19] (Fin 10 → ZMod 19) :=
  LinearMap.funLeft (ZMod 19) (ZMod 19) (Fin.castLE (by norm_num))

theorem basisVec_linearIndependent : LinearIndependent (ZMod 19) basisVec :=
  LinearIndependent.of_comp proj (Matrix.linearIndependent_rows_of_isUnit Am_isUnit)

theorem rowVecs_comb : ∀ r : Fin 20, rowVecs 19 W20 r = ∑ t : Fin 10, Dm r t • basisVec t := by
  have h : ∀ q : Fin 20 × Fin 20,
      rowVecs 19 W20 q.1 q.2 = ∑ t : Fin 10, Dm q.1 t * basisVec t q.2 := by
    decide +kernel
  intro r
  funext j
  rw [Finset.sum_apply]
  exact h (r, j)

theorem rowCode_eq_span : rowCode 19 W20 = Submodule.span (ZMod 19) (Set.range basisVec) := by
  apply le_antisymm
  · rw [rowCode, Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    rw [rowVecs_comb r]
    exact Submodule.sum_mem _ fun t _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    exact Submodule.subset_span ⟨Fin.castLE (by norm_num) t, rfl⟩

theorem finrank_rowCode : Module.finrank (ZMod 19) (rowCode 19 W20) = 10 := by
  rw [rowCode_eq_span, finrank_span_eq_card basisVec_linearIndependent]
  simp

/-! ## Main results -/

theorem not_isMDS : ¬ IsMDS (rowCode 19 W20) := by
  unfold IsMDS
  rw [finrank_rowCode]
  have := minDistance_le
  omega

/-- The counterexample in full: a conference matrix (source and textbook definitions, skew) of
order `19 + 1` whose `ℤ_19` row code (equal to the code reduced from the lattice `Λ(W20)`) has
dimension `(19+1)/2 = 10` but minimum distance at most `9 < (19+3)/2 = 11`; it is not MDS. -/
theorem counterexample :
    Nat.Prime 19 ∧ IsConferenceMatrix W20 ∧ IsStdConferenceMatrix W20 ∧ W20ᵀ = -W20 ∧
      latticeCode 19 W20 = (rowCode 19 W20 : Set (Fin 20 → ZMod 19)) ∧
      Module.finrank (ZMod 19) (rowCode 19 W20) = (19 + 1) / 2 ∧
      minDistance (rowCode 19 W20) ≤ 9 ∧ minWeight (rowCode 19 W20) ≤ 9 ∧
      minDistance (rowCode 19 W20) < (19 + 3) / 2 ∧ ¬ IsMDS (rowCode 19 W20) :=
  ⟨by norm_num, W20_conference, W20_std_conference, W20_skew, latticeCode_eq_rowCode 19 W20,
    finrank_rowCode, minDistance_le, minWeight_le, by have := minDistance_le; omega, not_isMDS⟩

/-- MathDB 324342 / arXiv:1210.5725 Conjecture 5 is false. -/
theorem conjecture5_false : ¬ Conjecture5 := fun h =>
  not_isMDS (h 19 (by norm_num) W20 W20_conference).1

/-- Even the bare MDS claim fails. -/
theorem mds_claim_false :
    ¬ ∀ p : ℕ, p.Prime → ∀ W : Matrix (Fin (p + 1)) (Fin (p + 1)) ℤ, IsConferenceMatrix W →
      IsMDS (rowCode p W) := fun h =>
  not_isMDS (h 19 (by norm_num) W20 W20_conference)

/-- Even the bare minimum-distance claim fails. -/
theorem distance_claim_false :
    ¬ ∀ p : ℕ, p.Prime → ∀ W : Matrix (Fin (p + 1)) (Fin (p + 1)) ℤ, IsConferenceMatrix W →
      minDistance (rowCode p W) = (p + 3) / 2 := fun h => by
  have h1 := h 19 (by norm_num) W20 W20_conference
  have h2 := minDistance_le
  omega

/-- Variant reading with minimum distance taken as least nonzero weight: also false. -/
theorem conjecture5_minWeight_false :
    ¬ ∀ p : ℕ, p.Prime → ∀ W : Matrix (Fin (p + 1)) (Fin (p + 1)) ℤ, IsConferenceMatrix W →
      minWeight (rowCode p W) = (p + 1) - Module.finrank (ZMod p) (rowCode p W) + 1 := fun h => by
  have h1 := h 19 (by norm_num) W20 W20_conference
  rw [finrank_rowCode] at h1
  have h2 := minWeight_le
  omega

/-- The textbook-definition reading is false too. -/
theorem conjecture5Std_false : ¬ Conjecture5Std := fun h =>
  not_isMDS (h 19 (by norm_num) W20 W20_std_conference).1

end ConferenceMDS
