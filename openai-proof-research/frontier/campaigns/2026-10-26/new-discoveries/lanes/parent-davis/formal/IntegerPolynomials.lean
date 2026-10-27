import Mathlib

namespace Davis

def coeffAdd : List ℤ → List ℤ → List ℤ
  | [], b => b
  | a, [] => a
  | a :: as, b :: bs => (a + b) :: coeffAdd as bs

def coeffScale (c : ℤ) (a : List ℤ) : List ℤ := a.map (c * ·)

def coeffMul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: as, b => coeffAdd (coeffScale a b) (0 :: coeffMul as b)

noncomputable def coeffEval : List ℤ → ℝ → ℝ
  | [], _ => 0
  | a :: as, x => a + x * coeffEval as x

theorem coeffEval_add (a b : List ℤ) (x : ℝ) :
    coeffEval (coeffAdd a b) x = coeffEval a x + coeffEval b x := by
  induction a generalizing b with
  | nil => simp [coeffAdd, coeffEval]
  | cons c cs ih =>
    cases b with
    | nil => simp [coeffAdd, coeffEval]
    | cons e es => simp only [coeffAdd, coeffEval, Int.cast_add, ih]; ring

theorem coeffEval_scale (c : ℤ) (a : List ℤ) (x : ℝ) :
    coeffEval (coeffScale c a) x = c * coeffEval a x := by
  induction a with
  | nil => simp [coeffScale, coeffEval]
  | cons b bs ih =>
    simp only [coeffScale, List.map_cons, coeffEval, Int.cast_mul] at ⊢
    change (c : ℝ) * b + x * coeffEval (coeffScale c bs) x = _
    rw [ih]
    ring

theorem coeffEval_mul (a b : List ℤ) (x : ℝ) :
    coeffEval (coeffMul a b) x = coeffEval a x * coeffEval b x := by
  induction a with
  | nil => simp [coeffMul, coeffEval]
  | cons c cs ih =>
    simp only [coeffMul, coeffEval_add, coeffEval_scale, coeffEval, Int.cast_zero, zero_add, ih]
    ring

theorem coeffEval_nonneg {a : List ℤ} {x : ℝ} (ha : ∀ c ∈ a, 0 ≤ c) (hx : 0 ≤ x) :
    0 ≤ coeffEval a x := by
  induction a with
  | nil => simp [coeffEval]
  | cons c cs ih =>
    have hc : 0 ≤ c := ha c (by simp)
    have hcs : ∀ z ∈ cs, 0 ≤ z := by intro z hz; exact ha z (by simp [hz])
    change 0 ≤ (c : ℝ) + x * coeffEval cs x
    exact add_nonneg (by exact_mod_cast hc) (mul_nonneg hx (ih hcs))

theorem coeffEval_pos {c : ℤ} {cs : List ℤ} {x : ℝ}
    (hc : 0 < c) (hcs : ∀ z ∈ cs, 0 ≤ z) (hx : 0 ≤ x) :
    0 < coeffEval (c :: cs) x := by
  change 0 < (c : ℝ) + x * coeffEval cs x
  exact add_pos_of_pos_of_nonneg (by exact_mod_cast hc)
    (mul_nonneg hx (coeffEval_nonneg hcs hx))

def coeffTranslate : List ℤ → ℤ → ℤ → List ℤ
  | [], _, _ => []
  | [c], _, _ => [c]
  | c :: b :: bs, m, q =>
      coeffAdd [c * q ^ (bs.length + 1)] (coeffMul [m, q] (coeffTranslate (b :: bs) m q))

theorem coeffEval_translate (a : List ℤ) (m q : ℤ) (hq : q ≠ 0) (x : ℝ) :
    coeffEval (coeffTranslate a m q) x =
      (q : ℝ) ^ (a.length - 1) * coeffEval a (x + (m : ℝ) / q) := by
  induction a with
  | nil => simp [coeffTranslate, coeffEval]
  | cons c cs ih =>
    cases cs with
    | nil => simp [coeffTranslate, coeffEval]
    | cons b bs =>
      have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq
      simp only [coeffTranslate, coeffEval_add, coeffEval_mul, coeffEval,
        Int.cast_mul, Int.cast_pow, mul_zero, add_zero, List.length_cons,
        Nat.add_sub_cancel] at ⊢
      rw [ih]
      simp only [List.length_cons, Nat.add_sub_cancel, coeffEval]
      rw [pow_succ]
      field_simp
      ring

def coeffRangeSum : ℕ → (ℕ → List ℤ) → List ℤ
  | 0, _ => []
  | n + 1, f => coeffAdd (coeffRangeSum n f) (f n)

theorem coeffEval_rangeSum (n : ℕ) (f : ℕ → List ℤ) (x : ℝ) :
    coeffEval (coeffRangeSum n f) x = ∑ i ∈ Finset.range n, coeffEval (f i) x := by
  induction n with
  | zero => simp [coeffRangeSum, coeffEval]
  | succ n ih => simp only [coeffRangeSum, coeffEval_add, ih, Finset.sum_range_succ]

end Davis
