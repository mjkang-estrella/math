import Mathlib

namespace FibonacciMinima
open scoped BigOperators
open Filter Finset
open Classical
attribute [local instance] propDecidable

/-- Forward solution of the integer Fibonacci recurrence. -/
def forward (x y : ℤ) : ℕ → ℤ :=
  Nat.twoStepInduction x y (fun _ u v => u + v)

@[simp] theorem forward_zero (x y : ℤ) : forward x y 0 = x := rfl
@[simp] theorem forward_one (x y : ℤ) : forward x y 1 = y := rfl
@[simp] theorem forward_step (x y : ℤ) (n : ℕ) :
    forward x y (n + 2) = forward x y n + forward x y (n + 1) := rfl

/-- The negative-index terms, with backward zero equal to the initial zeroth term. -/
def backward (x y : ℤ) : ℕ → ℤ :=
  Nat.twoStepInduction x (y - x) (fun _ u v => u - v)

@[simp] theorem backward_zero (x y : ℤ) : backward x y 0 = x := rfl
@[simp] theorem backward_one (x y : ℤ) : backward x y 1 = y - x := rfl
@[simp] theorem backward_step (x y : ℤ) (n : ℕ) :
    backward x y (n + 2) = backward x y n - backward x y (n + 1) := rfl

/-- Unique global absolute minimum at zero, including both infinite tails. -/
def minimumAtZero (x y : ℤ) : Prop :=
  (∀ n : ℕ, |x| < |forward x y (n + 1)|) ∧
  (∀ n : ℕ, |x| < |backward x y (n + 1)|)

theorem forward_neg (x y : ℤ) (n : ℕ) :
    forward (-x) (-y) n = -forward x y n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih ih' => simp [ih, ih']; ring

theorem backward_neg (x y : ℤ) (n : ℕ) :
    backward (-x) (-y) n = -backward x y n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp; ring
  | more n ih ih' => simp [ih, ih']; ring

theorem minimum_neg (x y : ℤ) : minimumAtZero (-x) (-y) ↔ minimumAtZero x y := by
  simp only [minimumAtZero, forward_neg, backward_neg, abs_neg]

/-- Positive same-sign tails stay beyond the threshold. -/
theorem forward_positive (x y t : ℤ) (ht : 0 ≤ t) (hx : t < x) (hy : t < y) :
    ∀ n, t < forward x y n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => exact hx
  | one => exact hy
  | more n ih ih' => rw [forward_step]; omega

theorem forward_shift (x y : ℤ) (n : ℕ) :
    forward x y (n + 1) = forward y (x + y) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih ih' =>
    calc
      forward x y (n + 2 + 1) = forward x y (n+1) + forward x y (n+1+1) := forward_step x y (n+1)
      _ = forward y (x+y) n + forward y (x+y) (n+1) := by rw [ih, ih']
      _ = forward y (x+y) (n+2) := (forward_step _ _ _).symm

/-- Opposite-sign backward tails alternate with growing absolute value. -/
theorem backward_large (x y t : ℤ) (ht : 0 ≤ t)
    (h : (t < y - x ∧ t < y - 2*x) ∨ (y - x < -t ∧ y - 2*x < -t)) :
    ∀ n, t < |backward x y (n + 1)| := by
  have hs : ∀ n, (t < backward x y (n+1) ∧ backward x y (n+2) < -t) ∨
      (backward x y (n+1) < -t ∧ t < backward x y (n+2)) := by
    intro n
    induction n with
    | zero =>
      simp only [zero_add, backward_one, backward_step, backward_zero]
      rcases h with h | h
      · left; omega
      · right; omega
    | succ n ih =>
      have he := backward_step x y (n+1)
      rw [show n+1+1=n+2 by omega] at he
      change (t < backward x y (n+2) ∧ backward x y (n+1+2) < -t) ∨
        (backward x y (n+2) < -t ∧ t < backward x y (n+1+2))
      rcases ih with h | h
      · right; constructor <;> omega
      · left; constructor <;> omega
  intro n
  rcases hs n with h | h
  · rw [abs_of_pos (by omega : 0 < backward x y (n+1))]; exact h.1
  · rw [abs_of_neg (by omega : backward x y (n+1) < 0)]; omega

/-- Exact cone criterion, stated without division by the first coordinate. -/
def cone (x y : ℤ) : Prop :=
  (x = 0 ∧ y ≠ 0) ∨
  (0 < x ∧ (y < -2*x ∨ 3*x < y)) ∨
  (x < 0 ∧ (-2*x < y ∨ y < 3*x))

theorem minimum_positive (x y : ℤ) (hx : 0 ≤ x)
    (hy : y < -2*x ∨ 3*x < y) : minimumAtZero x y := by
  rw [minimumAtZero, abs_of_nonneg hx]
  constructor
  · intro n
    rw [forward_shift]
    rcases hy with hy | hy
    · have hp := forward_positive (-y) (-(x+y)) x hx (by omega) (by omega) n
      rw [forward_neg] at hp
      rw [abs_of_neg (by omega : forward y (x+y) n < 0)]
      omega
    · have hp := forward_positive y (x+y) x hx (by omega) (by omega) n
      rw [abs_of_pos (by omega : 0 < forward y (x+y) n)]
      exact hp
  · apply backward_large x y x hx
    rcases hy with hy | hy
    · right; omega
    · left; omega

theorem minimum_iff_cone (x y : ℤ) : minimumAtZero x y ↔ cone x y := by
  constructor
  · intro h
    have h1 := h.1 0
    have h2 := h.1 1
    have hm1 := h.2 0
    have hm2 := h.2 1
    simp only [zero_add, forward_one, forward_step, forward_zero,
      backward_one, backward_step, backward_zero] at h1 h2 hm1 hm2
    unfold cone
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx] at h1 h2 hm1 hm2
      rcases eq_or_lt_of_le hx with hx | hx
      · left; constructor
        · omega
        · intro hy; simp [hy] at h1; omega
      · right; left; refine ⟨hx, ?_⟩
        rcases lt_or_ge y 0 with hy | hy
        · rw [abs_of_neg hy] at h1
          have : x + y < 0 := by omega
          rw [abs_of_neg this] at h2
          left; omega
        · rw [abs_of_nonneg hy] at h1
          have : 0 < y - x := by omega
          rw [abs_of_pos this] at hm1
          have : 0 < y - 2*x := by omega
          have he : x - (y-x) = -(y-2*x) := by ring
          rw [he, abs_neg, abs_of_pos this] at hm2
          right; omega
    · have hneg : minimumAtZero (-x) (-y) := (minimum_neg x y).2 h
      have h1 := hneg.1 0
      have h2 := hneg.1 1
      have hm1 := hneg.2 0
      have hm2 := hneg.2 1
      simp only [zero_add, forward_one, forward_step, forward_zero,
        backward_one, backward_step, backward_zero] at h1 h2 hm1 hm2
      have hxn : 0 ≤ -x := by omega
      rw [abs_of_nonneg hxn] at h1 h2 hm1 hm2
      by_cases hx0 : x = 0
      · left; constructor
        · exact hx0
        · intro hy; simp [hy, hx0] at h1
      · right; right; refine ⟨by omega, ?_⟩
        by_cases hy : y ≤ 0
        · rw [abs_of_nonneg (by omega : 0 ≤ -y)] at h1
          rw [abs_of_pos (by omega : 0 < -y - -x)] at hm1
          rw [abs_of_neg (by omega : -x - (-y - -x) < 0)] at hm2
          right; omega
        · rw [abs_of_neg (by omega : -y < 0)] at h1
          rw [abs_of_neg (by omega : -x + -y < 0)] at h2
          left; omega
  · intro h
    rcases h with ⟨rfl, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · apply minimum_positive 0 y (by omega)
      omega
    · exact minimum_positive x y (by omega) hy
    · apply (minimum_neg x y).1
      apply minimum_positive (-x) (-y) (by omega)
      omega

/-- All ordered integer initializations in the square. -/
def square (N : ℕ) : Finset (ℤ × ℤ) :=
  (Icc (-(N:ℤ)) N) ×ˢ (Icc (-(N:ℤ)) N)

noncomputable def successes (N : ℕ) : Finset (ℤ × ℤ) :=
  (square N).filter fun p => minimumAtZero p.1 p.2

noncomputable def row (N : ℕ) (x : ℤ) : Finset ℤ :=
  (Icc (-(N:ℤ)) N).filter (minimumAtZero x)

theorem square_card (N : ℕ) : (square N).card = (2*N+1)^2 := by
  have hc : (Icc (-(N:ℤ)) N).card = 2*N+1 := by rw [Int.card_Icc]; omega
  rw [square, card_product, hc]
  ring

theorem count_rows (N : ℕ) : (successes N).card =
    ∑ x ∈ Icc (-(N:ℤ)) N, (row N x).card := by
  simp only [successes, square, row, card_eq_sum_ones, sum_product, sum_filter]

theorem row_neg (N : ℕ) (x : ℤ) : (row N (-x)).card = (row N x).card := by
  apply Finset.card_bij (fun y _ => -y)
  · intro y hy
    simp only [row, mem_filter, mem_Icc] at hy ⊢
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    simpa only [neg_neg] using (minimum_neg (-x) y).2 hy.2
  · intro y hy z hz he
    omega
  · intro y hy
    refine ⟨-y, ?_, by simp⟩
    simp only [row, mem_filter, mem_Icc] at hy ⊢
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    exact (minimum_neg x y).2 hy.2

theorem row_zero (N : ℕ) : (row N 0).card = 2*N := by
  have he : row N 0 = (Icc (-(N:ℤ)) N).erase 0 := by
    ext y
    simp only [row, mem_filter, minimum_iff_cone, cone, mem_erase]
    constructor <;> intro h
    · rcases h with ⟨hb, h⟩; exact ⟨by simpa using h, hb⟩
    · exact ⟨h.2, by simp [h.1]⟩
  rw [he, card_erase_of_mem (by simp), Int.card_Icc]
  omega

/-- A positive row consists of the two disjoint integer intervals. -/
theorem row_positive (N j : ℕ) (hj : 0 < j) :
    (row N j).card = (N-2*j) + (N-3*j) := by
  have he : row N j = Icc (-(N:ℤ)) (-2*(j:ℤ)-1) ∪ Icc (3*(j:ℤ)+1) N := by
    ext y
    simp only [row, mem_filter, minimum_iff_cone, cone, mem_union, mem_Icc]
    have hj' : 0 < (j:ℤ) := by exact_mod_cast hj
    have hN : 0 ≤ (N:ℤ) := Int.natCast_nonneg N
    constructor <;> intro h <;> omega
  have hd : Disjoint (Icc (-(N:ℤ)) (-2*(j:ℤ)-1)) (Icc (3*(j:ℤ)+1) N) := by
    apply disjoint_left.mpr
    intro y hy hz
    simp only [mem_Icc] at hy hz
    omega
  rw [he, card_union_of_disjoint hd, Int.card_Icc, Int.card_Icc]
  omega

theorem symmetric_sum (N : ℕ) (f : ℤ → ℕ) (hf : ∀ x, f (-x) = f x) :
    ∑ x ∈ Icc (-(N:ℤ)) N, f x = f 0 + 2 * ∑ j ∈ Icc 1 N, f j := by
  let P := (Icc 1 N).image (fun j : ℕ => (j:ℤ))
  let M := (Icc 1 N).image (fun j : ℕ => -(j:ℤ))
  have he : Icc (-(N:ℤ)) N = insert 0 (P ∪ M) := by
    ext z
    simp only [P, M, mem_Icc, mem_insert, mem_union, mem_image]
    constructor
    · intro h
      rcases lt_trichotomy z 0 with hz | hz | hz
      · right; right; refine ⟨(-z).toNat, ?_, ?_⟩ <;> omega
      · exact Or.inl hz
      · right; left; refine ⟨z.toNat, ?_, ?_⟩ <;> omega
    · intro h
      rcases h with rfl | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ <;> omega
  have hd : Disjoint P M := by
    apply disjoint_left.mpr
    intro z hz hz'
    simp only [P, M, mem_image, mem_Icc] at hz hz'
    obtain ⟨j, hj, rfl⟩ := hz
    obtain ⟨k, hk, he⟩ := hz'
    omega
  have hn : 0 ∉ P ∪ M := by
    simp only [P, M, mem_union, mem_image, mem_Icc]
    rintro (⟨j, hj, he⟩ | ⟨j, hj, he⟩) <;> omega
  rw [he, sum_insert hn, sum_union hd]
  have hp : ∑ z ∈ P, f z = ∑ j ∈ Icc 1 N, f j := by
    unfold P
    rw [sum_image]
    intro a ha b hb he
    exact Int.natCast_inj.mp he
  have hm : ∑ z ∈ M, f z = ∑ j ∈ Icc 1 N, f j := by
    rw [show (∑ z ∈ M, f z) = ∑ j ∈ Icc 1 N, f (-(j:ℤ)) from
      sum_image (by intro a ha b hb he; exact Int.natCast_inj.mp (neg_injective he))]
    apply sum_congr rfl
    intro j hj
    exact hf j
  rw [hp, hm]
  omega

def triangle (N k : ℕ) : ℕ := ∑ j ∈ Icc 1 N, (N-k*j)

theorem exact_count (N : ℕ) :
    (successes N).card = 2*N + 2*triangle N 2 + 2*triangle N 3 := by
  rw [count_rows, symmetric_sum N (fun x => (row N x).card) (row_neg N), row_zero]
  have he : (∑ j ∈ Icc 1 N, (row N j).card) = triangle N 2 + triangle N 3 := by
    simp only [triangle, ← sum_add_distrib]
    apply sum_congr rfl
    intro j hj
    exact row_positive N j (by simp only [mem_Icc] at hj; omega)
  rw [he]
  omega

theorem triangle_truncate (N k : ℕ) (hk : 0 < k) :
    triangle N k = ∑ j ∈ Icc 1 (N/k), (N-k*j) := by
  unfold triangle
  symm
  apply sum_subset
  · intro j hj
    simp only [mem_Icc] at hj ⊢
    exact ⟨hj.1, le_trans hj.2 (Nat.div_le_self N k)⟩
  · intro j hj hj'
    simp only [mem_Icc] at hj hj'
    have : N < k*j := by
      have : N/k < j := by omega
      exact (Nat.div_lt_iff_lt_mul hk).1 this |>.trans_eq (Nat.mul_comm j k)
    omega

theorem sum_linear (N k q : ℕ) :
    2*(∑ j ∈ Icc 1 q, ((N:ℝ)-(k:ℝ)*j)) =
      (q:ℝ)*(2*N-k*(q+1)) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ q+1)]
    push_cast
    nlinarith

theorem triangle_formula (N k : ℕ) (hk : 0 < k) :
    2*(triangle N k : ℝ) = (N/k:ℕ)*(2*(N:ℝ)-(k:ℝ)*((N/k:ℕ)+1)) := by
  rw [triangle_truncate N k hk, Nat.cast_sum]
  have he : (∑ j ∈ Icc 1 (N/k), ((N-k*j:ℕ):ℝ)) =
      ∑ j ∈ Icc 1 (N/k), ((N:ℝ)-(k:ℝ)*j) := by
    apply sum_congr rfl
    intro j hj
    have hle : k*j ≤ N := by
      simp only [mem_Icc] at hj
      simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hk).1 hj.2
    rw [Nat.cast_sub hle, Nat.cast_mul]
  rw [he, sum_linear]

/-- The unique bi-infinite solution, indexed by the integers. -/
def sequence (x y : ℤ) : ℤ → ℤ
  | .ofNat n => forward x y n
  | .negSucc n => backward x y (n+1)

@[simp] theorem sequence_nat (x y : ℤ) (n : ℕ) : sequence x y n = forward x y n := rfl
@[simp] theorem sequence_neg_nat (x y : ℤ) (n : ℕ) :
    sequence x y (-(n:ℤ)) = backward x y n := by
  cases n with
  | zero => rfl
  | succ n => rfl

theorem sequence_recurrence (x y n : ℤ) :
    sequence x y (n+2) = sequence x y n + sequence x y (n+1) := by
  cases n with
  | ofNat n =>
    change forward x y (n+2) = forward x y n + forward x y (n+1)
    exact forward_step x y n
  | negSucc n =>
    cases n with
    | zero => change y = (y-x)+x; omega
    | succ n =>
      have he := backward_step x y n
      have h0 : Int.negSucc (n+1) = -((n+2:ℕ):ℤ) := by omega
      have h1 : Int.negSucc (n+1)+1 = -((n+1:ℕ):ℤ) := by omega
      have h2 : Int.negSucc (n+1)+2 = -(n:ℤ) := by omega
      rw [h1, h2, h0, sequence_neg_nat, sequence_neg_nat, sequence_neg_nat]
      omega

theorem global_minimum_iff (x y : ℤ) :
    (∀ n : ℤ, n ≠ 0 → |sequence x y 0| < |sequence x y n|) ↔
      minimumAtZero x y := by
  constructor
  · intro h
    constructor <;> intro n
    · exact h (n+1:ℕ) (by omega)
    · have he := h (-((n+1:ℕ):ℤ)) (by omega)
      rw [sequence_neg_nat] at he
      exact he
  · intro h n hn
    cases n with
    | ofNat n =>
      cases n with
      | zero => contradiction
      | succ n => exact h.1 n
    | negSucc n => exact h.2 n

/-- Actual square-uniform probability of a unique minimum at zero. -/
noncomputable def probability (N : ℕ) : ℝ :=
  (successes N).card / (square N).card

theorem quotient_ratio_limit (k : ℕ) (hk : 0 < k) :
    Tendsto (fun N : ℕ => ((N/k:ℕ):ℝ)/(N:ℝ)) atTop (nhds (1/(k:ℝ))) := by
  have hrem : Tendsto (fun N : ℕ => ((N%k:ℕ):ℝ)/(N:ℝ)) atTop (nhds 0) := by
    apply squeeze_zero (g := fun N : ℕ => (k:ℝ)/(N:ℝ))
    · intro N; positivity
    · intro N
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
      exact_mod_cast Nat.le_of_lt (Nat.mod_lt N hk)
    · exact tendsto_const_div_atTop_nhds_zero_nat (k:ℝ)
  have hk' : (k:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have he : ∀ᶠ N : ℕ in atTop,
      ((N/k:ℕ):ℝ)/(N:ℝ) = (1-((N%k:ℕ):ℝ)/(N:ℝ))/(k:ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (N:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    have hd := Nat.mod_add_div N k
    have hd' : ((N%k:ℕ):ℝ)+(k:ℝ)*((N/k:ℕ):ℝ) = N := by exact_mod_cast hd
    field_simp
    nlinarith
  apply (tendsto_congr' he).mpr
  convert ((tendsto_const_nhds (x := (1:ℝ))).sub hrem).div_const (k:ℝ) using 1; norm_num

theorem triangle_scaled_limit (k : ℕ) (hk : 0 < k) :
    Tendsto (fun N : ℕ => (triangle N k : ℝ)/(N:ℝ)^2) atTop (nhds (1/(2*(k:ℝ)))) := by
  have hq := quotient_ratio_limit k hk
  have hi := tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)
  have ht := (hq.mul ((tendsto_const_nhds (x := (2:ℝ))).sub
    (((tendsto_const_nhds (x := (k:ℝ)))).mul (hq.add hi)))).div_const 2
  have hk' : (k:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hv : (1/(k:ℝ))*(2-(k:ℝ)*(1/(k:ℝ)+0))/2 = 1/(2*(k:ℝ)) := by
    field_simp
    ring
  rw [hv] at ht
  apply (tendsto_congr' (show ∀ᶠ N : ℕ in atTop,
      (triangle N k : ℝ)/(N:ℝ)^2 =
        (((N/k:ℕ):ℝ)/(N:ℝ))*(2-(k:ℝ)*(((N/k:ℕ):ℝ)/(N:ℝ)+1/(N:ℝ)))/2 from ?_)).mpr ht
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have he := triangle_formula N k hk
  field_simp
  nlinarith

theorem count_scaled_limit :
    Tendsto (fun N : ℕ => ((successes N).card:ℝ)/(N:ℝ)^2) atTop (nhds (5/6:ℝ)) := by
  have h2 := triangle_scaled_limit 2 (by norm_num)
  have h3 := triangle_scaled_limit 3 (by norm_num)
  have hi := tendsto_const_div_atTop_nhds_zero_nat (2:ℝ)
  have ht := (hi.add (h2.const_mul 2)).add (h3.const_mul 2)
  norm_num at ht
  apply (tendsto_congr' (show ∀ᶠ N : ℕ in atTop,
      ((successes N).card:ℝ)/(N:ℝ)^2 =
        2/(N:ℝ)+2*((triangle N 2:ℝ)/(N:ℝ)^2)+2*((triangle N 3:ℝ)/(N:ℝ)^2) from ?_)).mpr ht
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  rw [exact_count]
  push_cast
  field_simp

/-- The full recurrence-to-lattice-count-to-limit result under square-uniform sampling. -/
theorem square_uniform_limit : Tendsto probability atTop (nhds (5/24:ℝ)) := by
  have hi := tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)
  have hd := ((tendsto_const_nhds (x := (2:ℝ))).add hi).pow 2
  have ht := count_scaled_limit.div hd (by norm_num)
  norm_num at ht
  apply (tendsto_congr' (show ∀ᶠ N : ℕ in atTop,
      probability N = (((successes N).card:ℝ)/(N:ℝ)^2)/(2+(N:ℝ)⁻¹)^2 from ?_)).mpr ht
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  rw [probability, square_card]
  push_cast
  field_simp

theorem square_uniform_counterexample :
    Tendsto probability atTop (nhds (5/24:ℝ)) ∧
    ¬Tendsto probability atTop (nhds (1/4:ℝ)) := by
  refine ⟨square_uniform_limit, ?_⟩
  intro h
  have he := tendsto_nhds_unique square_uniform_limit h
  norm_num at he

/-- A minimum with ties allowed. -/
def weakMinimumAtZero (x y : ℤ) : Prop :=
  (∀ n : ℕ, |x| ≤ |forward x y (n+1)|) ∧
  (∀ n : ℕ, |x| ≤ |backward x y (n+1)|)

theorem weak_neg (x y : ℤ) : weakMinimumAtZero (-x) (-y) ↔ weakMinimumAtZero x y := by
  simp only [weakMinimumAtZero, forward_neg, backward_neg, abs_neg]

theorem weak_positive_cone (x y : ℤ) (hx : 0 ≤ x) (h : weakMinimumAtZero x y) :
    y ≤ -2*x ∨ 3*x ≤ y := by
  have h1 := h.1 0
  have h2 := h.1 1
  have hm1 := h.2 0
  have hm2 := h.2 1
  simp only [zero_add, forward_one, forward_step, forward_zero,
    backward_one, backward_step, backward_zero, abs_of_nonneg hx] at h1 h2 hm1 hm2
  rw [le_abs] at h1 h2 hm1 hm2
  omega

/-- Ties at zero lie on just two integer lines; there is no unproved tie-density assumption. -/
theorem weak_strict_or_boundary (x y : ℤ) (h : weakMinimumAtZero x y) :
    minimumAtZero x y ∨ y = -2*x ∨ y = 3*x := by
  by_cases hb1 : y = -2*x
  · exact Or.inr (Or.inl hb1)
  by_cases hb2 : y = 3*x
  · exact Or.inr (Or.inr hb2)
  left
  apply (minimum_iff_cone x y).mpr
  unfold cone
  rcases le_total 0 x with hx | hx
  · have hc := weak_positive_cone x y hx h
    by_cases hx0 : x = 0
    · left; constructor
      · exact hx0
      · omega
    · right; left; constructor <;> omega
  · have hn : weakMinimumAtZero (-x) (-y) := (weak_neg x y).2 h
    have hc := weak_positive_cone (-x) (-y) (by omega) hn
    by_cases hx0 : x = 0
    · left; constructor
      · exact hx0
      · omega
    · right; right; constructor <;> omega

noncomputable def linePoints (N : ℕ) (k : ℤ) : Finset (ℤ × ℤ) :=
  (square N).filter fun p => p.2 = k*p.1

theorem line_card_bound (N : ℕ) (k : ℤ) : (linePoints N k).card ≤ 2*N+1 := by
  have hc : (Icc (-(N:ℤ)) N).card = 2*N+1 := by rw [Int.card_Icc]; omega
  rw [← hc]
  apply card_le_card_of_injOn Prod.fst
  · intro p hp
    change p ∈ linePoints N k at hp
    simp only [linePoints, mem_filter, square, mem_product] at hp
    exact hp.1.1
  · intro p hp q hq he
    change p ∈ linePoints N k at hp
    change q ∈ linePoints N k at hq
    simp only [linePoints, mem_filter] at hp hq
    apply Prod.ext he
    rw [hp.2, hq.2, he]

noncomputable def weakSuccesses (N : ℕ) : Finset (ℤ × ℤ) :=
  (square N).filter fun p => weakMinimumAtZero p.1 p.2

noncomputable def weakProbability (N : ℕ) : ℝ :=
  (weakSuccesses N).card / (square N).card

theorem weak_count_bounds (N : ℕ) :
    (successes N).card ≤ (weakSuccesses N).card ∧
    (weakSuccesses N).card ≤ (successes N).card + 2*(2*N+1) := by
  constructor
  · apply card_le_card
    intro p hp
    simp only [successes, weakSuccesses, mem_filter] at hp ⊢
    exact ⟨hp.1, ⟨fun n => (hp.2.1 n).le, fun n => (hp.2.2 n).le⟩⟩
  · have hs : weakSuccesses N ⊆ successes N ∪ linePoints N (-2) ∪ linePoints N 3 := by
      intro p hp
      simp only [weakSuccesses, mem_filter] at hp
      simp only [mem_union, successes, linePoints, mem_filter]
      rcases weak_strict_or_boundary p.1 p.2 hp.2 with h | h | h
      · exact Or.inl (Or.inl ⟨hp.1, h⟩)
      · exact Or.inl (Or.inr ⟨hp.1, h⟩)
      · exact Or.inr ⟨hp.1, h⟩
    calc
      (weakSuccesses N).card ≤ (successes N ∪ linePoints N (-2) ∪ linePoints N 3).card := card_le_card hs
      _ ≤ (successes N).card + (linePoints N (-2)).card + (linePoints N 3).card :=
        (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
      _ ≤ (successes N).card + 2*(2*N+1) := by
        have h1 := line_card_bound N (-2)
        have h2 := line_card_bound N 3
        omega

theorem weak_probability_bounds (N : ℕ) (hN : 0 < N) :
    probability N ≤ weakProbability N ∧ weakProbability N ≤ probability N + 2/(N:ℝ) := by
  obtain ⟨hlo, hhi⟩ := weak_count_bounds N
  have hlo' : ((successes N).card:ℝ) ≤ (weakSuccesses N).card := by exact_mod_cast hlo
  have hhi' : ((weakSuccesses N).card:ℝ) ≤ (successes N).card + 2*(2*(N:ℝ)+1) := by exact_mod_cast hhi
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  simp only [probability, weakProbability, square_card, Nat.cast_pow, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  constructor
  · exact div_le_div_of_nonneg_right hlo' (sq_nonneg _)
  · apply (div_le_iff₀ (sq_pos_of_pos (by positivity : (0:ℝ) < 2*N+1))).mpr
    have he : (((successes N).card:ℝ)/(2*N+1)^2 + 2/(N:ℝ))*(2*N+1)^2 =
        (successes N).card + 2*(2*N+1)^2/(N:ℝ) := by
      field_simp
    rw [he]
    have hb : 2*(2*(N:ℝ)+1) ≤ 2*(2*(N:ℝ)+1)^2/(N:ℝ) := by
      apply (le_div_iff₀ hn).mpr
      nlinarith
    linarith

theorem weak_square_uniform_limit : Tendsto weakProbability atTop (nhds (5/24:ℝ)) := by
  have hi := tendsto_const_div_atTop_nhds_zero_nat (2:ℝ)
  have hu : Tendsto (fun N => probability N + 2/(N:ℝ)) atTop (nhds (5/24:ℝ)) := by
    simpa only [add_zero] using square_uniform_limit.add hi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' square_uniform_limit hu
  · filter_upwards [eventually_gt_atTop 0] with N hN
    exact (weak_probability_bounds N hN).1
  · filter_upwards [eventually_gt_atTop 0] with N hN
    exact (weak_probability_bounds N hN).2

theorem weak_global_minimum_iff (x y : ℤ) :
    (∀ n : ℤ, |sequence x y 0| ≤ |sequence x y n|) ↔ weakMinimumAtZero x y := by
  constructor
  · intro h
    constructor <;> intro n
    · exact h (n+1:ℕ)
    · have he := h (-((n+1:ℕ):ℤ))
      rw [sequence_neg_nat] at he
      exact he
  · intro h n
    cases n with
    | ofNat n =>
      cases n with
      | zero => exact le_rfl
      | succ n => exact h.1 n
    | negSucc n => exact h.2 n

/-- MathDB 371202, under the precisely specified expanding-square interpretation.
Both strict and tie-inclusive global-minimum probabilities converge to 5/24. -/
theorem fibonacci_minima_square_counterexample :
    (∀ x y n : ℤ, sequence x y (n+2) = sequence x y n + sequence x y (n+1)) ∧
    (∀ x y : ℤ, (∀ n : ℤ, n ≠ 0 → |sequence x y 0| < |sequence x y n|) ↔ cone x y) ∧
    (∀ N : ℕ, (successes N).card = 2*N + 2*triangle N 2 + 2*triangle N 3) ∧
    Tendsto probability atTop (nhds (5/24:ℝ)) ∧
    Tendsto weakProbability atTop (nhds (5/24:ℝ)) ∧
    ¬Tendsto weakProbability atTop (nhds (1/4:ℝ)) := by
  refine ⟨sequence_recurrence, ?_, exact_count, square_uniform_limit, weak_square_uniform_limit, ?_⟩
  · intro x y
    exact (global_minimum_iff x y).trans (minimum_iff_cone x y)
  · intro h
    have he := tendsto_nhds_unique weak_square_uniform_limit h
    norm_num at he

end FibonacciMinima
