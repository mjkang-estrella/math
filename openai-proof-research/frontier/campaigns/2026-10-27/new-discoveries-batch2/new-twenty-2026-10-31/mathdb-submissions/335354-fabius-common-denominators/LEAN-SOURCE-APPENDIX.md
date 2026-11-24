# Lean source appendix for MathDB 335354

All 39 modules, in dependency order. Each block is byte-identical to its src/ file.
Third-party attribution and line ranges are recorded in PAPER.md, REPORT.md, and third-party.json.

### `WeightedMinimumCore.lean`

```lean
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
A kernel-checkable core of Section 4 of PROOF-335354.md.
This is NOT the full Fabius conjecture: the formal hypotheses below are the
coefficient/rescaling facts proved in the written argument. No source axiom or
`sorry` is introduced. The complete arithmetic endpoint remains a Lean plan.
-/

namespace FabiusProofLane

open Finset

/-- Choose the first minimum of an integer-valued weight on a finite prefix. -/
theorem exists_first_minimum (M : ℕ) (W : ℕ → ℤ) :
    ∃ j, j ≤ M ∧ W j ≤ W 0 ∧ (∀ i, i ≤ M → W j ≤ W i) ∧
      (∀ i, i < j → W j < W i) := by
  let g (i : ℕ) : ℤ := ((M : ℤ) + 1) * W i + i
  obtain ⟨j, hjmem, hmin⟩ :=
    (range (M + 1)).exists_min_image g (by simp)
  have hj : j ≤ M := by simpa using (Nat.le_of_lt_succ (mem_range.mp hjmem))
  have hji (i : ℕ) (hi : i ≤ M) : g j ≤ g i :=
    hmin i (mem_range.mpr (Nat.lt_succ_of_le hi))
  have hW (i : ℕ) (hi : i ≤ M) : W j ≤ W i := by
    have hg := hji i hi
    have hMj : (j : ℤ) ≤ M := by exact_mod_cast hj
    have hMi : (i : ℤ) ≤ M := by exact_mod_cast hi
    have hj0 : (0 : ℤ) ≤ j := Int.natCast_nonneg j
    have hM0 : (0 : ℤ) ≤ M := Int.natCast_nonneg M
    dsimp [g] at hg
    by_contra h
    have hw : W i + 1 ≤ W j := by omega
    nlinarith
  refine ⟨j, hj, hW 0 (Nat.zero_le M), hW, ?_⟩
  intro i hi
  have hiM : i ≤ M := le_trans (Nat.le_of_lt hi) hj
  have hw := hW i hiM
  have hg := hji i hiM
  have hij : (i : ℤ) < j := by exact_mod_cast hi
  dsimp [g] at hg
  by_contra h
  have heq : W j = W i := by omega
  rw [heq] at hg
  omega

/-- A unique least-valuation positive summand determines the sum's valuation. -/
theorem valuation_sum_unique_min {p : ℕ} [Fact p.Prime]
    (S : Finset ℕ) (F : ℕ → ℚ) (j : ℕ) (hj : j ∈ S)
    (hpos : ∀ i, 0 < F i)
    (hmin : ∀ i ∈ S, i ≠ j → padicValRat p (F j) < padicValRat p (F i)) :
    padicValRat p (∑ i ∈ S, F i) = padicValRat p (F j) := by
  have hsplit := S.sum_erase_add F hj
  by_cases he : (S.erase j).Nonempty
  · have hrestpos : 0 < ∑ i ∈ S.erase j, F i :=
      sum_pos (fun i _ => hpos i) he
    have hrestval : padicValRat p (F j) <
        padicValRat p (∑ i ∈ S.erase j, F i) :=
      padicValRat.lt_sum_of_lt he (fun i hi =>
        hmin i (mem_erase.mp hi).2 (mem_erase.mp hi).1) hpos
    rw [← hsplit, add_comm]
    exact padicValRat.add_eq_of_lt
      (ne_of_gt (add_pos (hpos j) hrestpos))
      (ne_of_gt (hpos j)) (ne_of_gt hrestpos) hrestval
  · have hempty : S.erase j = ∅ := not_nonempty_iff_eq_empty.mp he
    rw [hempty, sum_empty, zero_add] at hsplit
    rw [← hsplit]

/-- The first minimum is forced into the final `r` coefficient indices.

For the Fabius application `r=(p-1)/2`, `a k=e_(2k)`, `H l` is the
coefficient of degree `2l` after `p-1` rescalings, and `c n=T^(2n)-1`.
All premises are explicitly displayed; this theorem asserts no unproved
Fabius-series identity. -/
theorem weighted_minimum_at_end {p r : ℕ} [Fact p.Prime]
    (hr : 0 < r) (a H c : ℕ → ℚ)
    (ha : ∀ i, 0 < a i) (ha0 : a 0 = 1)
    (hH : ∀ i, 0 < H i)
    (hc : ∀ n, 0 < n → 0 < c n)
    (hcv : ∀ n, 0 < n → 1 ≤ padicValRat p (c n))
    (hbound : ∀ l, 0 ≤ (2 * (r : ℤ)) * padicValRat p (H l) + 2 * l)
    (hsmall : ∀ l, 0 < l → l < r →
      0 < (2 * (r : ℤ)) * padicValRat p (H l) + 2 * l)
    (hcritical : padicValRat p (H r) = -1)
    (hrec : ∀ n, 0 < n → c n * a n =
      ∑ i ∈ range n, H (i+1) * a (n-(i+1)))
    (M : ℕ) :
    ∃ j, j ≤ M ∧ M < j+r ∧
      (2 * (r : ℤ)) * padicValRat p (a j) + 2*j ≤ 0 := by
  let P : ℤ := 2 * r
  let W (i : ℕ) : ℤ := P * padicValRat p (a i) + 2*i
  have hP : 0 < P := by dsimp [P]; exact_mod_cast (Nat.mul_pos (by decide : 0 < 2) hr)
  obtain ⟨j, hj, hj0, hmin, hfirst⟩ := exists_first_minimum M W
  have hW0 : W 0 = 0 := by simp [W, ha0]
  have hjnonpos : W j ≤ 0 := by simpa [hW0] using hj0
  refine ⟨j, hj, ?_, hjnonpos⟩
  by_contra hbad
  have hnM : j+r ≤ M := by omega
  let n := j+r
  have hn : 0 < n := by dsimp [n]; omega
  let U (i : ℕ) : ℚ := H (i+1) * a (n-(i+1))
  have hUpos : ∀ i, 0 < U i := by
    intro i
    exact mul_pos (hH _) (ha _)
  have hcritmem : r-1 ∈ range n := by simp only [mem_range]; dsimp [n]; omega
  have hrl : r-1+1 = r := by omega
  have hnj : n-r = j := by dsimp [n]; omega
  have hcritval : padicValRat p (U (r-1)) = -1 + padicValRat p (a j) := by
    dsimp [U]
    rw [hrl, hnj, padicValRat.mul (ne_of_gt (hH r)) (ne_of_gt (ha j)), hcritical]
  have hcritweight : P * padicValRat p (U (r-1)) + 2*(n : ℤ) = W j := by
    rw [hcritval]
    dsimp [P, W, n]
    ring
  have hUmin : ∀ i ∈ range n, i ≠ r-1 →
      padicValRat p (U (r-1)) < padicValRat p (U i) := by
    intro i hi hine
    have hiN : i+1 ≤ n := by have := mem_range.mp hi; omega
    have hiNM : n-(i+1) ≤ M := le_trans (Nat.sub_le _ _) hnM
    have hWmin := hmin (n-(i+1)) hiNM
    have hdeg : ((n-(i+1) : ℕ) : ℤ) = (n : ℤ) - (i+1 : ℕ) := Nat.cast_sub hiN
    have hUval : padicValRat p (U i) =
        padicValRat p (H (i+1)) + padicValRat p (a (n-(i+1))) := by
      exact padicValRat.mul (ne_of_gt (hH _)) (ne_of_gt (ha _))
    have hne : i+1 ≠ r := by omega
    have hweight : W j < P * padicValRat p (U i) + 2*(n : ℤ) := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hs := hsmall (i+1) (by omega) hlt
        change 0 < P * padicValRat p (H (i+1)) + 2*(i+1 : ℕ) at hs
        dsimp [W] at hWmin
        rw [hdeg] at hWmin
        rw [hUval]
        nlinarith
      · have hij : n-(i+1) < j := by dsimp [n] at *; omega
        have hw := hfirst (n-(i+1)) hij
        have hb := hbound (i+1)
        change 0 ≤ P * padicValRat p (H (i+1)) + 2*(i+1 : ℕ) at hb
        dsimp [W] at hw
        rw [hdeg] at hw
        rw [hUval]
        nlinarith
    have hmul : P * padicValRat p (U (r-1)) < P * padicValRat p (U i) := by
      linarith [hcritweight]
    by_contra hnot
    have hle := mul_le_mul_of_nonneg_left (le_of_not_gt hnot) (le_of_lt hP)
    omega
  have hsumval := valuation_sum_unique_min (range n) U (r-1) hcritmem hUpos hUmin
  have heq := congrArg (padicValRat p) (hrec n hn)
  change padicValRat p (c n * a n) = padicValRat p (∑ i ∈ range n, U i) at heq
  rw [padicValRat.mul (ne_of_gt (hc n hn)) (ne_of_gt (ha n)), hsumval,
    hcritval] at heq
  have hcn := hcv n hn
  have hWn := hmin n hnM
  dsimp [W, P, n] at hWn
  dsimp [P] at hP
  nlinarith

end FabiusProofLane
```

### `WeightedMinimumArithmetic.lean`

```lean
import WeightedMinimumCore

namespace FabiusProofLane

/-- The end-window conclusion gives the denominator exponent needed in the paper. -/
theorem denominator_bound_of_end (r M j : ℕ) (v : ℤ)
    (_hr : 0 < r) (hwindow : M < j+r)
    (hweight : (2*(r : ℤ))*v + 2*j ≤ 0) :
    ((M/r : ℕ) : ℤ) ≤ -v := by
  have hdiv : (r : ℤ) * (M/r : ℕ) ≤ M := by
    exact_mod_cast Nat.mul_div_le M r
  have hr0 : (0 : ℤ) ≤ r := Int.natCast_nonneg r
  have hw : (M : ℤ) < (j : ℤ) + r := by exact_mod_cast hwindow
  by_contra h
  have hv : -v ≤ (M/r : ℕ) - (1 : ℤ) := by omega
  have hmul := mul_le_mul_of_nonneg_left hv hr0
  nlinarith

/-- Legendre's bound in the exact floor form used by Conjecture 16(b). -/
theorem factorial_valuation_le_div (p N : ℕ) [hp : Fact p.Prime] :
    padicValNat p (N+1).factorial ≤ N/(p-1) := by
  have hp1 : 0 < p-1 := Nat.sub_pos_of_lt hp.out.one_lt
  have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (Nat.succ_ne_zero N)
  simp only [Nat.succ_eq_add_one] at h
  apply (Nat.le_div_iff_mul_le hp1).mpr
  rw [Nat.mul_comm]
  omega

/-- Each coefficient of sinh(z)/z obeys the required weighted factorial bound. -/
theorem factorial_kernel_weight (p m : ℕ) [hp : Fact p.Prime] :
    0 ≤ ((p : ℤ)-1) * padicValRat p (1 / ((m+1).factorial : ℚ)) + m := by
  have hp1 : 1 ≤ p := le_of_lt hp.out.one_lt
  have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (Nat.succ_ne_zero m)
  simp only [Nat.succ_eq_add_one] at h
  have hle : (p-1) * padicValNat p (m+1).factorial ≤ m := by omega
  have hz : (((p-1) * padicValNat p (m+1).factorial : ℕ) : ℤ) ≤ m := by
    exact_mod_cast hle
  simp only [Nat.cast_mul, Nat.cast_sub hp1, Nat.cast_one] at hz
  simp only [one_div, padicValRat.inv, padicValRat.of_nat]
  nlinarith

#print axioms denominator_bound_of_end
#print axioms factorial_valuation_le_div
#print axioms factorial_kernel_weight

end FabiusProofLane
```

### `KernelCoefficients.lean`

```lean
import WeightedMinimumArithmetic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Prime.Factorial

namespace FabiusProofLane
open Finset

/-- Membership in the local ring Z_(p), phrased using rational valuations. -/
def IntegralAt (p : ℕ) (q : ℚ) : Prop := 0 ≤ padicValRat p q

lemma integralAt_zero (p : ℕ) : IntegralAt p 0 := by simp [IntegralAt]
lemma integralAt_one (p : ℕ) : IntegralAt p 1 := by simp [IntegralAt]

lemma integralAt_add {p : ℕ} [Fact p.Prime] {q r : ℚ}
    (hq : IntegralAt p q) (hr : IntegralAt p r) : IntegralAt p (q+r) := by
  by_cases h : q+r=0
  · rw [h]; exact integralAt_zero p
  · exact le_trans (le_min hq hr) (padicValRat.min_le_padicValRat_add h)

lemma integralAt_mul {p : ℕ} [Fact p.Prime] {q r : ℚ}
    (hq : IntegralAt p q) (hr : IntegralAt p r) : IntegralAt p (q*r) := by
  by_cases hq0 : q=0
  · simp [hq0, IntegralAt]
  by_cases hr0 : r=0
  · simp [hr0, IntegralAt]
  unfold IntegralAt at *
  rw [padicValRat.mul hq0 hr0]
  omega

lemma integralAt_neg {p : ℕ} {q : ℚ} (hq : IntegralAt p q) : IntegralAt p (-q) := by
  simpa [IntegralAt] using hq

lemma integralAt_sub {p : ℕ} [Fact p.Prime] {q r : ℚ}
    (hq : IntegralAt p q) (hr : IntegralAt p r) : IntegralAt p (q-r) := by
  simpa only [sub_eq_add_neg] using integralAt_add hq (integralAt_neg hr)

lemma integralAt_sum {p : ℕ} [Fact p.Prime] (S : Finset ℕ) (F : ℕ → ℚ)
    (hF : ∀ i ∈ S, IntegralAt p (F i)) : IntegralAt p (∑ i ∈ S, F i) := by
  induction S using Finset.induction_on with
  | empty => simpa using integralAt_zero p
  | @insert i S hi ih =>
    rw [sum_insert hi]
    exact integralAt_add (hF i (mem_insert_self i S))
      (ih (fun j hj => hF j (mem_insert_of_mem hj)))

lemma weighted_add {p : ℕ} [Fact p.Prime] (P d : ℤ) (hP : 0 ≤ P) (hd : 0 ≤ d)
    {q r : ℚ} (hq : 0 ≤ P * padicValRat p q + d)
    (hr : 0 ≤ P * padicValRat p r + d) :
    0 ≤ P * padicValRat p (q+r) + d := by
  by_cases h : q+r=0
  · simpa [h] using hd
  have hv := padicValRat.min_le_padicValRat_add (p:=p) h
  rcases le_total (padicValRat p q) (padicValRat p r) with hle | hle
  · rw [min_eq_left hle] at hv
    have := mul_le_mul_of_nonneg_left hv hP
    linarith
  · rw [min_eq_right hle] at hv
    have := mul_le_mul_of_nonneg_left hv hP
    linarith

lemma weighted_sum {p : ℕ} [Fact p.Prime] (P d : ℤ) (hP : 0 ≤ P) (hd : 0 ≤ d)
    (S : Finset ℕ) (F : ℕ → ℚ)
    (hF : ∀ i ∈ S, 0 ≤ P * padicValRat p (F i) + d) :
    0 ≤ P * padicValRat p (∑ i ∈ S, F i) + d := by
  induction S using Finset.induction_on with
  | empty => simpa using hd
  | @insert i S hi ih =>
    rw [sum_insert hi]
    exact weighted_add P d hP hd (hF i (mem_insert_self i S))
      (ih (fun j hj => hF j (mem_insert_of_mem hj)))

/-- Coefficient convolution, with even degrees indexed by half their degree. -/
def conv (a b : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ range (n+1), a i * b (n-i)

lemma conv_pos (a b : ℕ → ℚ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (n : ℕ) :
    0 < conv a b n := by
  exact sum_pos (fun i _ => mul_pos (ha i) (hb (n-i))) (by simp)

lemma conv_zero (a b : ℕ → ℚ) : conv a b 0 = a 0 * b 0 := by simp [conv]

lemma conv_integral_below {p : ℕ} [Fact p.Prime] (a b : ℕ → ℚ) (r : ℕ)
    (ha : ∀ i, i < r → IntegralAt p (a i))
    (hb : ∀ i, i < r → IntegralAt p (b i)) (n : ℕ) (hn : n < r) :
    IntegralAt p (conv a b n) := by
  apply integralAt_sum
  intro i hi
  have hi' : i ≤ n := Nat.le_of_lt_succ (mem_range.mp hi)
  exact integralAt_mul (ha i (lt_of_le_of_lt hi' hn))
    (hb (n-i) (lt_of_le_of_lt (Nat.sub_le _ _) hn))

lemma conv_weight {p : ℕ} [Fact p.Prime] (P : ℤ) (hP : 0 ≤ P)
    (a b : ℕ → ℚ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hwa : ∀ i, 0 ≤ P * padicValRat p (a i) + 2*i)
    (hwb : ∀ i, 0 ≤ P * padicValRat p (b i) + 2*i) (n : ℕ) :
    0 ≤ P * padicValRat p (conv a b n) + 2*n := by
  apply weighted_sum P (2*n) hP (by positivity)
  intro i hi
  have hi' : i ≤ n := Nat.le_of_lt_succ (mem_range.mp hi)
  have hsub : ((n-i : ℕ) : ℤ) = (n : ℤ)-i := Nat.cast_sub hi'
  rw [padicValRat.mul (ne_of_gt (ha i)) (ne_of_gt (hb (n-i)))]
  have ha' := hwa i
  have hb' := hwb (n-i)
  rw [hsub] at hb'
  linarith

/-- The individual rescaled sinh(z)/z coefficients, indexed by even degree. -/
def sinhKernel (i n : ℕ) : ℚ := (2 : ℚ)^(i*(2*n)) / ((2*n+1).factorial : ℚ)

lemma sinhKernel_pos (i n : ℕ) : 0 < sinhKernel i n := by
  unfold sinhKernel
  positivity

lemma sinhKernel_zero (i : ℕ) : sinhKernel i 0 = 1 := by simp [sinhKernel]

lemma sinhKernel_val {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (i n : ℕ) :
    padicValRat p (sinhKernel i n) = -(padicValNat p (2*n+1).factorial : ℤ) := by
  have hpnot : ¬ p ∣ 2 := by
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h)
  have htwo : padicValRat p (2 : ℚ) = 0 := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
    simp [padicValNat.eq_zero_of_not_dvd hpnot]
  unfold sinhKernel
  rw [padicValRat.div (by positivity) (by positivity), padicValRat.pow, htwo,
    mul_zero, padicValRat.of_nat]
  omega

lemma sinhKernel_weight {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (i n : ℕ) :
    0 ≤ ((p : ℤ)-1) * padicValRat p (sinhKernel i n) + 2*n := by
  rw [sinhKernel_val hp2]
  have h := factorial_kernel_weight p (2*n)
  simp only [one_div, padicValRat.inv, padicValRat.of_nat] at h
  exact h


/-- First `k+1` rescaled sinh factors, without formal-power-series infrastructure. -/
def kernelProduct : ℕ → ℕ → ℚ
  | 0 => sinhKernel 0
  | k+1 => conv (kernelProduct k) (sinhKernel (k+1))

lemma kernelProduct_pos (k n : ℕ) : 0 < kernelProduct k n := by
  induction k generalizing n with
  | zero => exact sinhKernel_pos 0 n
  | succ k ih =>
    apply conv_pos
    · intro i; exact ih i
    · intro i; exact sinhKernel_pos (k+1) i

lemma kernelProduct_zero (k : ℕ) : kernelProduct k 0 = 1 := by
  induction k with
  | zero => exact sinhKernel_zero 0
  | succ k ih => simp [kernelProduct, conv_zero, ih, sinhKernel_zero]

lemma kernelProduct_weight {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (k n : ℕ) :
    0 ≤ ((p : ℤ)-1) * padicValRat p (kernelProduct k n) + 2*n := by
  induction k generalizing n with
  | zero => exact sinhKernel_weight hp2 0 n
  | succ k ih =>
    apply conv_weight ((p : ℤ)-1) (by have := hp.out.two_le; omega)
    · intro i; exact kernelProduct_pos k i
    · intro i; exact sinhKernel_pos (k+1) i
    · intro i; exact ih i
    · intro i; exact sinhKernel_weight hp2 (k+1) i

lemma sinhKernel_integral_below {p r : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hpr : 2*r=p-1) (i n : ℕ) (hn : n < r) : IntegralAt p (sinhKernel i n) := by
  have hlt : 2*n+1 < p := by have := hp.out.two_le; omega
  have hnot : ¬p ∣ (2*n+1).factorial := by
    exact (hp.out.dvd_factorial).not.mpr (by omega)
  unfold IntegralAt
  rw [sinhKernel_val hp2, padicValNat.eq_zero_of_not_dvd hnot]
  omega

lemma kernelProduct_integral_below {p r : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hpr : 2*r=p-1) (k n : ℕ) (hn : n < r) : IntegralAt p (kernelProduct k n) := by
  induction k generalizing n with
  | zero => exact sinhKernel_integral_below hp2 hpr 0 n hn
  | succ k ih =>
    exact conv_integral_below _ _ r (fun i hi => ih i hi)
      (fun i hi => sinhKernel_integral_below hp2 hpr (k+1) i hi) n hn

lemma kernelProduct_small_weight {p r : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hpr : 2*r=p-1) (k n : ℕ) (hn0 : 0 < n) (hn : n < r) :
    0 < ((p : ℤ)-1) * padicValRat p (kernelProduct k n) + 2*n := by
  have hv := kernelProduct_integral_below hp2 hpr k n hn
  unfold IntegralAt at hv
  have hp1 : 0 ≤ (p : ℤ)-1 := by have := hp.out.two_le; omega
  have hm := mul_nonneg hp1 hv
  have hnint : (0 : ℤ) < n := by exact_mod_cast hn0
  linarith


lemma conv_decompose (a b : ℕ → ℚ) (r : ℕ) (hr : 0 < r)
    (ha0 : a 0=1) (hb0 : b 0=1) :
    conv a b r = a r + b r +
      ∑ i ∈ range (r-1), a (i+1) * b (r-(i+1)) := by
  cases r with
  | zero => omega
  | succ t =>
    rw [conv, sum_range_succ, sum_range_succ']
    simp only [Nat.sub_zero, Nat.sub_self, ha0, hb0, one_mul, mul_one,
      Nat.add_sub_cancel]
    ring

/-- Only the single-factor contributions can carry a denominator at degree p-1. -/
lemma kernelProduct_critical_error {p r : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hr : 0 < r) (hpr : 2*r=p-1) (k : ℕ) :
    IntegralAt p (kernelProduct k r - ∑ i ∈ range (k+1), sinhKernel i r) := by
  induction k with
  | zero => simp [kernelProduct, IntegralAt]
  | succ k ih =>
    have hcross : IntegralAt p
        (∑ i ∈ range (r-1), kernelProduct k (i+1) * sinhKernel (k+1) (r-(i+1))) := by
      apply integralAt_sum
      intro i hi
      have hi' := mem_range.mp hi
      have hi0 : i+1 < r := by omega
      have hisub : r-(i+1) < r := by omega
      exact integralAt_mul (kernelProduct_integral_below hp2 hpr k (i+1) hi0)
        (sinhKernel_integral_below hp2 hpr (k+1) (r-(i+1)) hisub)
    have heq := conv_decompose (kernelProduct k) (sinhKernel (k+1)) r hr
      (kernelProduct_zero k) (sinhKernel_zero (k+1))
    change IntegralAt p (conv (kernelProduct k) (sinhKernel (k+1)) r - _)
    rw [heq, sum_range_succ]
    convert integralAt_add ih hcross using 1 <;> ring


lemma prime_factorial_valuation (p : ℕ) [hp : Fact p.Prime] :
    padicValNat p p.factorial = 1 := by
  have hlo := one_le_padicValNat_of_dvd (Nat.factorial_ne_zero p)
    ((hp.out.dvd_factorial).mpr (le_refl p))
  have hhi := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p hp.out.ne_zero
  have hp2 := hp.out.two_le
  have hpred : p-1+1=p := by omega
  nlinarith

lemma critical_numerator_not_dvd {p r : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hpr : 2*r=p-1) :
    ¬ p ∣ ∑ i ∈ range (p-1), 2^(i*(2*r)) := by
  have hnot : ¬p ∣ 2 := by
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h)
  have h2 : (2 : ZMod p) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using (ZMod.natCast_eq_zero_iff 2 p).not.mpr hnot
  have hfermat := ZMod.pow_card_sub_one_eq_one h2
  have hpow (i : ℕ) : (2 : ZMod p)^(i*(2*r)) = 1 := by
    rw [hpr, Nat.mul_comm i (p-1), pow_mul, hfermat, one_pow]
  have hsum : ((∑ i ∈ range (p-1), 2^(i*(2*r)) : ℕ) : ZMod p) = -1 := by
    push_cast
    simp only [hpow, sum_const, card_range, nsmul_eq_mul, mul_one]
    rw [Nat.cast_sub (by have := hp.out.two_le; omega), ZMod.natCast_self,
      Nat.cast_one, zero_sub]
  intro hd
  have hz := (ZMod.natCast_eq_zero_iff _ p).mpr hd
  rw [hsum] at hz
  exact one_ne_zero (neg_eq_zero.mp hz)

/-- The iterated kernel has valuation exactly -1 in its first possible pole degree. -/
lemma kernelProduct_critical_val {p r : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hr : 0 < r) (hpr : 2*r=p-1) :
    padicValRat p (kernelProduct (p-2) r) = -1 := by
  let S : ℕ := ∑ i ∈ range (p-1), 2^(i*(2*r))
  have hSnot : ¬p ∣ S := critical_numerator_not_dvd hp2 hpr
  have hS0 : S ≠ 0 := by intro h; exact hSnot (h ▸ dvd_zero p)
  have hp1 : 2*r+1=p := by have := hp.out.two_le; omega
  have hk : p-2+1=p-1 := by have := hp.out.two_le; omega
  have hsingle : (∑ i ∈ range (p-2+1), sinhKernel i r) =
      (S : ℚ) / (p.factorial : ℚ) := by
    simp only [sinhKernel, hp1, hk, div_eq_mul_inv]
    rw [← sum_mul]
    congr 1
    simp [S]
  let q : ℚ := (S : ℚ) / (p.factorial : ℚ)
  let R : ℚ := kernelProduct (p-2) r - q
  have hR : IntegralAt p R := by
    have h := kernelProduct_critical_error hp2 hr hpr (p-2)
    rw [hsingle] at h
    exact h
  have hq : padicValRat p q = -1 := by
    dsimp [q]
    rw [padicValRat.div (by exact_mod_cast hS0) (by positivity),
      padicValRat.of_nat, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hSnot,
      prime_factorial_valuation]
    norm_num
  have heq : kernelProduct (p-2) r = q+R := by dsimp [R]; ring
  rw [heq]
  by_cases hR0 : R=0
  · simpa [hR0] using hq
  · have hq0 : q ≠ 0 := by intro h; simp [h] at hq
    have hsum0 : q+R ≠ 0 := by rw [← heq]; exact ne_of_gt (kernelProduct_pos _ _)
    rw [padicValRat.add_eq_of_lt hsum0 hq0 hR0 (by unfold IntegralAt at hR; omega)]
    exact hq

end FabiusProofLane



```

### `DilationSeries.lean`

```lean
import KernelCoefficients
import Mathlib.RingTheory.PowerSeries.Basic

namespace FabiusProofLane
open Finset PowerSeries

noncomputable def seqSeries (a : ℕ → ℚ) : PowerSeries ℚ := PowerSeries.mk a

lemma seqSeries_coeff (a : ℕ → ℚ) (n : ℕ) : coeff n (seqSeries a)=a n := by
  simp [seqSeries]

lemma seqSeries_conv (a b : ℕ → ℚ) : seqSeries (conv a b)=seqSeries a * seqSeries b := by
  ext n
  simp only [seqSeries_coeff, PowerSeries.coeff_mul, conv]
  exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a i * b j) n).symm

lemma seqSeries_kernel_rescale (i : ℕ) :
    seqSeries (sinhKernel i) = rescale ((4 : ℚ)^i) (seqSeries (sinhKernel 0)) := by
  ext n
  simp only [seqSeries_coeff, coeff_rescale, sinhKernel, zero_mul, pow_zero, one_div]
  have hpow : (2 : ℚ)^(i*(2*n)) = ((4 : ℚ)^i)^n := by
    rw [show (4 : ℚ)=2^2 by norm_num, ← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [hpow, div_eq_mul_inv]

/-- Dilation identity from a coefficient recurrence; no analytic assumptions. -/
lemma dilation_of_recurrence (a : ℕ → ℚ)
    (hrec : ∀ n, 0 < n → ((4 : ℚ)^n-1)*a n =
      ∑ i ∈ range n, sinhKernel 0 (i+1) * a (n-(i+1))) :
    rescale (4 : ℚ) (seqSeries a) = seqSeries (sinhKernel 0) * seqSeries a := by
  ext n
  rw [coeff_rescale, seqSeries_coeff, ← seqSeries_conv, seqSeries_coeff]
  cases n with
  | zero => simp [conv, sinhKernel]
  | succ n =>
    have h := hrec (n+1) (by omega)
    rw [conv, sum_range_succ']
    simp only [sinhKernel_zero, Nat.sub_zero, one_mul]
    linarith

/-- Iterating the basic dilation supplies the actual finite product used in the proof. -/
lemma iterated_dilation (a : ℕ → ℚ)
    (hbase : rescale (4 : ℚ) (seqSeries a) =
      seqSeries (sinhKernel 0) * seqSeries a) (k : ℕ) :
    rescale ((4 : ℚ)^(k+1)) (seqSeries a) =
      seqSeries (kernelProduct k) * seqSeries a := by
  induction k with
  | zero => simpa [kernelProduct] using hbase
  | succ k ih =>
    rw [pow_succ', rescale_mul, RingHom.comp_apply, hbase, map_mul]
    rw [← seqSeries_kernel_rescale (k+1), ih, ← mul_assoc, mul_comm
      (seqSeries (sinhKernel (k+1))) (seqSeries (kernelProduct k)), ← seqSeries_conv]
    rfl

lemma iterated_coefficient_recurrence (a : ℕ → ℚ)
    (hrec : ∀ n, 0 < n → ((4 : ℚ)^n-1)*a n =
      ∑ i ∈ range n, sinhKernel 0 (i+1) * a (n-(i+1))) (k n : ℕ) :
    (((4 : ℚ)^(k+1))^n-1)*a n =
      ∑ i ∈ range n, kernelProduct k (i+1) * a (n-(i+1)) := by
  have h := congrArg (coeff n) (iterated_dilation a (dilation_of_recurrence a hrec) k)
  rw [coeff_rescale, seqSeries_coeff, ← seqSeries_conv, seqSeries_coeff,
    conv, sum_range_succ'] at h
  simp only [kernelProduct_zero, Nat.sub_zero, one_mul] at h
  linarith

end FabiusProofLane
```

### `CoefficientDenominator.lean`

```lean
import DilationSeries

namespace FabiusProofLane
open Finset

lemma dilationFactor_pos (k n : ℕ) (hn : 0 < n) :
    0 < (((4 : ℚ)^(k+1))^n-1) := by
  have h4 : (1 : ℚ) < 4^(k+1) := one_lt_pow₀ (by norm_num) (by omega)
  exact sub_pos.mpr (one_lt_pow₀ h4 (by omega))

lemma dilationFactor_val {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (n : ℕ) (hn : 0 < n) :
    1 ≤ padicValRat p (((4 : ℚ)^(p-1))^n-1) := by
  have hnot : ¬p ∣ 4 := by
    intro h
    have h2 : p ∣ 2 := hp.out.dvd_of_dvd_pow (show p ∣ 2^2 by norm_num; exact h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h2)
  have h4 : (4 : ZMod p) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using (ZMod.natCast_eq_zero_iff 4 p).not.mpr hnot
  have hfermat := ZMod.pow_card_sub_one_eq_one h4
  have hnatpos : 0 < (4^(p-1))^n-1 := by
    have hp1 : 0 < p-1 := by have := hp.out.two_le; omega
    have h := Nat.one_lt_pow hn.ne' (show 1 < 4^(p-1) from Nat.one_lt_pow hp1.ne' (by decide))
    omega
  have hdvd : p ∣ (4^(p-1))^n-1 := by
    apply (ZMod.natCast_eq_zero_iff _ p).mp
    rw [Nat.cast_sub (by omega : 1 ≤ (4^(p-1))^n), Nat.cast_pow, Nat.cast_pow,
      Nat.cast_ofNat, Nat.cast_one, hfermat, one_pow, sub_self]
  have heq : (((4^(p-1))^n-1 : ℕ) : ℚ) = ((4 : ℚ)^(p-1))^n-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ (4^(p-1))^n)]
    push_cast
    rfl
  rw [← heq, padicValRat.of_nat]
  exact_mod_cast one_le_padicValNat_of_dvd (Nat.ne_of_gt hnatpos) hdvd

/-- Section 4, including all actual sinh-kernel coefficient estimates.

The sole recurrence premise is exactly E(2z)=(sinh z/z)E(z), written on
its even coefficient indices. The theorem is not yet the dyadic lcm endpoint.
-/
theorem coefficient_denominator_witness {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (a : ℕ → ℚ) (ha0 : a 0=1) (ha : ∀ n, 0 < a n)
    (hrec : ∀ n, 0 < n → ((4 : ℚ)^n-1)*a n =
      ∑ i ∈ range n, sinhKernel 0 (i+1) * a (n-(i+1))) (N : ℕ) :
    ∃ j, 2*j ≤ N ∧ (padicValNat p (N+1).factorial : ℤ) ≤ -padicValRat p (a j) := by
  have hodd : Odd p := (Nat.odd_iff).mpr (hp.out.eq_two_or_odd.resolve_left hp2)
  obtain ⟨r, hrp⟩ := hodd
  have hr : 0 < r := by have := hp.out.two_le; omega
  have hpr : 2*r=p-1 := by omega
  have hk : p-2+1=p-1 := by have := hp.out.two_le; omega
  let H := kernelProduct (p-2)
  let c (n : ℕ) : ℚ := ((4 : ℚ)^(p-1))^n-1
  have hcrec (n : ℕ) (hn : 0 < n) : c n * a n =
      ∑ i ∈ range n, H (i+1) * a (n-(i+1)) := by
    simpa only [c, H, hk] using iterated_coefficient_recurrence a hrec (p-2) n
  have hfactor (n : ℕ) (hn : 0 < n) : 0 < c n := by
    dsimp [c]
    simpa only [hk] using dilationFactor_pos (p-2) n hn
  have hweight (l : ℕ) : 0 ≤ (2*(r : ℤ))*padicValRat p (H l)+2*l := by
    have hh := kernelProduct_weight hp2 (p-2) l
    have hz : (2*(r : ℤ))=(p : ℤ)-1 := by
      have hh : (p : ℤ)=2*r+1 := by exact_mod_cast hrp
      omega
    simpa only [H, hz] using hh
  have hsmall (l : ℕ) (hl0 : 0 < l) (hl : l < r) :
      0 < (2*(r : ℤ))*padicValRat p (H l)+2*l := by
    have hh := kernelProduct_small_weight hp2 hpr (p-2) l hl0 hl
    have hz : (2*(r : ℤ))=(p : ℤ)-1 := by
      have hh : (p : ℤ)=2*r+1 := by exact_mod_cast hrp
      omega
    simpa only [H, hz] using hh
  obtain ⟨j, hj, hwindow, hval⟩ := weighted_minimum_at_end hr a H c ha ha0
    (fun l => kernelProduct_pos _ _) hfactor (fun n hn => dilationFactor_val hp2 n hn)
    hweight hsmall (kernelProduct_critical_val hp2 hr hpr) hcrec (N/2)
  refine ⟨j, ?_, ?_⟩
  · have hmul := Nat.mul_le_mul_left 2 hj
    have hdiv := Nat.mul_div_le N 2
    omega
  · have hbound := denominator_bound_of_end r (N/2) j (padicValRat p (a j)) hr hwindow hval
    have hdiv : N/2/r=N/(p-1) := by rw [Nat.div_div_eq_div_mul, hpr]
    rw [hdiv] at hbound
    have hfact := factorial_valuation_le_div p N
    exact le_trans (by exact_mod_cast hfact) hbound

#print axioms coefficient_denominator_witness

end FabiusProofLane
```

### `ExplicitCoefficients.lean`

```lean
import CoefficientDenominator

namespace FabiusProofLane
open Finset

/-- The actual rational coefficient recurrence of E(z), with even indices halved. -/
def evenCoefficient : ℕ → ℚ
  | 0 => 1
  | n+1 => (∑ i : Fin (n+1), sinhKernel 0 (i.val+1) * evenCoefficient (n-i.val)) /
      ((4 : ℚ)^(n+1)-1)
termination_by n => n
decreasing_by omega

@[simp] lemma evenCoefficient_zero : evenCoefficient 0=1 := by rw [evenCoefficient]

lemma evenCoefficient_pos (n : ℕ) : 0 < evenCoefficient n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [evenCoefficient]
      apply div_pos
      · exact Finset.sum_pos (fun i _ =>
          mul_pos (sinhKernel_pos 0 (i.val+1)) (ih (n-i.val) (by omega))) Finset.univ_nonempty
      · exact sub_pos.mpr (one_lt_pow₀ (by norm_num) (by omega))

lemma evenCoefficient_recurrence (n : ℕ) (hn : 0 < n) :
    ((4 : ℚ)^n-1)*evenCoefficient n =
      ∑ i ∈ range n, sinhKernel 0 (i+1) * evenCoefficient (n-(i+1)) := by
  cases n with
  | zero => omega
  | succ n =>
    rw [evenCoefficient]
    have hne : (4 : ℚ)^(n+1)-1 ≠ 0 := by
      exact ne_of_gt (sub_pos.mpr (one_lt_pow₀ (by norm_num) (by omega)))
    rw [mul_div_cancel₀ _ hne]
    rw [Fin.sum_univ_eq_sum_range (fun i => sinhKernel 0 (i+1) * evenCoefficient (n-i)) (n+1)]
    apply sum_congr rfl
    intro i hi
    congr 2
    omega

/-- Kernel-checked new arithmetic lemma on the explicitly defined Fabius coefficients.
The semantic moment/evaluator and common-denominator bridges remain outside this theorem. -/
theorem explicit_coefficient_denominator_witness (p N : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ j, 2*j ≤ N ∧
      (padicValNat p (N+1).factorial : ℤ) ≤ -padicValRat p (evenCoefficient j) := by
  exact coefficient_denominator_witness hp2 evenCoefficient evenCoefficient_zero
    evenCoefficient_pos evenCoefficient_recurrence N

#print axioms explicit_coefficient_denominator_witness

end FabiusProofLane
```

### `UpstreamArithmetic.lean`

```lean
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Order.Interval.Finset.Nat

/-!
# Exact arithmetic attached to the Fabius function

This file keeps the arithmetic part of Arias de Reyna's paper in `ℚ` and `ℕ`.
In particular, no denominator or `p`-adic valuation is ever taken of a real
number.  Later analytic theorems connect these exact quantities to the bounded
Fabius function and to Rvachev's `up` function.

The definitions follow equations (10), (19), (27), and (32) of
*Arithmetic of the Fabius function* (arXiv:1702.06487v3).  The exponent in the
definition of `reshetnikov` is the positive exponent appearing in equation
(27); the arXiv abstract has a sign typo.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

/-! ### Triangular numbers

`Nat.choose n 2` is the `n`-th triangular number, and it appears throughout
this development as the exponent of a power of two: in `dyadicScale`, in the
Thue--Morse block weights, in the flatness constants `2 ^ C(n+1,2)`, and in
every q-binomial formula.  The step and square identities below were
previously re-proved privately in ten places under ten different names; they
are stated once here because `Arithmetic` is the only module every consumer
already imports. -/

/-- The triangular step identity: `C(n+1, 2) = C(n, 2) + n`.

This is `Nat.choose_succ_succ` followed by `Nat.choose_one_right`, but it is
used often enough, and in enough modules that share no ancestor but this one,
to deserve a name. -/
theorem choose_succ_two (n : ℕ) :
    (n + 1).choose 2 = n.choose 2 + n := by
  rw [show n + 1 = Nat.succ n by omega, Nat.choose_succ_succ]
  simp [Nat.choose_one_right, add_comm]

/-- Twice a triangular number plus its index is a square:
`2 * C(n, 2) + n = n ^ 2`.

Equivalently `C(n, 2) = n(n-1)/2`, stated without natural subtraction or
division so that it can be transported into any semiring by `push_cast`. -/
theorem two_mul_choose_two_add (n : ℕ) :
    2 * n.choose 2 + n = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : 2 * (n + 1).choose 2 + (n + 1)
          = (2 * n.choose 2 + n) + (2 * n + 1) := by
        rw [choose_succ_two]
        ring
      rw [hstep, ih]
      ring

/-- A natural-number square splits into two adjacent second binomial coefficients. -/
theorem choose_square_split (n : ℕ) :
    n * n = (n + 1).choose 2 + n.choose 2 := by
  rw [choose_succ_two]
  calc
    n * n = n ^ 2 := by ring
    _ = 2 * n.choose 2 + n := (two_mul_choose_two_add n).symm
    _ = (n.choose 2 + n) + n.choose 2 := by ring

/-- The shifted form of `choose_succ_two`, stated at `n + 2` because several
dyadic recursions index their blocks from one rather than zero. -/
theorem choose_add_two_two (n : ℕ) :
    (n + 2).choose 2 = (n + 1).choose 2 + (n + 1) :=
  choose_succ_two (n + 1)

/-- The sum of the binary digits of `n`, denoted `w(n)` in the paper. -/
def binaryWeight (n : ℕ) : ℕ :=
  (Nat.digits 2 n).sum

/-- The Thue--Morse sign `(-1)^w(n)`. -/
def thueMorseSign (n : ℕ) : ℤ :=
  (-1) ^ binaryWeight n

/-- The product `∏_{j=a}^{b-1} (2j+1)`. -/
def oddFactorProduct (a b : ℕ) : ℕ :=
  ∏ j ∈ Ico a b, (2 * j + 1)

/-- The product `∏_{j=a}^{b-1} (2^j-1)`. -/
def mersenneIntervalProduct (a b : ℕ) : ℕ :=
  ∏ j ∈ Ico a b, (2 ^ j - 1)

/-- The product `1 * 3 * ... * (2n - 1)`, with value `1` at `n = 0`. -/
def oddDoubleFactorial (n : ℕ) : ℕ :=
  ∏ k ∈ range n, (2 * k + 1)

/-- Split `(2n)!` into its even and odd factors. -/
theorem factorial_two_mul_eq (n : ℕ) :
    (2 * n).factorial = 2 ^ n * n.factorial * oddDoubleFactorial n := by
  induction n with
  | zero => simp [oddDoubleFactorial]
  | succ n ih =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
        Nat.factorial_succ (2 * n + 1), Nat.factorial_succ (2 * n), ih,
        pow_succ, Nat.factorial_succ n]
      simp only [oddDoubleFactorial, Finset.prod_range_succ]
      ring

/-- The product `∏_{k=1}^n (2^k - 1)`. -/
def mersenneProduct (n : ℕ) : ℕ :=
  ∏ k ∈ range n, (2 ^ (k + 1) - 1)

/-- The product `∏_{k=1}^n (2^(2k) - 1)`. -/
def evenMersenneProduct (n : ℕ) : ℕ :=
  ∏ k ∈ range n, (2 ^ (2 * (k + 1)) - 1)

/-- The product `∏_{k=0}^n (2^(2k+1) - 1)`. -/
def oddMersenneProduct (n : ℕ) : ℕ :=
  ∏ k ∈ range (n + 1), (2 ^ (2 * k + 1) - 1)

/-! ### Structural facts about the normalization products -/

/-- Append the final odd factor to an odd double factorial. -/
theorem oddDoubleFactorial_succ (n : ℕ) :
    oddDoubleFactorial (n + 1) = oddDoubleFactorial n * (2 * n + 1) := by
  simp [oddDoubleFactorial, Finset.prod_range_succ]

/-- Append the final factor to the ordinary Mersenne product. -/
theorem mersenneProduct_succ_eq (n : ℕ) :
    mersenneProduct (n + 1) = mersenneProduct n * (2 ^ (n + 1) - 1) := by
  simp [mersenneProduct, Finset.prod_range_succ]

/-- Append the final factor to the even-indexed Mersenne product. -/
theorem evenMersenneProduct_succ_eq (n : ℕ) :
    evenMersenneProduct (n + 1) =
      evenMersenneProduct n * (2 ^ (2 * (n + 1)) - 1) := by
  simp [evenMersenneProduct, Finset.prod_range_succ]

/-- Append the final factor to the odd-indexed Mersenne product. -/
theorem oddMersenneProduct_succ_eq (n : ℕ) :
    oddMersenneProduct (n + 1) =
      oddMersenneProduct n * (2 ^ (2 * (n + 1) + 1) - 1) := by
  simp [oddMersenneProduct, Finset.prod_range_succ]

/-- Odd double factorials are positive, including the empty product. -/
theorem oddDoubleFactorial_pos (n : ℕ) : 0 < oddDoubleFactorial n := by
  unfold oddDoubleFactorial
  exact Finset.prod_pos fun k _ => by omega

/-- Ordinary Mersenne products are positive, including the empty product. -/
theorem mersenneProduct_pos (n : ℕ) : 0 < mersenneProduct n := by
  unfold mersenneProduct
  apply Finset.prod_pos
  intro k hk
  exact Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) (by omega))

/-- Even-indexed Mersenne products are positive, including the empty product. -/
theorem evenMersenneProduct_pos (n : ℕ) : 0 < evenMersenneProduct n := by
  unfold evenMersenneProduct
  apply Finset.prod_pos
  intro k hk
  exact Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) (by omega))

/-- Odd-indexed Mersenne products are positive. -/
theorem oddMersenneProduct_pos (n : ℕ) : 0 < oddMersenneProduct n := by
  unfold oddMersenneProduct
  apply Finset.prod_pos
  intro k hk
  exact Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) (by omega))

/-- A finite product of odd natural numbers is odd. -/
theorem finset_prod_odd {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, Odd (f i)) : Odd (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (hf a (by simp)).mul (ih (by
        intro i hi
        exact hf i (by simp [hi])))

/-- A positive power of two minus one is odd. -/
theorem two_pow_sub_one_odd {e : ℕ} (he : 0 < e) : Odd (2 ^ e - 1) := by
  apply Nat.Even.sub_odd Nat.one_le_two_pow
  · exact Nat.even_pow.mpr ⟨even_two, Nat.ne_of_gt he⟩
  · exact odd_one

/-- Every odd double factorial is odd. -/
theorem odd_oddDoubleFactorial (n : ℕ) : Odd (oddDoubleFactorial n) := by
  unfold oddDoubleFactorial
  apply finset_prod_odd
  intro k hk
  exact odd_two_mul_add_one k

/-- Every ordinary Mersenne product is odd. -/
theorem odd_mersenneProduct (n : ℕ) : Odd (mersenneProduct n) := by
  unfold mersenneProduct
  apply finset_prod_odd
  intro k hk
  exact two_pow_sub_one_odd (by omega)

/-- Every even-indexed Mersenne product is odd. -/
theorem odd_evenMersenneProduct (n : ℕ) : Odd (evenMersenneProduct n) := by
  unfold evenMersenneProduct
  apply finset_prod_odd
  intro k hk
  exact two_pow_sub_one_odd (by omega)

/-- Every odd-indexed Mersenne product is odd. -/
theorem odd_oddMersenneProduct (n : ℕ) : Odd (oddMersenneProduct n) := by
  unfold oddMersenneProduct
  apply finset_prod_odd
  intro k hk
  exact two_pow_sub_one_odd (by omega)

/-- A rational number is the image of a natural number. -/
def IsNatural (q : ℚ) : Prop :=
  ∃ m : ℕ, q = m

/-- A rational number is the image of an odd natural number. -/
def IsOddNatural (q : ℚ) : Prop :=
  ∃ m : ℕ, Odd m ∧ q = m

/-! ### Odd reduced denominators -/

/-- The sum of rationals with odd reduced denominators again has odd reduced
denominator. -/
theorem rat_den_add_odd {q r : ℚ} (hq : Odd q.den) (hr : Odd r.den) :
    Odd (q + r).den :=
  (hq.mul hr).of_dvd_nat (Rat.add_den_dvd q r)

/-- The product of rationals with odd reduced denominators again has odd
reduced denominator. -/
theorem rat_den_mul_odd {q r : ℚ} (hq : Odd q.den) (hr : Odd r.den) :
    Odd (q * r).den :=
  (hq.mul hr).of_dvd_nat (Rat.mul_den_dvd q r)

/-- A finite sum of rationals with odd reduced denominators has odd reduced
denominator. -/
theorem rat_den_sum_odd {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, Odd (f i).den) : Odd (∑ i ∈ s, f i).den := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      apply rat_den_add_odd (hf a (by simp))
      exact ih (by
        intro i hi
        exact hf i (by simp [hi]))

/-- Dividing by an odd natural preserves oddness of the reduced denominator. -/
theorem rat_den_div_nat_odd (q : ℚ) (d : ℕ)
    (hq : Odd q.den) (hd : Odd d) : Odd (q / (d : ℚ)).den := by
  rw [div_eq_mul_inv]
  apply rat_den_mul_odd hq
  rw [Rat.inv_natCast_den_of_pos hd.pos]
  exact hd

/-- The reduced denominator of a quotient of natural numbers divides its
displayed denominator. -/
theorem rat_den_dvd_nat_div (a b : ℕ) :
    ((a : ℚ) / (b : ℚ)).den ∣ b := by
  have hInt :
      ((((a : ℚ) / (b : ℚ)).den : ℕ) : ℤ) ∣ (b : ℤ) := by
    rw [Rat.natCast_div_eq_divInt]
    exact Rat.den_dvd a b
  exact_mod_cast hInt

/-- If multiplication by a natural number makes a rational integral, then
the rational's reduced denominator divides that natural number.  The
statement includes the zero multiplier, where divisibility is automatic. -/
theorem rat_den_dvd_of_mul_nat_eq_int {q : ℚ} {B : ℕ} {z : ℤ}
    (h : q * (B : ℚ) = (z : ℚ)) : q.den ∣ B := by
  by_cases hB : B = 0
  · subst B
    exact dvd_zero _
  have hBq : (B : ℚ) ≠ 0 := by exact_mod_cast hB
  have hq : q = (z : ℚ) / (B : ℚ) := (eq_div_iff hBq).2 h
  have hdivInt : q = Rat.divInt z (B : ℤ) := by
    rw [hq, Rat.divInt_eq_div]
    norm_num
  have hdvdInt : (q.den : ℤ) ∣ (B : ℤ) := by
    rw [hdivInt]
    exact Rat.den_dvd z B
  exact_mod_cast hdvdInt

/--
The rational moment sequence `c_n`, defined by the recurrence in equation
(10).  Strong recursion makes the recurrence itself the executable
specification and keeps later arithmetic proofs independent of integration.
-/
def moment : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
      (∑ k : Fin (n + 1),
          (Nat.choose (2 * (n + 1) + 1) (2 * k.val) : ℚ) * moment k.val) /
        (((2 * (n + 1) + 1 : ℕ) : ℚ) * ((2 : ℚ) ^ (2 * (n + 1)) - 1))
termination_by n => n
decreasing_by exact k.isLt

/--
The rational half-moment sequence `d_n`, defined by equation (19).
-/
def halfMoment : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
      (∑ k : Fin (n + 1), (Nat.choose (n + 2) k.val : ℚ) * halfMoment k.val) /
        (((n + 2 : ℕ) : ℚ) * ((2 : ℚ) ^ (n + 1) - 1))
termination_by n => n
decreasing_by exact k.isLt

/-- The zeroth moment is one: the recursion starts from the total mass of
the Fabius density. -/
@[simp]
theorem moment_zero : moment 0 = 1 := by
  rw [moment]

/-- The zeroth half-moment is one, by the same normalization as
`moment_zero`. -/
@[simp]
theorem halfMoment_zero : halfMoment 0 = 1 := by
  rw [halfMoment]

/-- The recurrence equation for a positive-index moment. -/
theorem moment_succ (n : ℕ) :
    moment (n + 1) =
      (∑ k : Fin (n + 1),
        (Nat.choose (2 * (n + 1) + 1) (2 * k.val) : ℚ) * moment k.val) /
        (((2 * (n + 1) + 1 : ℕ) : ℚ) * ((2 : ℚ) ^ (2 * (n + 1)) - 1)) := by
  rw [moment]

/-- The recurrence equation for a positive-index half moment. -/
theorem halfMoment_succ (n : ℕ) :
    halfMoment (n + 1) =
      (∑ k : Fin (n + 1),
        (Nat.choose (n + 2) k.val : ℚ) * halfMoment k.val) /
        (((n + 2 : ℕ) : ℚ) * ((2 : ℚ) ^ (n + 1) - 1)) := by
  rw [halfMoment]

/-- Every recursively defined half moment is strictly positive. -/
theorem halfMoment_pos (n : ℕ) : 0 < halfMoment n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => norm_num
      | succ n =>
          rw [halfMoment_succ]
          apply div_pos
          · apply Finset.sum_pos
            · intro k hk
              exact mul_pos (by
                exact_mod_cast Nat.choose_pos (by omega : k.val ≤ n + 2))
                (ih k.val k.isLt)
            · exact ⟨0, Finset.mem_univ _⟩
          · exact mul_pos (by positivity) (sub_pos.mpr
              (one_lt_pow₀ (a := (2 : ℚ)) (by norm_num) (by omega)))

/--
The natural sequence `F_n` from Proposition 1.  This is the integral recurrence
(13), with quotients of double factorials replaced by interval products.
-/
def momentNumerator : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      ∑ k : Fin (n + 1),
        momentNumerator k.val * Nat.choose (2 * (n + 1) + 1) (2 * k.val) *
          oddFactorProduct (k.val + 1) (n + 1) *
          (∏ j ∈ Ico (k.val + 1) (n + 1), (2 ^ (2 * j) - 1))
termination_by n => n
decreasing_by exact k.isLt

/-- The division-free recurrence defining `F_(n+1)`. -/
theorem momentNumerator_succ (n : ℕ) :
    momentNumerator (n + 1) =
      ∑ k : Fin (n + 1),
        momentNumerator k.val * Nat.choose (2 * (n + 1) + 1) (2 * k.val) *
          oddFactorProduct (k.val + 1) (n + 1) *
          (∏ j ∈ Ico (k.val + 1) (n + 1), (2 ^ (2 * j) - 1)) := by
  rw [momentNumerator]

/--
The natural sequence `G_n` from Proposition 4, defined by the recurrence in
its proof.  Factorial quotients are represented by interval products.
-/
def halfMomentNumerator : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      ∑ k : Fin (n + 1),
        halfMomentNumerator k.val * Nat.choose (n + 2) k.val *
          (∏ j ∈ Ico (k.val + 2) (n + 2), j) *
          mersenneIntervalProduct (k.val + 1) (n + 1)
termination_by n => n
decreasing_by exact k.isLt

/-- The division-free recurrence defining `G_(n+1)`. -/
theorem halfMomentNumerator_succ (n : ℕ) :
    halfMomentNumerator (n + 1) =
      ∑ k : Fin (n + 1),
        halfMomentNumerator k.val * Nat.choose (n + 2) k.val *
          (∏ j ∈ Ico (k.val + 2) (n + 2), j) *
          mersenneIntervalProduct (k.val + 1) (n + 1) := by
  rw [halfMomentNumerator]

/-- The exact rational value corresponding to `F(2⁻ⁿ)`, from equation (22). -/
def halfMomentFabiusValue (n : ℕ) : ℚ :=
  halfMoment n / ((n.factorial : ℚ) * (2 : ℚ) ^ n.choose 2)

/--
Equation (32): the exact rational value of `F(a / 2^n)`.

The analytic bridge is stated for `a ≤ 2^n`.  The formula itself is useful for
exact computation and is total on natural inputs.
-/
def fabiusDyadic (n a : ℕ) : ℚ :=
  (2 : ℚ) ^ (-(Nat.choose (n + 1) 2 : ℤ)) / n.factorial *
    ∑ h : Fin a, (thueMorseSign h.val : ℚ) *
      ∑ k : Fin (n / 2 + 1),
        (Nat.choose n (2 * k.val) : ℚ) *
          ((2 : ℚ) * a - 2 * h.val - 1) ^ (n - 2 * k.val) * moment k.val

/-- The exact rational value corresponding to `F(2⁻ⁿ)`. -/
def fabiusAtInverseTwoPow (n : ℕ) : ℚ :=
  fabiusDyadic n 1

/-! ## Executable evaluation at arbitrary dyadic arguments -/

/--
The table `[F(1), F(1/2), ..., F(2⁻ⁿ)]`, computed by the recurrence used in
Reshetnikov's exact evaluator.

Keeping the already-computed prefix in an array avoids the repeated unfolding
of `halfMoment` that a direct recursive implementation would perform.
-/
def fabiusInversePowTwoTable : (n : ℕ) → Array ℚ
  | 0 => #[1]
  | n + 1 =>
      let previous := fabiusInversePowTwoTable n
      previous.push <|
        (∑ k : Fin (n + 1),
            (previous[k.val]?).getD 0 /
              ((2 : ℚ) ^ ((n + 1).choose 2 - k.val.choose 2) *
                ((n + 1 - k.val + 1).factorial : ℚ))) /
          ((2 : ℚ) ^ (n + 1) - 1)

/-- Read an inverse-power value from a precomputed table. -/
def fabiusInversePowTwoTableValue (values : Array ℚ) (n : ℕ) : ℚ :=
  (values[n]?).getD 0

/--
Horner evaluation of the Taylor polynomial about `2⁻ᵒʳᵈᵉʳ` used in
Proposition 10.  A table containing at least the entries through `order` is
expected; the public evaluator below always supplies such a table.
-/
def fabiusTaylorHorner (values : Array ℚ) (order : ℕ) (offset : ℚ) : ℚ :=
  let rec go : ℕ → ℚ
    | 0 => 1
    | m + 1 =>
        fabiusInversePowTwoTableValue values (m + 1) +
          ((2 : ℚ) ^ (order - m) * offset / (order - m)) * go m
  go order

/--
The bit-recursive core of the exact dyadic evaluator on `[0,1]`.

At every recursive call the highest set bit of `numerator` is removed.  Thus
evaluation terminates after at most the number of set bits in the numerator,
instead of summing over every smaller numerator as equation (32) does.
Numerators at or above `2^exponent` are clamped to `1`.
-/
def fabiusDyadicUnitAux (values : Array ℚ) (exponent : ℕ) : ℕ → ℚ
  | 0 => 0
  | a + 1 =>
      if 2 ^ exponent ≤ a + 1 then
        1
      else
        let leadingExponent := Nat.log2 (a + 1)
        let order := exponent - leadingExponent
        let remainder := a + 1 - 2 ^ leadingExponent
        let offset := (remainder : ℚ) / (2 : ℚ) ^ exponent
        fabiusTaylorHorner values order offset -
          fabiusDyadicUnitAux values exponent remainder
termination_by a => a
decreasing_by
  apply Nat.sub_lt (Nat.zero_lt_succ a)
  positivity

/-- Exact bounded Fabius value at the natural dyadic `numerator / 2^exponent`. -/
def fabiusDyadicUnit (exponent numerator : ℕ) : ℚ :=
  if numerator = 0 then
    0
  else if 2 ^ exponent ≤ numerator then
    1
  else
    fabiusDyadicUnitAux (fabiusInversePowTwoTable exponent) exponent numerator

/--
Compute the bounded/CDF Fabius function exactly at any signed dyadic argument
`numerator / 2^exponent`.

This is the principal total evaluator for the project's convention: values at
nonpositive arguments are `0`, values at arguments at least `1` are `1`, and
the interior is evaluated by Reshetnikov's terminating Taylor recursion.
-/
def fabiusDyadicValue (exponent : ℕ) (numerator : ℤ) : ℚ :=
  if numerator ≤ 0 then 0 else fabiusDyadicUnit exponent numerator.toNat

/-- The exact dyadic evaluator vanishes at numerator zero, matching
`F 0 = 0`. -/
@[simp]
theorem fabiusDyadicUnit_zero (exponent : ℕ) :
    fabiusDyadicUnit exponent 0 = 0 := by
  simp [fabiusDyadicUnit]

/-- Above the unit interval the exact dyadic evaluator is constant `1`.
The hypothesis is on the numerator, so `2 ^ exponent ≤ numerator` says the
argument `numerator / 2 ^ exponent` is at least one. -/
theorem fabiusDyadicUnit_of_ge (exponent numerator : ℕ)
    (h : 2 ^ exponent ≤ numerator) :
    fabiusDyadicUnit exponent numerator = 1 := by
  simp [fabiusDyadicUnit, h, Nat.ne_of_gt (lt_of_lt_of_le (by positivity) h)]

/-- The signed-numerator evaluator vanishes at zero. -/
@[simp]
theorem fabiusDyadicValue_zero (exponent : ℕ) :
    fabiusDyadicValue exponent 0 = 0 := by
  simp [fabiusDyadicValue]

/-- The bounded dyadic evaluator is zero on the whole left half line, not
merely at the origin: a nonpositive numerator is sent to `0` by definition,
matching the convention `F x = 0` for `x ≤ 0`. -/
theorem fabiusDyadicValue_of_nonpos (exponent : ℕ) (numerator : ℤ)
    (h : numerator ≤ 0) :
    fabiusDyadicValue exponent numerator = 0 := by
  simp [fabiusDyadicValue, h]

/-- The bounded dyadic evaluator is constant `1` to the right of the unit
interval.  This is where it parts company with `extendedFabiusDyadicValue`,
which continues by reflection and the Thue--Morse sign instead. -/
theorem fabiusDyadicValue_of_ge (exponent : ℕ) (numerator : ℤ)
    (h : (2 ^ exponent : ℤ) ≤ numerator) :
    fabiusDyadicValue exponent numerator = 1 := by
  have hpos : 0 < numerator := lt_of_lt_of_le (by positivity) h
  have hnat : 2 ^ exponent ≤ numerator.toNat := by
    apply (Int.le_toNat hpos.le).2
    simpa using h
  simp [fabiusDyadicValue, fabiusDyadicUnit, not_le_of_gt hpos, hnat]

/--
Compute the paper's signed global extension exactly at any dyadic argument.

Positive arguments are reduced to `[0,1]` using the triangular reduction
modulo `2` and the Thue--Morse sign.  Nonpositive arguments are `0`.  This is
separate from `fabiusDyadicValue`, since the bounded function is instead
constant `1` to the right of the unit interval.
-/
def extendedFabiusDyadicValue (exponent : ℕ) (numerator : ℤ) : ℚ :=
  if numerator ≤ 0 then
    0
  else
    let scale := 2 ^ exponent
    let period := 2 * scale
    let naturalNumerator := numerator.toNat
    let block := naturalNumerator / period
    let residue := naturalNumerator % period
    let coreNumerator := if residue ≤ scale then residue else period - residue
    (thueMorseSign block : ℚ) * fabiusDyadicUnit exponent coreNumerator

/-- The signed global evaluator vanishes at zero. -/
@[simp]
theorem extendedFabiusDyadicValue_zero (exponent : ℕ) :
    extendedFabiusDyadicValue exponent 0 = 0 := by
  simp [extendedFabiusDyadicValue]

/-- The signed global evaluator is zero on the whole left half line.  Unlike
`fabiusDyadicValue_of_ge`, there is no companion statement to the right: the
signed extension is not eventually constant, it is quasi-periodic. -/
theorem extendedFabiusDyadicValue_of_nonpos (exponent : ℕ) (numerator : ℤ)
    (h : numerator ≤ 0) :
    extendedFabiusDyadicValue exponent numerator = 0 := by
  simp [extendedFabiusDyadicValue, h]

/-- A rational is dyadic when its reduced denominator is a power of two. -/
def IsDyadicRational (x : ℚ) : Prop :=
  ∃ exponent : ℕ, x.den = 2 ^ exponent

/--
Return the denominator exponent when a reduced rational is dyadic.

For example, the exponent of `5/16` is `4`; a non-dyadic rational such as
`2/3` returns `none`.
-/
def dyadicExponent? (x : ℚ) : Option ℕ :=
  let exponent := x.den.log2
  if x.den = 2 ^ exponent then some exponent else none

/--
Evaluate the bounded Fabius function on a rational input when it is dyadic.
The result is an explicit reduced rational; `none` certifies that the input's
reduced denominator is not a power of two.
-/
def evalFabiusDyadic (x : ℚ) : Option ℚ :=
  match dyadicExponent? x with
  | none => none
  | some exponent => some (fabiusDyadicValue exponent x.num)

/-- Rational-input wrapper for the signed global dyadic evaluator. -/
def evalExtendedFabiusDyadic (x : ℚ) : Option ℚ :=
  match dyadicExponent? x with
  | none => none
  | some exponent => some (extendedFabiusDyadicValue exponent x.num)

/--
The exact value of `up(a / 2^n)` for an integer numerator.  Evenness reduces
negative arguments to nonnegative ones; values outside the support are zero.
The absolute value records the nonnegative codomain of Rvachev's function in
the exact representation.  The analytic bridge proves it is extensionally
redundant whenever a bounded Fabius function is supplied.
-/
def rvachevDyadic (n : ℕ) (a : ℤ) : ℚ :=
  if a.natAbs ≤ 2 ^ n then
    |fabiusDyadic n (2 ^ n - a.natAbs)|
  else
    0

/-- Rational-input wrapper for the exact Rvachev dyadic evaluator.  It returns
`none` precisely when the reduced denominator is not a power of two. -/
def evalRvachevDyadic (x : ℚ) : Option ℚ :=
  match dyadicExponent? x with
  | none => none
  | some exponent => some (rvachevDyadic exponent x.num)

/-- The positive odd numerators at dyadic level `n`. -/
def oddDyadicNumerators (n : ℕ) : Finset ℕ :=
  (Icc 1 (2 ^ n - 1)).filter Odd

/-- Reflection about the midpoint permutes the positive odd dyadic grid. -/
theorem oddDyadicNumerators_reflect_mem (n a : ℕ) (hn : 1 ≤ n)
    (ha : a ∈ oddDyadicNumerators n) :
    2 ^ n - a ∈ oddDyadicNumerators n := by
  have ha_filter := (mem_filter.mp (show
    a ∈ (Icc 1 (2 ^ n - 1)).filter Odd by simpa [oddDyadicNumerators] using ha))
  have ha_bounds := Finset.mem_Icc.mp ha_filter.1
  have haodd := ha_filter.2
  rw [oddDyadicNumerators, mem_filter, Finset.mem_Icc]
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  apply Nat.Even.sub_odd (by omega) _ haodd
  exact Nat.even_pow.mpr ⟨even_two, by omega⟩

/-- The equivalent LCM formed from bounded Fabius values on the odd grid. -/
def fabiusDyadicDenominator (n : ℕ) : ℕ :=
  (oddDyadicNumerators n).lcm fun a => (fabiusDyadic n a).den

/--
The paper's `D_n`: the LCM of denominators of Rvachev `up` on the positive
odd level-`n` dyadic grid (Definition 12).
-/
def dyadicDenominator (n : ℕ) : ℕ :=
  (oddDyadicNumerators n).lcm fun a => (rvachevDyadic n a).den

/--
Reshetnikov's rational number `R_n` (equation (27)).  Its mathematically
intended domain is `n ≥ 1`; the definition is made total only for convenience.
-/
def reshetnikov (n : ℕ) : ℚ :=
  (2 : ℚ) ^ (n - 1).choose 2 * (Nat.factorial (2 * n) : ℚ) *
    fabiusAtInverseTwoPow n * evenMersenneProduct (n / 2)

/-- The explicit common-denominator bound in Theorem 13. -/
def denominatorBound (n : ℕ) : ℕ :=
  n.factorial * 2 ^ (n + 1).choose 2 * oddDoubleFactorial (n / 2 + 1) *
    evenMersenneProduct (n / 2)

/-- The rational normalization `A_n = 2^(-choose n 2) D_n`. -/
def normalizedDyadicDenominator (n : ℕ) : ℚ :=
  dyadicDenominator n / (2 : ℚ) ^ n.choose 2

/-- The sequence `K_n = A_(2n-1)` from Conjecture 16. -/
def conjecturalK (n : ℕ) : ℚ :=
  normalizedDyadicDenominator (2 * n - 1)

/-- The sequence `H_n = K_n / (2 (2n-1)!)` from Conjecture 16. -/
def conjecturalH (n : ℕ) : ℚ :=
  conjecturalK n / (2 * (Nat.factorial (2 * n - 1) : ℚ))

end Fabius
```

### `SourceMomentBridge.lean`

```lean
import ExplicitCoefficients
import UpstreamArithmetic
import Mathlib.Tactic.FieldSimp

namespace FabiusProofLane
open Finset

noncomputable def sourceCoefficient (n : ℕ) : ℚ :=
  Fabius.moment n / ((2*n).factorial : ℚ)

lemma binomial_factorial_ratio (N K : ℕ) (h : K ≤ N) :
    (N.choose K : ℚ) / (N.factorial : ℚ) =
      1 / ((K.factorial : ℚ) * ((N-K).factorial : ℚ)) := by
  apply (div_eq_div_iff (by positivity) (by positivity)).mpr
  have hh := Nat.choose_mul_factorial_mul_factorial h
  have hq : (N.choose K : ℚ) * (K.factorial : ℚ) * ((N-K).factorial : ℚ) = (N.factorial : ℚ) := by
    exact_mod_cast hh
  simpa only [mul_assoc, one_mul] using hq

lemma source_kernel_term (n k : ℕ) (hk : k < n) :
    sinhKernel 0 (n-k) * sourceCoefficient k =
      (Nat.choose (2*n+1) (2*k) : ℚ) * Fabius.moment k /
        (((2*n+1 : ℕ) : ℚ) * ((2*n).factorial : ℚ)) := by
  have hsub : 2*n+1-2*k=2*(n-k)+1 := by omega
  have hf : (((2*n+1).factorial : ℕ) : ℚ) =
      ((2*n+1 : ℕ) : ℚ) * ((2*n).factorial : ℚ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hb := binomial_factorial_ratio (2*n+1) (2*k) (by omega)
  rw [hsub, hf] at hb
  calc
    sinhKernel 0 (n-k) * sourceCoefficient k =
        (1 / (((2*k).factorial : ℚ) * ((2*(n-k)+1).factorial : ℚ))) * Fabius.moment k := by
      simp only [sinhKernel, sourceCoefficient, zero_mul, pow_zero,
        div_eq_mul_inv, mul_inv_rev]
      ring
    _ = ((Nat.choose (2*n+1) (2*k) : ℚ) /
        (((2*n+1 : ℕ) : ℚ) * ((2*n).factorial : ℚ))) * Fabius.moment k := by rw [hb]
    _ = _ := by ring

lemma sourceCoefficient_recurrence (n : ℕ) (hn : 0 < n) :
    ((4 : ℚ)^n-1)*sourceCoefficient n =
      ∑ i ∈ range n, sinhKernel 0 (i+1) * sourceCoefficient (n-(i+1)) := by
  have hrange : (∑ i ∈ range n, sinhKernel 0 (i+1) * sourceCoefficient (n-(i+1))) =
      ∑ k ∈ range n, sinhKernel 0 (n-k) * sourceCoefficient k := by
    rw [← Finset.sum_range_reflect (fun k => sinhKernel 0 (n-k) * sourceCoefficient k) n]
    apply sum_congr rfl
    intro i hi
    have hi' := mem_range.mp hi
    congr 2 <;> omega
  rw [hrange]
  have hterms : (∑ k ∈ range n, sinhKernel 0 (n-k) * sourceCoefficient k) =
      (∑ k ∈ range n, (Nat.choose (2*n+1) (2*k) : ℚ) * Fabius.moment k) /
        (((2*n+1 : ℕ) : ℚ) * ((2*n).factorial : ℚ)) := by
    simp only [div_eq_mul_inv, Finset.sum_mul]
    apply sum_congr rfl
    intro k hk
    exact source_kernel_term n k (mem_range.mp hk)
  rw [hterms]
  cases n with
  | zero => omega
  | succ s =>
    unfold sourceCoefficient
    rw [Fabius.moment_succ]
    rw [Fin.sum_univ_eq_sum_range (fun k =>
      (Nat.choose (2*(s+1)+1) (2*k) : ℚ) * Fabius.moment k) (s+1)]
    have hpow : (2 : ℚ)^(2*(s+1)) = (4 : ℚ)^(s+1) := by
      rw [pow_mul]
      norm_num
    rw [hpow]
    have ht : (4 : ℚ)^(s+1)-1 ≠ 0 := by
      exact ne_of_gt (sub_pos.mpr (one_lt_pow₀ (by norm_num) (by omega)))
    have hD : (((2*(s+1)).factorial : ℕ) : ℚ) ≠ 0 := by positivity
    have hL : (((2*(s+1)+1 : ℕ)) : ℚ) ≠ 0 := by positivity
    field_simp

lemma sourceCoefficient_eq_explicit (n : ℕ) : sourceCoefficient n = evenCoefficient n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [sourceCoefficient]
    | succ n =>
      have hs := sourceCoefficient_recurrence (n+1) (by omega)
      have he := evenCoefficient_recurrence (n+1) (by omega)
      have hsum : (∑ i ∈ range (n+1), sinhKernel 0 (i+1) * sourceCoefficient (n+1-(i+1))) =
          ∑ i ∈ range (n+1), sinhKernel 0 (i+1) * evenCoefficient (n+1-(i+1)) := by
        apply sum_congr rfl
        intro i hi
        rw [ih _ (by have := mem_range.mp hi; omega)]
      rw [hsum] at hs
      have ht : (4 : ℚ)^(n+1)-1 ≠ 0 := by
        exact ne_of_gt (sub_pos.mpr (one_lt_pow₀ (by norm_num) (by omega)))
      exact (mul_left_cancel₀ ht) (hs.trans he.symm)

/-- The checked witness now refers to the source's actual rational moment sequence. -/
theorem source_moment_denominator_witness (p N : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ j, 2*j ≤ N ∧ (padicValNat p (N+1).factorial : ℤ) ≤
      -padicValRat p (Fabius.moment j / ((2*j).factorial : ℚ)) := by
  obtain ⟨j, hj, hv⟩ := explicit_coefficient_denominator_witness p N hp2
  refine ⟨j, hj, ?_⟩
  rw [← sourceCoefficient_eq_explicit j] at hv
  exact hv

#print axioms source_moment_denominator_witness

end FabiusProofLane
```

### `LocalPolynomial.lean`

```lean
import SourceMomentBridge
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination

namespace FabiusProofLane
open Finset Polynomial

/-- The ordinary localization Z_(p), implemented as a rational subring. -/
def integralSubring (p : ℕ) [Fact p.Prime] : Subring ℚ where
  carrier := {q | IntegralAt p q}
  zero_mem' := integralAt_zero p
  one_mem' := integralAt_one p
  add_mem' := integralAt_add
  mul_mem' := integralAt_mul
  neg_mem' := integralAt_neg

lemma integralAt_int (p : ℕ) [Fact p.Prime] (z : ℤ) : IntegralAt p (z : ℚ) := by
  unfold IntegralAt
  rw [padicValRat.of_int]
  exact Int.natCast_nonneg _

lemma integralAt_iff_den {p : ℕ} [hp : Fact p.Prime] (q : ℚ) :
    IntegralAt p q ↔ ¬p ∣ q.den := by
  have hden := Rat.den_nz q
  have hvalden : padicValNat p q.den = 0 ↔ ¬p ∣ q.den := by
    constructor
    · intro hv hd
      have hh := one_le_padicValNat_of_dvd (p:=p) hden hd
      omega
    · exact padicValNat.eq_zero_of_not_dvd
  rw [← hvalden]
  unfold IntegralAt padicValRat
  have hnum0 : (0 : ℤ) ≤ padicValInt p q.num := Int.natCast_nonneg _
  have hd0 : (0 : ℤ) ≤ padicValNat p q.den := Int.natCast_nonneg _
  rcases Rat.num_or_den_zero_padicVal q hp.out with hn | hd
  · rw [hn]
    constructor <;> intro h <;> omega
  · simp [hd, hnum0]

lemma exists_integral_coefficient_scale {p : ℕ} [hp : Fact p.Prime] (P : ℚ[X]) :
    ∃ t : ℕ, ∀ i, IntegralAt p (((p : ℚ)^t)*P.coeff i) := by
  classical
  let t := P.support.sup (fun i => (-padicValRat p (P.coeff i)).toNat)
  refine ⟨t, ?_⟩
  intro i
  by_cases hi : P.coeff i=0
  · simp [hi, IntegralAt]
  have himem : i ∈ P.support := mem_support_iff.mpr hi
  have hle : (-padicValRat p (P.coeff i)).toNat ≤ t := by
    exact Finset.le_sup (f:=fun k => (-padicValRat p (P.coeff k)).toNat) himem
  have hz : -padicValRat p (P.coeff i) ≤ (t : ℤ) := by
    have ha : -padicValRat p (P.coeff i) ≤ (((-padicValRat p (P.coeff i)).toNat : ℕ) : ℤ) := by omega
    have hh : (((-padicValRat p (P.coeff i)).toNat : ℕ) : ℤ) ≤ t := by exact_mod_cast hle
    omega
  unfold IntegralAt
  rw [padicValRat.mul (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)) hi, padicValRat.pow,
    padicValRat.self hp.out.one_lt, mul_one]
  omega

/-- Rational points of Z_(p) have integral approximants in either parity class.
The Bezout calculation simultaneously enforces the p-power congruence and parity. -/
lemma local_approximation {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (x : ℚ) (hx : IntegralAt p x) (t : ℕ) (eps : ℤ) :
    ∃ z r : ℤ, z=2*r+eps ∧
      IntegralAt p ((x-(z : ℚ))/(p : ℚ)^t) := by
  have hden : ¬p ∣ x.den := (integralAt_iff_den x).mp hx
  have hpnot : ¬p ∣ 2 := by
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h)
  have hprod : ¬p ∣ 2*x.den := by
    intro h
    rcases hp.out.dvd_mul.mp h with h | h
    · exact hpnot h
    · exact hden h
  have hcop : Nat.Coprime (2*x.den) p :=
    ((hp.out.coprime_iff_not_dvd).mpr hprod).symm
  have hcoppow : Nat.Coprime (2*x.den) (p^t) := hcop.pow_right t
  have hcopint : IsCoprime ((2*x.den : ℕ) : ℤ) ((p^t : ℕ) : ℤ) :=
    Nat.Coprime.isCoprime hcoppow
  obtain ⟨A,B,hbez⟩ := hcopint
  let r : ℤ := A*(x.num-(x.den : ℤ)*eps)
  let z : ℤ := 2*r+eps
  refine ⟨z,r,rfl,?_⟩
  have hD : (x.den : ℚ) ≠ 0 := by exact_mod_cast Rat.den_nz x
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hbezq : (A : ℚ)*(2*(x.den : ℚ))+(B : ℚ)*(p : ℚ)^t=1 := by
    exact_mod_cast hbez
  have heq : (x-(z : ℚ))/(p : ℚ)^t =
      ((B*(x.num-(x.den : ℤ)*eps) : ℤ) : ℚ) / (x.den : ℚ) := by
    dsimp [z,r]
    push_cast
    have hxnum : x*(x.den : ℚ)=(x.num : ℚ) := by
      exact Rat.mul_den_eq_num x
    field_simp
    linear_combination hxnum - ((x.num : ℚ)-(x.den : ℚ)*(eps : ℚ))*hbezq
  rw [heq, div_eq_mul_inv]
  apply integralAt_mul (integralAt_int p _)
  unfold IntegralAt
  rw [padicValRat.inv, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hden]
  omega


/-- Clearing coefficient denominators turns congruent local inputs into
congruent evaluations, without topology or a p-adic field. -/
lemma local_polynomial_difference {p : ℕ} [hp : Fact p.Prime]
    (P : ℚ[X]) (t : ℕ)
    (hcoeff : ∀ i, IntegralAt p (((p : ℚ)^t)*P.coeff i))
    (x y : ℚ) (hx : IntegralAt p x) (hy : IntegralAt p y)
    (hxy : IntegralAt p ((x-y)/(p : ℚ)^t)) :
    IntegralAt p (P.eval x-P.eval y) := by
  classical
  let R := integralSubring p
  let Q : ℚ[X] := C ((p : ℚ)^t)*P
  have hlift : Q ∈ Polynomial.lifts R.subtype := by
    apply (Polynomial.lifts_iff_coeff_lifts Q).mpr
    intro i
    refine ⟨⟨Q.coeff i, ?_⟩,rfl⟩
    change IntegralAt p (Q.coeff i)
    simpa only [Q, Polynomial.coeff_C_mul] using hcoeff i
  obtain ⟨Q',hQ'⟩ := (Polynomial.lifts_iff_set_range Q).mp hlift
  let xr : R := ⟨x,hx⟩
  let yr : R := ⟨y,hy⟩
  obtain ⟨s,hs⟩ := Polynomial.sub_dvd_eval_sub xr yr Q'
  have hex (z : R) : ((Q'.eval z : R) : ℚ) = Q.eval (z : ℚ) := by
    rw [← hQ']
    exact (Polynomial.eval_map_apply (p:=Q') (f:=R.subtype) z).symm
  have hsQ := congrArg R.subtype hs
  rw [map_sub, map_mul, map_sub] at hsQ
  change ((Q'.eval xr : R) : ℚ) - ((Q'.eval yr : R) : ℚ) = (x-y)*(s : ℚ) at hsQ
  rw [hex xr, hex yr] at hsQ
  change Q.eval x-Q.eval y=(x-y)*(s : ℚ) at hsQ
  simp only [Q, Polynomial.eval_mul, Polynomial.eval_C] at hsQ
  have hp0 : (p : ℚ)^t ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have heq : (p : ℚ)^t*(P.eval x-P.eval y) =
      (p : ℚ)^t*(((x-y)/(p : ℚ)^t)*(s : ℚ)) := by
    rw [mul_sub, hsQ]
    field_simp
  have heq' := mul_left_cancel₀ hp0 heq
  rw [heq']
  exact integralAt_mul hxy s.property

/-- Even integers, odd integers, or any parity coset determine local integrality
of a rational polynomial. This is the density fact used in the written proof. -/
theorem local_polynomial_parity_density {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (P : ℚ[X]) (eps : ℤ)
    (hclass : ∀ r : ℤ, IntegralAt p (P.eval ((2*r+eps : ℤ) : ℚ)))
    (x : ℚ) (hx : IntegralAt p x) : IntegralAt p (P.eval x) := by
  obtain ⟨t,ht⟩ := exists_integral_coefficient_scale (p:=p) P
  obtain ⟨z,r,hzr,happrox⟩ := local_approximation hp2 x hx t eps
  have hy : IntegralAt p (P.eval (z : ℚ)) := by rw [hzr]; exact hclass r
  have hdiff := local_polynomial_difference P t ht x (z : ℚ) hx (integralAt_int p z) happrox
  have heq : P.eval x=(P.eval x-P.eval (z : ℚ))+P.eval (z : ℚ) := by ring
  rw [heq]
  exact integralAt_add hdiff hy

#print axioms local_polynomial_parity_density

end FabiusProofLane

```

### `AppellLocalDenominators.lean`

```lean
import LocalPolynomial

namespace FabiusProofLane
open Polynomial

lemma two_valuation_zero {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    padicValRat p (2 : ℚ)=0 := by
  have hnot : ¬p ∣ 2 := by
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h)
  rw [show (2 : ℚ)=((2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
    padicValNat.eq_zero_of_not_dvd hnot]
  rfl

lemma integralAt_two_inv {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    IntegralAt p ((2 : ℚ)⁻¹) := by
  unfold IntegralAt
  rw [padicValRat.inv, two_valuation_zero hp2]
  omega

lemma integralAt_two_pow_iff {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (n : ℕ) (q : ℚ) : IntegralAt p ((2 : ℚ)^n*q) ↔ IntegralAt p q := by
  by_cases hq : q=0
  · simp [hq,IntegralAt]
  unfold IntegralAt
  rw [padicValRat.mul (by positivity) hq, padicValRat.pow,
    two_valuation_zero hp2, mul_zero, zero_add]

/-- `u` clears all local values of a polynomial, with no least-exponent choice. -/
def ClearsLocal (p : ℕ) (u : ℚ) (P : ℚ[X]) : Prop :=
  ∀ x : ℚ, IntegralAt p x → IntegralAt p (u*P.eval x)

lemma clearsLocal_lower {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (u : ℚ) (P R : ℚ[X]) (n : ℕ)
    (hrec : ∀ x : ℚ, P.eval (x+1)-P.eval (x-1) = (2 : ℚ)^n*R.eval (x/2))
    (hP : ClearsLocal p u P) : ClearsLocal p u R := by
  intro x hx
  have h2x : IntegralAt p ((2 : ℚ)*x) := integralAt_mul (integralAt_int p 2) hx
  have hpv := hP (2*x+1) (integralAt_add h2x (integralAt_one p))
  have hmv := hP (2*x-1) (integralAt_sub h2x (integralAt_one p))
  have hdiff := integralAt_sub hpv hmv
  have heq : u*P.eval (2*x+1)-u*P.eval (2*x-1)=(2 : ℚ)^n*(u*R.eval x) := by
    rw [← mul_sub, hrec]
    rw [show (2*x)/2=x by ring]
    ring
  rw [heq] at hdiff
  exact (integralAt_two_pow_iff hp2 n _).mp hdiff

lemma clearsLocal_upper {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (u : ℚ) (P R : ℚ[X]) (n : ℕ) (eps : ℤ)
    (hrec : ∀ x : ℚ, P.eval (x+1)-P.eval (x-1) = (2 : ℚ)^n*R.eval (x/2))
    (hR : ClearsLocal p u R) (hbase : IntegralAt p (u*P.eval (eps : ℚ))) :
    ClearsLocal p u P := by
  let g (z : ℤ) : ℚ := u*P.eval ((2*z+eps : ℤ) : ℚ)
  have hg0 : IntegralAt p (g 0) := by simpa [g] using hbase
  have hinc (z : ℤ) : IntegralAt p (g (z+1)-g z) := by
    let x : ℚ := ((2*z+eps+1 : ℤ) : ℚ)
    have hx : IntegralAt p (x/2) := by
      rw [div_eq_mul_inv]
      exact integralAt_mul (integralAt_int p _) (integralAt_two_inv hp2)
    have hv := hR (x/2) hx
    have hmul : IntegralAt p ((2 : ℚ)^n*(u*R.eval (x/2))) :=
      (integralAt_two_pow_iff hp2 n _).mpr hv
    have heq : g (z+1)-g z=(2 : ℚ)^n*(u*R.eval (x/2)) := by
      have he := hrec x
      have hplus : x+1=((2*(z+1)+eps : ℤ) : ℚ) := by dsimp [x]; push_cast; ring
      have hminus : x-1=((2*z+eps : ℤ) : ℚ) := by dsimp [x]; push_cast; ring
      rw [hplus,hminus] at he
      dsimp [g]
      rw [← mul_sub,he]
      ring
    rw [heq]
    exact hmul
  have hg (z : ℤ) : IntegralAt p (g z) := by
    induction z using Int.induction_on with
    | zero => exact hg0
    | succ i hi =>
      have hh := integralAt_add (hinc (i : ℤ)) hi
      have heq : (g ((i : ℤ)+1)-g (i : ℤ))+g (i : ℤ)=g ((i : ℤ)+1) := by ring
      simpa only [heq] using hh
    | pred i hi =>
      have hh := integralAt_sub hi (hinc (-(i : ℤ)-1))
      have heq : -(i : ℤ)-1+1=-(i : ℤ) := by ring
      rw [heq] at hh
      have heq' : g (-(i : ℤ))-(g (-(i : ℤ))-g (-(i : ℤ)-1))=g (-(i : ℤ)-1) := by ring
      simpa only [heq'] using hh
  intro x hx
  have hclass : ∀ z : ℤ, IntegralAt p ((C u*P).eval ((2*z+eps : ℤ) : ℚ)) := by
    intro z
    simpa only [Polynomial.eval_C_mul] using hg z
  have h := local_polynomial_parity_density hp2 (C u*P) eps hclass x hx
  simpa only [Polynomial.eval_C_mul] using h

/-- Exact local denominator step, with either the value at zero or the value at one. -/
theorem clearsLocal_step {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (u : ℚ) (P R : ℚ[X]) (n : ℕ) (eps : ℤ)
    (hrec : ∀ x : ℚ, P.eval (x+1)-P.eval (x-1) = (2 : ℚ)^n*R.eval (x/2)) :
    ClearsLocal p u P ↔ ClearsLocal p u R ∧ IntegralAt p (u*P.eval (eps : ℚ)) := by
  constructor
  · intro h
    exact ⟨clearsLocal_lower hp2 u P R n hrec h, h _ (integralAt_int p eps)⟩
  · rintro ⟨hR,hbase⟩
    exact clearsLocal_upper hp2 u P R n eps hrec hR hbase

/-- The new running-coefficient characterization for any sequence with the
Fabius Appell difference identity. The identity remains an explicit premise. -/
theorem clearsLocal_iff_prefix_constants {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (u : ℚ) (Q : ℕ → ℚ[X]) (hQ0 : Q 0=C 1)
    (hrec : ∀ n x, (Q (n+1)).eval (x+1)-(Q (n+1)).eval (x-1) =
      (2 : ℚ)^(n+1)*(Q n).eval (x/2)) (n : ℕ) :
    ClearsLocal p u (Q n) ↔ ∀ i, i ≤ n → IntegralAt p (u*(Q i).eval 0) := by
  induction n with
  | zero =>
    simp only [Nat.le_zero] at *
    constructor
    · intro h i hi
      subst i
      exact h 0 (integralAt_zero p)
    · intro h x hx
      simpa only [hQ0,Polynomial.eval_C,mul_one] using h 0 rfl
  | succ n ih =>
    rw [clearsLocal_step hp2 u (Q (n+1)) (Q n) (n+1) 0 (hrec n),ih]
    simp only [Int.cast_zero]
    constructor
    · rintro ⟨h,hn⟩ i hi
      by_cases hil : i ≤ n
      · exact h i hil
      · have heq : i=n+1 := by omega
        simpa only [heq] using hn
    · intro h
      exact ⟨fun i hi => h i (by omega), h (n+1) (by omega)⟩

#print axioms clearsLocal_iff_prefix_constants
end FabiusProofLane
```

### `FiniteSampling.lean`

```lean
import AppellLocalDenominators
import Mathlib.Algebra.Polynomial.Taylor

namespace FabiusProofLane
open Polynomial

lemma forward_difference_degree (P : ℚ[X]) (d : ℕ) (hP : P.natDegree ≤ d+1) :
    (Polynomial.taylor 1 P-P).natDegree ≤ d := by
  by_cases hzero : P=0
  · simp [hzero]
  by_cases hdiff : Polynomial.taylor 1 P-P=0
  · simp [hdiff]
  have hstrict : (Polynomial.taylor 1 P-P).degree < P.degree :=
    Polynomial.degree_sub_lt_right (Polynomial.degree_taylor P 1) hzero
      (Polynomial.leadingCoeff_taylor 1 P)
  have hdeg : P.degree ≤ ((d+1 : ℕ) : WithBot ℕ) :=
    Polynomial.degree_le_of_natDegree_le hP
  have hlt : (Polynomial.taylor 1 P-P).natDegree < d+1 :=
    (Polynomial.natDegree_lt_iff_degree_lt hdiff).mpr (lt_of_lt_of_le hstrict hdeg)
  omega

/-- Consecutive integral samples determine all integer values.
The proof uses degree-lowering differences and two-sided integer induction,
rather than assuming an integer-valued binomial-polynomial API. -/
theorem integer_samples_zero {p : ℕ} [hp : Fact p.Prime]
    (d : ℕ) (P : ℚ[X]) (hP : P.natDegree ≤ d)
    (hsample : ∀ i : ℕ, i ≤ d → IntegralAt p (P.eval (i : ℚ))) :
    ∀ z : ℤ, IntegralAt p (P.eval (z : ℚ)) := by
  induction d generalizing P with
  | zero =>
    have heq : P=C (P.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hP
    have hconst (x : ℚ) : P.eval x=P.coeff 0 := by
      simpa only [Polynomial.eval_C] using congrArg (fun Q : ℚ[X] => Q.eval x) heq
    intro z
    have h := hsample 0 (by omega)
    rw [hconst] at h ⊢
    exact h
  | succ d ih =>
    let D := Polynomial.taylor 1 P-P
    have hD : D.natDegree ≤ d := forward_difference_degree P d hP
    have heval (x : ℚ) : D.eval x=P.eval (x+1)-P.eval x := by
      simp [D,Polynomial.eval_sub,Polynomial.taylor_eval]
    have hDsamples (i : ℕ) (hi : i ≤ d) : IntegralAt p (D.eval (i : ℚ)) := by
      rw [heval]
      have h := integralAt_sub (hsample (i+1) (by omega)) (hsample i (by omega))
      simpa only [Nat.cast_add,Nat.cast_one] using h
    have hDall := ih D hD hDsamples
    have hinc (z : ℤ) : IntegralAt p (P.eval ((z+1 : ℤ) : ℚ)-P.eval (z : ℚ)) := by
      have h := hDall z
      rw [heval] at h
      simpa only [Int.cast_add,Int.cast_one] using h
    intro z
    induction z using Int.induction_on with
    | zero => simpa only [Int.cast_zero,Nat.cast_zero] using hsample 0 (by omega)
    | succ i hi =>
      have hh := integralAt_add (hinc (i : ℤ)) hi
      have heq : (P.eval (((i : ℤ)+1 : ℤ) : ℚ)-P.eval ((i : ℤ) : ℚ))+
          P.eval ((i : ℤ) : ℚ)=P.eval (((i : ℤ)+1 : ℤ) : ℚ) := by ring
      simpa only [heq] using hh
    | pred i hi =>
      have hh := integralAt_sub hi (hinc (-(i : ℤ)-1))
      have heq : -(i : ℤ)-1+1=-(i : ℤ) := by ring
      rw [heq] at hh
      have heq' : P.eval ((-(i : ℤ) : ℤ) : ℚ)-
          (P.eval ((-(i : ℤ) : ℤ) : ℚ)-P.eval ((-(i : ℤ)-1 : ℤ) : ℚ)) =
          P.eval ((-(i : ℤ)-1 : ℤ) : ℚ) := by ring
      simpa only [heq'] using hh

/-- Any d+1 consecutive integer samples determine local p-integrality. -/
theorem consecutive_samples_local {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (d : ℕ) (P : ℚ[X]) (hP : P.natDegree ≤ d) (a : ℤ)
    (hsample : ∀ i : ℕ, i ≤ d → IntegralAt p (P.eval ((a+i : ℤ) : ℚ)))
    (x : ℚ) (hx : IntegralAt p x) : IntegralAt p (P.eval x) := by
  let T := Polynomial.taylor (a : ℚ) P
  have hTdeg : T.natDegree ≤ d := by simpa only [T,Polynomial.natDegree_taylor] using hP
  have hTsamp (i : ℕ) (hi : i ≤ d) : IntegralAt p (T.eval (i : ℚ)) := by
    have h := hsample i hi
    simpa [T,Polynomial.taylor_eval,add_comm] using h
  have hTall := integer_samples_zero d T hTdeg hTsamp
  have hPall (z : ℤ) : IntegralAt p (P.eval (z : ℚ)) := by
    have h := hTall (z-a)
    simpa [T,Polynomial.taylor_eval] using h
  have hclass (z : ℤ) : IntegralAt p (P.eval ((2*z+0 : ℤ) : ℚ)) := hPall _
  exact local_polynomial_parity_density hp2 P 0 hclass x hx

#print axioms consecutive_samples_local
end FabiusProofLane
```

### `SourceAppell.lean`

```lean
import FiniteSampling
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Expand

namespace FabiusProofLane
open Finset

noncomputable def momentSeries : PowerSeries ℚ :=
  PowerSeries.expand 2 (by decide) (seqSeries sourceCoefficient)
noncomputable def sinhSeries : PowerSeries ℚ :=
  PowerSeries.expand 2 (by decide) (seqSeries (sinhKernel 0))

lemma momentSeries_even (n : ℕ) : PowerSeries.coeff (2*n) momentSeries=sourceCoefficient n := by
  simp [momentSeries,PowerSeries.coeff_expand_mul,seqSeries_coeff]
lemma momentSeries_odd (n : ℕ) : PowerSeries.coeff (2*n+1) momentSeries=0 := by
  apply PowerSeries.coeff_expand_of_not_dvd
  omega
lemma sinhSeries_even (n : ℕ) : PowerSeries.coeff (2*n) sinhSeries=1/((2*n+1).factorial : ℚ) := by
  simp [sinhSeries,PowerSeries.coeff_expand_mul,seqSeries_coeff,sinhKernel]
lemma sinhSeries_odd (n : ℕ) : PowerSeries.coeff (2*n+1) sinhSeries=0 := by
  apply PowerSeries.coeff_expand_of_not_dvd
  omega

lemma momentSeries_dilation : PowerSeries.rescale (2 : ℚ) momentSeries=sinhSeries*momentSeries := by
  have hb := dilation_of_recurrence sourceCoefficient sourceCoefficient_recurrence
  have hex : PowerSeries.rescale (2 : ℚ) momentSeries =
      PowerSeries.expand 2 (by decide) (PowerSeries.rescale (4 : ℚ) (seqSeries sourceCoefficient)) := by
    ext n
    obtain ⟨r,hr|hr⟩ := Nat.even_or_odd' n
    · subst n
      rw [PowerSeries.coeff_rescale,momentSeries_even,PowerSeries.coeff_expand_mul,
        PowerSeries.coeff_rescale,seqSeries_coeff]
      rw [show (2 : ℚ)^(2*r)=(4 : ℚ)^r by rw [pow_mul]; norm_num]
    · subst n
      rw [PowerSeries.coeff_rescale,momentSeries_odd,mul_zero,
        PowerSeries.coeff_expand_of_not_dvd (h:=by omega)]
  rw [hex,hb,map_mul]
  rfl

lemma exp_difference_sinh :
    PowerSeries.rescale (1 : ℚ) (PowerSeries.exp ℚ)-
      PowerSeries.rescale (-1 : ℚ) (PowerSeries.exp ℚ) =
      PowerSeries.C 2*(sinhSeries*PowerSeries.X) := by
  ext n
  rw [map_sub,PowerSeries.coeff_rescale,PowerSeries.coeff_rescale,
    PowerSeries.coeff_C_mul]
  cases n with
  | zero => simp [PowerSeries.coeff_exp]
  | succ n =>
    rw [show n+1=n+1 by rfl]
    rw [show sinhSeries*PowerSeries.X=sinhSeries*PowerSeries.X^1 by simp,
      PowerSeries.coeff_mul_X_pow]
    obtain ⟨r,hr|hr⟩ := Nat.even_or_odd' n
    · subst n
      rw [sinhSeries_even,PowerSeries.coeff_exp]
      norm_num [pow_add,pow_mul]
      ring
    · subst n
      rw [sinhSeries_odd,PowerSeries.coeff_exp]
      simp [pow_add]

noncomputable def appellSeries (x : ℚ) : PowerSeries ℚ :=
  momentSeries*PowerSeries.rescale x (PowerSeries.exp ℚ)

noncomputable def sourceAppellPolynomial (n : ℕ) : Polynomial ℚ :=
  ∑ i ∈ range (n+1), Polynomial.monomial (n-i)
    (PowerSeries.coeff i momentSeries/((n-i).factorial : ℚ))

lemma sourceAppellPolynomial_eval (n : ℕ) (x : ℚ) :
    (sourceAppellPolynomial n).eval x=PowerSeries.coeff n (appellSeries x) := by
  simp only [sourceAppellPolynomial,Polynomial.eval_finsetSum,Polynomial.eval_monomial,
    appellSeries,PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i momentSeries *
      PowerSeries.coeff j (PowerSeries.rescale x (PowerSeries.exp ℚ))) n]
  apply sum_congr rfl
  intro i hi
  rw [PowerSeries.coeff_rescale,PowerSeries.coeff_exp]
  change PowerSeries.coeff i momentSeries / ((n-i).factorial : ℚ) * x^(n-i) =
    PowerSeries.coeff i momentSeries * (x^(n-i) * (1 / ((n-i).factorial : ℚ)))
  ring

lemma sourceAppellPolynomial_degree (n : ℕ) : (sourceAppellPolynomial n).natDegree ≤ n := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  exact le_trans (Polynomial.natDegree_monomial_le _) (Nat.sub_le _ _)

lemma sourceAppellPolynomial_zero : sourceAppellPolynomial 0=Polynomial.C 1 := by
  have h0 : PowerSeries.constantCoeff momentSeries=1 := by
    simpa [sourceCoefficient,PowerSeries.coeff_zero_eq_constantCoeff] using momentSeries_even 0
  simp [sourceAppellPolynomial,h0]


lemma appellSeries_difference (x : ℚ) :
    appellSeries (x+1)-appellSeries (x-1) =
      PowerSeries.C 2*(PowerSeries.rescale (2 : ℚ) (appellSeries (x/2))*PowerSeries.X) := by
  have hp := PowerSeries.exp_mul_exp_eq_exp_add x (1 : ℚ)
  have hm := PowerSeries.exp_mul_exp_eq_exp_add x (-1 : ℚ)
  have he : PowerSeries.rescale (2 : ℚ)
      (PowerSeries.rescale (x/2) (PowerSeries.exp ℚ)) =
      PowerSeries.rescale x (PowerSeries.exp ℚ) := by
    rw [PowerSeries.rescale_rescale]
    congr 1
    ring
  calc
    appellSeries (x+1)-appellSeries (x-1) =
        (momentSeries*PowerSeries.rescale x (PowerSeries.exp ℚ))*
          (PowerSeries.rescale 1 (PowerSeries.exp ℚ)-PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) := by
      dsimp [appellSeries]
      rw [← hp,show x-1=x+(-1) by ring,← hm]
      ring
    _ = (momentSeries*PowerSeries.rescale x (PowerSeries.exp ℚ))*
        (PowerSeries.C 2*(sinhSeries*PowerSeries.X)) := by rw [exp_difference_sinh]
    _ = PowerSeries.C 2*((PowerSeries.rescale (2 : ℚ) momentSeries*
        PowerSeries.rescale x (PowerSeries.exp ℚ))*PowerSeries.X) := by
      rw [momentSeries_dilation]
      ring
    _ = _ := by rw [appellSeries,map_mul,he]

lemma sourceAppellPolynomial_difference (n : ℕ) (x : ℚ) :
    (sourceAppellPolynomial (n+1)).eval (x+1)-
      (sourceAppellPolynomial (n+1)).eval (x-1) =
      (2 : ℚ)^(n+1)*(sourceAppellPolynomial n).eval (x/2) := by
  have h := congrArg (PowerSeries.coeff (n+1)) (appellSeries_difference x)
  rw [map_sub,PowerSeries.coeff_C_mul,
    show PowerSeries.rescale (2 : ℚ) (appellSeries (x/2))*PowerSeries.X =
      PowerSeries.rescale (2 : ℚ) (appellSeries (x/2))*PowerSeries.X^1 by simp,
    PowerSeries.coeff_mul_X_pow,PowerSeries.coeff_rescale] at h
  rw [← sourceAppellPolynomial_eval,← sourceAppellPolynomial_eval,
    ← sourceAppellPolynomial_eval] at h
  rw [h,pow_succ]
  ring

lemma sourceAppellPolynomial_constant (n : ℕ) :
    (sourceAppellPolynomial n).eval 0=PowerSeries.coeff n momentSeries := by
  classical
  rw [sourceAppellPolynomial,Polynomial.eval_finsetSum,Finset.sum_eq_single n]
  · simp
  · intro i hi hne
    have hin : i < n := by have := mem_range.mp hi; omega
    have hd : n-i ≠ 0 := by omega
    simp [Polynomial.eval_monomial,zero_pow hd]
  · simp

theorem sourceAppell_local_characterization {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (u : ℚ) (n : ℕ) :
    ClearsLocal p u (sourceAppellPolynomial n) ↔
      ∀ i, i ≤ n → IntegralAt p (u*PowerSeries.coeff i momentSeries) := by
  have h := clearsLocal_iff_prefix_constants hp2 u sourceAppellPolynomial
    sourceAppellPolynomial_zero sourceAppellPolynomial_difference n
  simpa only [sourceAppellPolynomial_constant] using h

#print axioms sourceAppell_local_characterization
end FabiusProofLane

```

### `UpstreamMomentPowerSeries.lean`

```lean
import UpstreamArithmetic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Formal power series for the Fabius moment sequences

This file proves, entirely in exact rational arithmetic, that the half moments
are the even-binomial transform of the moments.  The key step packages the
recurrence defining `moment` as a formal-power-series identity.  This avoids
using any analytic facts about the Fabius or Rvachev functions in the proof of
the inverse-power evaluator formula.  A single arbitrary-translation
coefficient calculation supplies both the centered-series API and the
half-translation used in the recurrence proof.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset PowerSeries

namespace Fabius

/-- Equation (9), the original recurrence before isolating `c_n`. -/
theorem moment_original_recurrence (n : ℕ) :
    ((2 * n + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (2 * n) * moment n =
      ∑ k ∈ range (n + 1),
        (Nat.choose (2 * n + 1) (2 * k) : ℚ) * moment k := by
  cases n with
  | zero => norm_num [moment]
  | succ n =>
      rw [sum_range_succ, moment_succ]
      rw [Fin.sum_univ_eq_sum_range
        (fun k =>
          (Nat.choose (2 * (n + 1) + 1) (2 * k) : ℚ) * moment k) (n + 1)]
      have hchoose : (2 * (n + 1) + 1).choose (2 * (n + 1)) =
          2 * (n + 1) + 1 := by
        exact Nat.choose_succ_self_right (2 * (n + 1))
      rw [hchoose]
      have hpow : (2 : ℚ) ^ (2 * (n + 1)) - 1 ≠ 0 := by
        apply ne_of_gt
        exact sub_pos.mpr (one_lt_pow₀ (by norm_num) (by omega))
      field_simp
      ring

/-- The generating series `∑ (moment n / (2 * n)!) * X ^ n` of the Fabius
moments. -/
noncomputable def momentPS : PowerSeries ℚ :=
  PowerSeries.mk fun n => moment n / ((2 * n).factorial : ℚ)

/-- The generating series `∑ X ^ n / (2 * n + 1)!`, obtained from `sinh x / x`
by substituting `X` for `x ^ 2`. -/
noncomputable def sinhDivPS : PowerSeries ℚ :=
  PowerSeries.mk fun n => 1 / ((2 * n + 1).factorial : ℚ)

/-- The original moment recurrence, packaged as the functional equation
`momentPS (4 * X) = momentPS * sinhDivPS` between formal power series. -/
lemma momentPS_functional :
    PowerSeries.rescale 4 momentPS = momentPS * sinhDivPS := by
  ext n
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_mul]
  simp only [momentPS, sinhDivPS, PowerSeries.coeff_mk,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hleft :
      (((2 * n + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (2 * n) * moment n) /
          ((2 * n + 1).factorial : ℚ) =
        4 ^ n * (moment n / ((2 * n).factorial : ℚ)) := by
    rw [show 2 * n + 1 = (2 * n).succ by omega, Nat.factorial_succ]
    norm_num [pow_mul]
    field_simp
  have hterm (x : ℕ) (hx : x ∈ range n.succ) :
      ((Nat.choose (2 * n + 1) (2 * x) : ℚ) * moment x) /
          ((2 * n + 1).factorial : ℚ) =
        moment x / ((2 * x).factorial : ℚ) *
          (1 / ((2 * (n - x) + 1).factorial : ℚ)) := by
    have hxle : 2 * x ≤ 2 * n + 1 := by
      have : x ≤ n := Nat.le_of_lt_succ (mem_range.1 hx)
      omega
    rw [Nat.cast_choose ℚ hxle]
    have hsub : 2 * n + 1 - 2 * x = 2 * (n - x) + 1 := by
      have : x ≤ n := Nat.le_of_lt_succ (mem_range.1 hx)
      omega
    rw [hsub]
    field_simp
  have h := congrArg
    (fun q : ℚ => q / ((2 * n + 1).factorial : ℚ))
    (moment_original_recurrence n)
  rw [hleft] at h
  rw [Finset.sum_div] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro x hx
  exact hterm x hx

private noncomputable def expm1DivPSQ : PowerSeries ℚ :=
  PowerSeries.mk fun n => 1 / ((n + 1).factorial : ℚ)

private lemma X_mul_expm1DivPSQ :
    (PowerSeries.X : PowerSeries ℚ) * expm1DivPSQ =
      PowerSeries.exp ℚ - 1 := by
  ext (_ | n)
  · simp
  · simp [expm1DivPSQ, PowerSeries.coeff_exp]

private noncomputable def expandedSinhDivPS : PowerSeries ℚ :=
  PowerSeries.expand 2 (by omega) (PowerSeries.rescale (1 / 4) sinhDivPS)

private lemma X_mul_expandedSinhDivPS :
    (PowerSeries.X : PowerSeries ℚ) * expandedSinhDivPS =
      PowerSeries.rescale (1 / 2) (PowerSeries.exp ℚ) -
        PowerSeries.rescale (-1 / 2) (PowerSeries.exp ℚ) := by
  ext (_ | m)
  · rw [PowerSeries.coeff_zero_X_mul]
    simp only [map_sub, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
    norm_num
  · simp only [PowerSeries.coeff_succ_X_mul, expandedSinhDivPS,
      PowerSeries.coeff_expand, PowerSeries.coeff_rescale, sinhDivPS,
      PowerSeries.coeff_mk, map_sub, PowerSeries.coeff_exp]
    rcases m.even_or_odd with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [← two_mul k]
      simp
      norm_num [pow_succ, pow_mul, div_pow]
      ring
    · have hnot : ¬ 2 ∣ 2 * k + 1 := Nat.not_two_dvd_bit1 k
      rw [if_neg hnot]
      norm_num [pow_succ, pow_mul]

private lemma expm1DivPSQ_mul_exp_half :
    expm1DivPSQ * PowerSeries.rescale (1 / 2) (PowerSeries.exp ℚ) =
      PowerSeries.exp ℚ * expandedSinhDivPS := by
  apply PowerSeries.X_pow_mul_cancel (k := 1)
  simp only [pow_one]
  rw [← mul_assoc, X_mul_expm1DivPSQ]
  calc
    (PowerSeries.exp ℚ - 1) *
          PowerSeries.rescale (1 / 2) (PowerSeries.exp ℚ) =
        PowerSeries.exp ℚ *
            PowerSeries.rescale (1 / 2) (PowerSeries.exp ℚ) -
          PowerSeries.rescale (1 / 2) (PowerSeries.exp ℚ) := by ring
    _ = PowerSeries.exp ℚ *
        (PowerSeries.rescale (1 / 2) (PowerSeries.exp ℚ) -
          PowerSeries.rescale (-1 / 2) (PowerSeries.exp ℚ)) := by
      have h : PowerSeries.exp ℚ *
          PowerSeries.rescale (-1 / 2) (PowerSeries.exp ℚ) =
            PowerSeries.rescale (1 / 2) (PowerSeries.exp ℚ) := by
        convert
          (PowerSeries.exp_mul_exp_eq_exp_add (A := ℚ) (1 : ℚ) (-1 / 2))
            using 1 <;> norm_num
      rw [mul_sub, h]
    _ = (PowerSeries.X : PowerSeries ℚ) *
        (PowerSeries.exp ℚ * expandedSinhDivPS) := by
      rw [← X_mul_expandedSinhDivPS]
      ring

private noncomputable def expandedMomentQuarter : PowerSeries ℚ :=
  PowerSeries.expand 2 (by omega) (PowerSeries.rescale (1 / 4) momentPS)

private lemma rescale_two_expandedMomentQuarter :
    PowerSeries.rescale 2 expandedMomentQuarter =
      PowerSeries.expand 2 (by omega) momentPS := by
  ext m
  simp only [PowerSeries.coeff_rescale, expandedMomentQuarter,
    PowerSeries.coeff_expand]
  split_ifs with hm
  · obtain ⟨k, rfl⟩ := hm
    norm_num [pow_mul, div_pow]
  · simp

private lemma expandedSinhDivPS_mul_expandedMomentQuarter :
    expandedSinhDivPS * expandedMomentQuarter =
      PowerSeries.expand 2 (by omega) momentPS := by
  rw [expandedSinhDivPS, expandedMomentQuarter]
  rw [← map_mul]
  congr 1
  rw [← map_mul]
  rw [mul_comm sinhDivPS momentPS, ← momentPS_functional]
  rw [PowerSeries.rescale_rescale]
  norm_num

private noncomputable def halfMomentCandidatePS : PowerSeries ℚ :=
  PowerSeries.rescale (1 / 2) (PowerSeries.exp ℚ) * expandedMomentQuarter

private lemma halfMomentCandidatePS_functional :
    PowerSeries.rescale 2 halfMomentCandidatePS =
      expm1DivPSQ * halfMomentCandidatePS := by
  rw [halfMomentCandidatePS, map_mul]
  rw [PowerSeries.rescale_rescale, rescale_two_expandedMomentQuarter]
  norm_num
  rw [← mul_assoc, expm1DivPSQ_mul_exp_half]
  rw [mul_assoc, expandedSinhDivPS_mul_expandedMomentQuarter]

private lemma sum_range_even_div_two {R : Type*} [AddCommMonoid R]
    (n : ℕ) (f : ℕ → R) :
    (∑ x ∈ range (n + 1), if 2 ∣ x then f (x / 2) else 0) =
      ∑ k ∈ range (n / 2 + 1), f k := by
  rw [← Finset.sum_filter]
  have hfilter :
      (range (n + 1)).filter (fun x => 2 ∣ x) =
        (range (n / 2 + 1)).image (fun k => 2 * k) := by
    ext x
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hx, ⟨k, rfl⟩⟩
      refine ⟨k, ?_, rfl⟩
      omega
    · rintro ⟨k, hk, rfl⟩
      refine ⟨by omega, ⟨k, rfl⟩⟩
  rw [hfilter, Finset.sum_image]
  · simp
  · intro a _ b _ hab
    change 2 * a = 2 * b at hab
    omega

private lemma coeff_exp_mul_expandedMomentQuarter (y : ℚ) (n : ℕ) :
    PowerSeries.coeff n
      (PowerSeries.rescale y (PowerSeries.exp ℚ) * expandedMomentQuarter) =
      (1 / ((2 : ℚ) ^ n * (n.factorial : ℚ))) *
        ∑ k ∈ range (n / 2 + 1),
          (Nat.choose n (2 * k) : ℚ) *
            (2 * y) ^ (n - 2 * k) * moment k := by
  rw [mul_comm, PowerSeries.coeff_mul]
  simp only [Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    expandedMomentQuarter, PowerSeries.coeff_expand,
    PowerSeries.coeff_rescale, momentPS, PowerSeries.coeff_mk,
    PowerSeries.coeff_exp]
  simp only [ite_mul, zero_mul]
  have hnormalize :
      (∑ x ∈ range n.succ,
        if 2 ∣ x then
          (1 / 4 : ℚ) ^ (x / 2) *
              (moment (x / 2) / ((2 * (x / 2)).factorial : ℚ)) *
            (y ^ (n - x) *
              (algebraMap ℚ ℚ) (1 / ((n - x).factorial : ℚ)))
        else 0) =
      ∑ x ∈ range (n + 1), if 2 ∣ x then
        ((1 / 4 : ℚ) ^ (x / 2) *
            (moment (x / 2) / ((2 * (x / 2)).factorial : ℚ))) *
          (y ^ (n - 2 * (x / 2)) *
            (1 / ((n - 2 * (x / 2)).factorial : ℚ)))
        else 0 := by
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hdiv : 2 ∣ x
    · obtain ⟨k, rfl⟩ := hdiv
      simp
    · simp [hdiv]
  rw [hnormalize]
  rw [sum_range_even_div_two n (fun k =>
    ((1 / 4 : ℚ) ^ k * (moment k / ((2 * k).factorial : ℚ))) *
      (y ^ (n - 2 * k) *
        (1 / ((n - 2 * k).factorial : ℚ))))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : 2 * k ≤ n := by
    have : k ≤ n / 2 := Nat.le_of_lt_succ (mem_range.1 hk)
    omega
  rw [Nat.cast_choose ℚ hk']
  norm_num [div_pow, pow_mul]
  field_simp
  have hn : n = 2 * k + (n - 2 * k) :=
    (Nat.add_sub_of_le hk').symm
  rw [hn, pow_add]
  norm_num [pow_mul]
  ring

private lemma coeff_halfMomentCandidatePS (n : ℕ) :
    PowerSeries.coeff n halfMomentCandidatePS =
      (∑ k ∈ range (n / 2 + 1),
          (Nat.choose n (2 * k) : ℚ) * moment k) /
        ((2 : ℚ) ^ n * (n.factorial : ℚ)) := by
  rw [halfMomentCandidatePS, coeff_exp_mul_expandedMomentQuarter]
  norm_num
  ring

/-- The centered even-moment series
`sum moment(k) X^(2k) / (4^k (2k)!)`.  Multiplication by `exp(X/2)`
recovers the factorially normalized half-moment series. -/
noncomputable def centeredMomentPowerSeries : PowerSeries ℚ :=
  expandedMomentQuarter

/-- The even coefficients of the centered series are the factorially
normalized moments, with the centering scale `4^n`. -/
@[simp] theorem coeff_centeredMomentPowerSeries_even (n : ℕ) :
    PowerSeries.coeff (2 * n) centeredMomentPowerSeries =
      moment n / ((4 : ℚ) ^ n * ((2 * n).factorial : ℚ)) := by
  simp [centeredMomentPowerSeries, expandedMomentQuarter, momentPS]
  ring

/-- The centered moment series has no odd-degree coefficients. -/
@[simp] theorem coeff_centeredMomentPowerSeries_odd (n : ℕ) :
    PowerSeries.coeff (2 * n + 1) centeredMomentPowerSeries = 0 := by
  rw [centeredMomentPowerSeries, expandedMomentQuarter]
  apply PowerSeries.coeff_expand_of_not_dvd
  exact Nat.not_two_dvd_bit1 n

/-- Coefficients after translating the centered even-moment series by an
arbitrary rational amount. -/
theorem coeff_exp_mul_centeredMomentPowerSeries (y : ℚ) (n : ℕ) :
    PowerSeries.coeff n
      (PowerSeries.rescale y (PowerSeries.exp ℚ) *
        centeredMomentPowerSeries) =
      (1 / ((2 : ℚ) ^ n * (n.factorial : ℚ))) *
        ∑ k ∈ range (n / 2 + 1),
          (Nat.choose n (2 * k) : ℚ) *
            (2 * y) ^ (n - 2 * k) * moment k := by
  simpa only [centeredMomentPowerSeries] using
    coeff_exp_mul_expandedMomentQuarter y n

/-- Coefficients after translating the centered moment series by `1/2`.
This is the even-binomial transform appearing in Proposition 3. -/
theorem coeff_expHalf_mul_centeredMomentPowerSeries (n : ℕ) :
    PowerSeries.coeff n
        (PowerSeries.rescale (1 / 2) (PowerSeries.exp ℚ) *
          centeredMomentPowerSeries) =
      (∑ k ∈ range (n / 2 + 1),
          (Nat.choose n (2 * k) : ℚ) * moment k) /
        ((2 : ℚ) ^ n * (n.factorial : ℚ)) := by
  simpa only [centeredMomentPowerSeries, halfMomentCandidatePS] using
    coeff_halfMomentCandidatePS n

private def halfMomentCandidate (n : ℕ) : ℚ :=
  (∑ k ∈ range (n / 2 + 1),
      (Nat.choose n (2 * k) : ℚ) * moment k) / (2 : ℚ) ^ n

private lemma coeff_halfMomentCandidatePS' (n : ℕ) :
    PowerSeries.coeff n halfMomentCandidatePS =
      halfMomentCandidate n / (n.factorial : ℚ) := by
  rw [coeff_halfMomentCandidatePS, halfMomentCandidate]
  field_simp

private lemma halfMomentCandidate_original_recurrence (n : ℕ) :
    (((n + 1 : ℕ) : ℚ) * (2 : ℚ) ^ n) * halfMomentCandidate n =
      ∑ k ∈ range (n + 1),
        (Nat.choose (n + 1) k : ℚ) * halfMomentCandidate k := by
  have hfun : PowerSeries.rescale 2 halfMomentCandidatePS =
      halfMomentCandidatePS * expm1DivPSQ := by
    simpa [mul_comm] using halfMomentCandidatePS_functional
  have h := congrArg (PowerSeries.coeff n) hfun
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_mul,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk, expm1DivPSQ,
    PowerSeries.coeff_mk] at h
  simp_rw [coeff_halfMomentCandidatePS'] at h
  have hleft :
      ((n + 1).factorial : ℚ) *
          ((2 : ℚ) ^ n *
            (halfMomentCandidate n / (n.factorial : ℚ))) =
        (((n + 1 : ℕ) : ℚ) * (2 : ℚ) ^ n) *
          halfMomentCandidate n := by
    rw [Nat.factorial_succ]
    field_simp
    push_cast
    ring
  have hterm (k : ℕ) (hk : k ∈ range (n + 1)) :
      ((n + 1).factorial : ℚ) *
          (halfMomentCandidate k / (k.factorial : ℚ) *
            (1 / ((n - k + 1).factorial : ℚ))) =
        (Nat.choose (n + 1) k : ℚ) * halfMomentCandidate k := by
    have hkn : k ≤ n := Nat.le_of_lt_succ (mem_range.1 hk)
    have hk' : k ≤ n + 1 := hkn.trans (Nat.le_succ n)
    rw [Nat.cast_choose ℚ hk']
    have hsub : n + 1 - k = n - k + 1 := by omega
    rw [hsub]
    field_simp
  calc
    (((n + 1 : ℕ) : ℚ) * (2 : ℚ) ^ n) * halfMomentCandidate n =
        ((n + 1).factorial : ℚ) *
          ((2 : ℚ) ^ n *
            (halfMomentCandidate n / (n.factorial : ℚ))) := hleft.symm
    _ = ((n + 1).factorial : ℚ) *
        (∑ x ∈ range n.succ,
          halfMomentCandidate x / (x.factorial : ℚ) *
            (1 / ((n - x + 1).factorial : ℚ))) := by rw [h]
    _ = ∑ k ∈ range (n + 1),
        (Nat.choose (n + 1) k : ℚ) * halfMomentCandidate k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      exact hterm k hk

@[simp] private lemma halfMomentCandidate_zero : halfMomentCandidate 0 = 1 := by
  norm_num [halfMomentCandidate, moment]

private lemma halfMomentCandidate_succ (n : ℕ) :
    halfMomentCandidate (n + 1) =
      (∑ k : Fin (n + 1),
          (Nat.choose (n + 2) k.val : ℚ) * halfMomentCandidate k.val) /
        (((n + 2 : ℕ) : ℚ) * ((2 : ℚ) ^ (n + 1) - 1)) := by
  have h := halfMomentCandidate_original_recurrence (n + 1)
  rw [Fin.sum_univ_eq_sum_range
    (fun k => (Nat.choose (n + 2) k : ℚ) * halfMomentCandidate k) (n + 1)]
  rw [sum_range_succ] at h
  have hchoose : (n + 2).choose (n + 1) = n + 2 := by
    exact Nat.choose_succ_self_right (n + 1)
  rw [hchoose] at h
  have hpow : (2 : ℚ) ^ (n + 1) - 1 ≠ 0 := by
    apply ne_of_gt
    exact sub_pos.mpr (one_lt_pow₀ (by norm_num) (by omega))
  have hfactor : ((n + 2 : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp
  push_cast at h ⊢
  linear_combination h

/-- Proposition 3: the half moments are the even-binomial transform of the moments. -/
theorem halfMoment_eq_evenMomentSum (n : ℕ) :
    halfMoment n =
      (∑ k ∈ range (n / 2 + 1),
        (Nat.choose n (2 * k) : ℚ) * moment k) / (2 : ℚ) ^ n := by
  change halfMoment n = halfMomentCandidate n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp
      | succ n =>
          rw [halfMoment_succ, halfMomentCandidate_succ]
          congr 1
          apply Finset.sum_congr rfl
          intro k hk
          rw [ih k.val k.isLt]

/-- Multiplying the centered moment series by `exp(X/2)` produces the
factorially normalized half-moment series coefficient by coefficient. -/
theorem coeff_expHalf_mul_centeredMomentPowerSeries_eq_halfMoment (n : ℕ) :
    PowerSeries.coeff n
        (PowerSeries.rescale (1 / 2) (PowerSeries.exp ℚ) *
          centeredMomentPowerSeries) =
      halfMoment n / (n.factorial : ℚ) := by
  rw [coeff_expHalf_mul_centeredMomentPowerSeries,
    halfMoment_eq_evenMomentSum]
  field_simp

/-- Odd half moments reduce to a single even moment. -/
theorem halfMoment_odd_eq_moment (n : ℕ) :
    halfMoment (2 * n + 1) = ((2 * n + 1 : ℕ) : ℚ) / 2 * moment n := by
  rw [halfMoment_eq_evenMomentSum]
  rw [show (2 * n + 1) / 2 = n by omega]
  have h := moment_original_recurrence n
  rw [← h]
  rw [pow_succ]
  field_simp

/-- Equation (32) at numerator one agrees with the half-moment formula (22). -/
theorem fabiusAtInverseTwoPow_eq_halfMoment (n : ℕ) :
    fabiusAtInverseTwoPow n = halfMomentFabiusValue n := by
  rw [fabiusAtInverseTwoPow, fabiusDyadic, halfMomentFabiusValue,
    halfMoment_eq_evenMomentSum]
  norm_num [thueMorseSign, binaryWeight]
  rw [Fin.sum_univ_eq_sum_range
    (fun k => (Nat.choose n (2 * k) : ℚ) * moment k) (n / 2 + 1)]
  have hchoose : (n + 1).choose 2 = n + n.choose 2 := by
    simp [Nat.choose_succ_succ, Nat.choose_one_right]
  rw [hchoose, pow_add]
  field_simp

end Fabius

```

### `UpstreamNormalizedEvenMoments.lean`

```lean
import UpstreamMomentPowerSeries

/-!
# Natural normalization of the even moments

This module proves, entirely in exact arithmetic, that the division-free
natural recurrence `momentNumerator` gives the numerator normalization of the
rational moment recurrence `moment` from Proposition 1 of the paper.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

private def momentDenominator (n : ℕ) : ℕ :=
  oddDoubleFactorial (n + 1) * evenMersenneProduct n

/-- Rewrite the initial even-indexed Mersenne product as a product over
`[1, n + 1)`. -/
theorem evenMersenneProduct_eq_prod_Ico (n : ℕ) :
    evenMersenneProduct n =
      ∏ j ∈ Ico 1 (n + 1), (2 ^ (2 * j) - 1) := by
  simp [evenMersenneProduct, Finset.prod_Ico_eq_prod_range, add_comm]

/-- Split an odd double factorial at an arbitrary index. -/
theorem oddDoubleFactorial_mul_interval (a b : ℕ) (hab : a ≤ b) :
    oddDoubleFactorial a * oddFactorProduct a b = oddDoubleFactorial b := by
  simpa [oddDoubleFactorial, oddFactorProduct] using
    (Finset.prod_range_mul_prod_Ico (fun j => 2 * j + 1) hab)

/-- Split the even-indexed Mersenne product at an arbitrary index. -/
theorem evenMersenneProduct_mul_interval (k n : ℕ) (hkn : k ≤ n) :
    evenMersenneProduct k *
        (∏ j ∈ Ico (k + 1) (n + 1), (2 ^ (2 * j) - 1)) =
      evenMersenneProduct n := by
  rw [evenMersenneProduct_eq_prod_Ico, evenMersenneProduct_eq_prod_Ico]
  exact Finset.prod_Ico_consecutive (fun j => 2 ^ (2 * j) - 1)
    (by omega) (Nat.succ_le_succ hkn)

private lemma momentDenominator_mul_tail (k n : ℕ) (hkn : k ≤ n) :
    momentDenominator k *
        (oddFactorProduct (k + 1) (n + 1) *
          (∏ j ∈ Ico (k + 1) (n + 1), (2 ^ (2 * j) - 1))) =
      oddDoubleFactorial (n + 1) * evenMersenneProduct n := by
  have hodd := oddDoubleFactorial_mul_interval (k + 1) (n + 1)
    (Nat.succ_le_succ hkn)
  have hmrs := evenMersenneProduct_mul_interval k n hkn
  unfold momentDenominator
  calc
    oddDoubleFactorial (k + 1) * evenMersenneProduct k *
          (oddFactorProduct (k + 1) (n + 1) *
            ∏ j ∈ Ico (k + 1) (n + 1), (2 ^ (2 * j) - 1)) =
        (oddDoubleFactorial (k + 1) * oddFactorProduct (k + 1) (n + 1)) *
          (evenMersenneProduct k *
            ∏ j ∈ Ico (k + 1) (n + 1), (2 ^ (2 * j) - 1)) := by
              ring
    _ = oddDoubleFactorial (n + 1) * evenMersenneProduct n := by
      rw [hodd, hmrs]

private lemma momentDenominator_succ (n : ℕ) :
    momentDenominator (n + 1) =
      ((2 * (n + 1) + 1) * (2 ^ (2 * (n + 1)) - 1)) *
        momentDenominator n := by
  rw [momentDenominator, oddDoubleFactorial_succ, evenMersenneProduct_succ_eq,
    momentDenominator]
  ring

private lemma momentDenominator_pos (n : ℕ) : 0 < momentDenominator n := by
  exact Nat.mul_pos (oddDoubleFactorial_pos _) (evenMersenneProduct_pos _)

/-- Split an odd double factorial at its middle factor. -/
theorem oddDoubleFactorial_mul_Icc (n : ℕ) :
    (2 * n + 1) * oddDoubleFactorial (2 * n + 1) =
      oddDoubleFactorial (n + 1) *
        ∏ j ∈ Icc n (2 * n), (2 * j + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  unfold oddDoubleFactorial
  have h := Finset.prod_range_mul_prod_Ico (fun j => 2 * j + 1)
    (show n ≤ 2 * n + 1 by omega)
  rw [← h]
  rw [Finset.prod_range_succ]
  ring

/-- Casting an even-indexed Mersenne factor from `ℕ` to `ℚ`. -/
theorem mersenneFactor_cast (j : ℕ) :
    (((2 ^ (2 * j) - 1 : ℕ) : ℚ)) = (2 : ℚ) ^ (2 * j) - 1 := by
  rw [Nat.cast_sub (show 1 ≤ 2 ^ (2 * j) by exact one_le_pow₀ (by omega))]
  norm_num

/--
The division-free natural sequence `momentNumerator` is exactly the numerator
normalization of the rational moment sequence.
-/
theorem moment_eq_momentNumerator_div (n : ℕ) :
    moment n =
      (momentNumerator n : ℚ) /
        ((oddDoubleFactorial (n + 1) * evenMersenneProduct n : ℕ) : ℚ) := by
  change moment n = (momentNumerator n : ℚ) / (momentDenominator n : ℚ)
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => norm_num [moment, momentNumerator, momentDenominator,
          oddDoubleFactorial, evenMersenneProduct]
      | succ n =>
          rw [moment_succ, momentNumerator_succ]
          rw [Nat.cast_sum, Finset.sum_div, Finset.sum_div]
          apply Finset.sum_congr rfl
          intro k hk
          rw [ih k.val k.isLt]
          push_cast
          let tail : ℕ :=
            oddFactorProduct (k.val + 1) (n + 1) *
              ∏ j ∈ Ico (k.val + 1) (n + 1), (2 ^ (2 * j) - 1)
          have htail : momentDenominator k.val * tail = momentDenominator n := by
            exact momentDenominator_mul_tail k.val n
              (Nat.le_of_lt_succ k.isLt)
          have hdenNat :
              ((2 * (n + 1) + 1) * (2 ^ (2 * (n + 1)) - 1)) *
                    momentDenominator k.val * tail =
                momentDenominator (n + 1) := by
            calc
              ((2 * (n + 1) + 1) * (2 ^ (2 * (n + 1)) - 1)) *
                    momentDenominator k.val * tail =
                  ((2 * (n + 1) + 1) * (2 ^ (2 * (n + 1)) - 1)) *
                    (momentDenominator k.val * tail) := by ring
              _ = ((2 * (n + 1) + 1) * (2 ^ (2 * (n + 1)) - 1)) *
                    momentDenominator n := by rw [htail]
              _ = momentDenominator (n + 1) := (momentDenominator_succ n).symm
          have hp : 1 ≤ 2 ^ (2 * (n + 1)) :=
            (Nat.one_lt_pow (by omega) (by omega)).le
          have hdenRat := congrArg (fun z : ℕ => (z : ℚ)) hdenNat
          push_cast [Nat.cast_sub hp] at hdenRat
          have hDk : ((momentDenominator k.val : ℕ) : ℚ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (momentDenominator_pos k.val))
          have hDs : ((momentDenominator (n + 1) : ℕ) : ℚ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (momentDenominator_pos (n + 1)))
          have hA : (2 * (n : ℚ) + 3) ≠ 0 := by positivity
          have hB : (2 : ℚ) ^ (2 * (n + 1)) - 1 ≠ 0 := by
            exact sub_ne_zero.mpr (ne_of_gt
              (one_lt_pow₀ (a := (2 : ℚ)) (by norm_num) (by omega)))
          have htailCast :
              (tail : ℚ) =
                (oddFactorProduct (k.val + 1) (n + 1) : ℚ) *
                  ∏ j ∈ Ico (k.val + 1) (n + 1), ((2 ^ (2 * j) - 1 : ℕ) : ℚ) := by
            simp [tail]
          have hnum :
              (momentNumerator k.val : ℚ) *
                    ((2 * (n + 1) + 1).choose (2 * k.val) : ℚ) *
                    (oddFactorProduct (k.val + 1) (n + 1) : ℚ) *
                    ∏ j ∈ Ico (k.val + 1) (n + 1),
                      ((2 ^ (2 * j) - 1 : ℕ) : ℚ) =
                (momentNumerator k.val : ℚ) *
                  ((2 * (n + 1) + 1).choose (2 * k.val) : ℚ) *
                  (tail : ℚ) := by
            rw [htailCast]
            ring
          rw [hnum]
          field_simp [hDk, hDs, hA, hB]
          rw [← hdenRat]
          ring

/-- The reduced denominator of `moment n` divides its natural normalization.
This packages the exact quotient formula in a form convenient for subsequent
denominator arguments. -/
theorem moment_den_dvd_normalization (n : ℕ) :
    (moment n).den ∣
      oddDoubleFactorial (n + 1) * evenMersenneProduct n := by
  rw [moment_eq_momentNumerator_div]
  exact rat_den_dvd_nat_div _ _

end Fabius

```

### `UpstreamParity.lean`

```lean
import UpstreamArithmetic
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Nat.Choose.Lucas

/-!
# Parity of the Fabius moment numerators

This file proves the binary-coefficient count in Proposition 18 of
Arias de Reyna's *Arithmetic of the Fabius function* and uses it to prove
that every integral moment numerator `momentNumerator n` is odd.

The proofs are entirely in the exact-arithmetic layer.  Lucas's theorem at
the prime `2` gives the binary recurrences for odd binomial coefficients;
the recurrence defining `momentNumerator` then reduces modulo `2` to one of
those counts.  Besides the full-row formulas, the module records the exact
truncated odd-coefficient count used by the two-adic half-moment recurrence
and a reusable bridge between filters on `Fin N` and `range N`.  Lucas's
theorem also shows that a power-of-two column probes one binary digit of the
row index; summing those columns recovers the Thue--Morse sign.
-/

set_option autoImplicit false

open scoped BigOperators Interval
open Finset

namespace Fabius

/-! ## Odd binomial coefficients -/

/-- The binary weight after adjoining a low binary digit to a positive prefix. -/
theorem binaryWeight_bit (b : Bool) (n : ℕ) (hn : n ≠ 0) :
    binaryWeight (Nat.bit b n) = binaryWeight n + if b then 1 else 0 := by
  unfold binaryWeight
  rw [Nat.digits_two_eq_bits, Nat.digits_two_eq_bits,
    Nat.bits_append_bit n b (fun h => (hn h).elim)]
  cases b <;> simp [Nat.add_comm]

/-- Lucas's theorem for an even entry in an odd-indexed binomial row. -/
theorem odd_choose_two_mul_left (n k : ℕ) :
    Odd (Nat.choose (2 * n + 1) (2 * k)) ↔ Odd (Nat.choose n k) := by
  rw [Nat.odd_iff, Nat.odd_iff]
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (2 * n + 1) (2 * k) 2 inferInstance
  change Nat.choose (2 * n + 1) (2 * k) % 2 = _ at h
  have hn : (2 * n + 1) / 2 = n := by omega
  simp [hn] at h
  rw [h]

/-- Lucas's theorem for an odd entry in an odd-indexed binomial row. -/
theorem odd_choose_two_mul_add_one_left (n k : ℕ) :
    Odd (Nat.choose (2 * n + 1) (2 * k + 1)) ↔ Odd (Nat.choose n k) := by
  rw [Nat.odd_iff, Nat.odd_iff]
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (2 * n + 1) (2 * k + 1) 2 inferInstance
  change Nat.choose (2 * n + 1) (2 * k + 1) % 2 = _ at h
  have hn : (2 * n + 1) / 2 = n := by omega
  have hk : (2 * k + 1) / 2 = k := by omega
  simp [hn, hk] at h
  rw [h]

/-- Lucas's theorem for an even entry in an even-indexed binomial row. -/
theorem odd_choose_two_mul_even (n k : ℕ) :
    Odd (Nat.choose (2 * n) (2 * k)) ↔ Odd (Nat.choose n k) := by
  rw [Nat.odd_iff, Nat.odd_iff]
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (2 * n) (2 * k) 2 inferInstance
  change Nat.choose (2 * n) (2 * k) % 2 = _ at h
  simp at h
  rw [h]

/-- Odd-position entries in an even-indexed binomial row are even. -/
theorem not_odd_choose_two_mul_odd (n k : ℕ) :
    ¬ Odd (Nat.choose (2 * n) (2 * k + 1)) := by
  rw [Nat.odd_iff]
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (2 * n) (2 * k + 1) 2 inferInstance
  change Nat.choose (2 * n) (2 * k + 1) % 2 = _ at h
  simp at h
  omega

/-- Odd-position entries in an even-indexed binomial row are even. -/
theorem even_choose_two_mul_add_one (n k : ℕ) :
    Even (Nat.choose (2 * n) (2 * k + 1)) :=
  Nat.not_odd_iff_even.mp (not_odd_choose_two_mul_odd n k)

private theorem choose_pow_two_mod_two_div (n j : ℕ) :
    Nat.choose n (2 ^ j) % 2 = n / 2 ^ j % 2 := by
  induction j generalizing n with
  | zero => simp [Nat.choose_one_right]
  | succ j ih =>
      letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat
        n (2 ^ (j + 1)) 2 inferInstance
      change Nat.choose n (2 ^ (j + 1)) % 2 = _ at h
      calc
        Nat.choose n (2 ^ (j + 1)) % 2 =
            Nat.choose (n / 2) (2 ^ j) % 2 := by
              simpa [pow_succ] using h
        _ = (n / 2) / 2 ^ j % 2 := ih (n := n / 2)
        _ = n / 2 ^ (j + 1) % 2 := by
              rw [Nat.div_div_eq_div_mul, pow_succ']

/-- Lucas at a power-of-two column: the binomial residue is the corresponding
binary digit of the row index. -/
theorem choose_pow_two_mod_two (n j : ℕ) :
    Nat.choose n (2 ^ j) % 2 = (Nat.digits 2 n).getD j 0 := by
  rw [Nat.getD_digits n j (by norm_num : 2 ≤ 2)]
  exact choose_pow_two_mod_two_div n j

private lemma sum_getD_range_length (L : List ℕ) :
    (∑ j ∈ range L.length, L.getD j 0) = L.sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      rw [List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero, List.sum_cons]
      rw [ih]
      exact Nat.add_comm _ _

/-- The Thue--Morse sign is the parity character of the power-of-two columns
in the corresponding row of Pascal's triangle.  The range stops at the binary
digit length; every omitted `2 ^ j` exceeds `n`, so its binomial coefficient
vanishes. -/
theorem thueMorseSign_pascalPowTwo (n : ℕ) :
    thueMorseSign n =
      (-1 : ℤ) ^ ∑ j ∈ range (Nat.digits 2 n).length,
        Nat.choose n (2 ^ j) := by
  have hsum : Nat.ModEq 2
      (∑ j ∈ range (Nat.digits 2 n).length, Nat.choose n (2 ^ j))
      (∑ j ∈ range (Nat.digits 2 n).length,
        (Nat.digits 2 n).getD j 0) := by
    apply Nat.ModEq.sum
    intro j _hj
    change Nat.choose n (2 ^ j) % 2 = (Nat.digits 2 n).getD j 0 % 2
    rw [choose_pow_two_mod_two,
      Nat.getD_digits n j (by norm_num : 2 ≤ 2), Nat.mod_mod]
  rw [sum_getD_range_length] at hsum
  change
    (∑ j ∈ range (Nat.digits 2 n).length,
      Nat.choose n (2 ^ j)) % 2 = binaryWeight n % 2 at hsum
  rw [thueMorseSign]
  calc
    (-1 : ℤ) ^ binaryWeight n =
        (-1 : ℤ) ^ (binaryWeight n % 2) :=
      neg_one_pow_eq_pow_mod_two (R := ℤ) (binaryWeight n)
    _ = (-1 : ℤ) ^
        ((∑ j ∈ range (Nat.digits 2 n).length,
          Nat.choose n (2 ^ j)) % 2) := by
      rw [hsum]
    _ = (-1 : ℤ) ^ ∑ j ∈ range (Nat.digits 2 n).length,
        Nat.choose n (2 ^ j) :=
      (neg_one_pow_eq_pow_mod_two (R := ℤ)
        (∑ j ∈ range (Nat.digits 2 n).length,
          Nat.choose n (2 ^ j))).symm

/-- The indices of the odd coefficients in row `n` of Pascal's triangle. -/
def oddBinomialIndices (n : ℕ) : Finset ℕ :=
  (range (n + 1)).filter (fun k => Odd (Nat.choose n k))

/-- Doubling the row index preserves the number of odd binomial coefficients. -/
theorem card_oddBinomialIndices_two_mul (n : ℕ) :
    (oddBinomialIndices (2 * n)).card = (oddBinomialIndices n).card := by
  symm
  apply Finset.card_bij (fun k _ => 2 * k)
  · intro k hk
    simp only [oddBinomialIndices, mem_filter, mem_range] at hk ⊢
    constructor
    · omega
    · exact (odd_choose_two_mul_even n k).2 hk.2
  · intro a ha b hb hab
    omega
  · intro j hj
    simp only [oddBinomialIndices, mem_filter, mem_range] at hj
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' j
    · subst j
      refine ⟨k, ?_, rfl⟩
      simp only [oddBinomialIndices, mem_filter, mem_range]
      constructor
      · omega
      · exact (odd_choose_two_mul_even n k).1 hj.2
    · subst j
      exact (not_odd_choose_two_mul_odd n k hj.2).elim

/-- Passing from row `n` to row `2n+1` doubles the number of odd coefficients. -/
theorem card_oddBinomialIndices_two_mul_add_one (n : ℕ) :
    (oddBinomialIndices (2 * n + 1)).card = 2 * (oddBinomialIndices n).card := by
  let source : Finset (ℕ × Bool) := oddBinomialIndices n ×ˢ Finset.univ
  have hcard : source.card = (oddBinomialIndices (2 * n + 1)).card := by
    apply Finset.card_bij
      (fun kb _ => 2 * kb.1 + if kb.2 then 1 else 0)
    · intro kb hkb
      rcases kb with ⟨k, b⟩
      simp only [source, mem_product, mem_univ, and_true, oddBinomialIndices,
        mem_filter, mem_range] at hkb ⊢
      constructor
      · split <;> omega
      · cases b with
        | false => simpa using (odd_choose_two_mul_left n k).2 hkb.2
        | true => simpa using (odd_choose_two_mul_add_one_left n k).2 hkb.2
    · intro a ha b hb hab
      rcases a with ⟨a, ba⟩
      rcases b with ⟨b, bb⟩
      cases ba <;> cases bb <;> simp_all <;> omega
    · intro j hj
      simp only [oddBinomialIndices, mem_filter, mem_range] at hj
      obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' j
      · subst j
        refine ⟨(k, false), ?_, by simp⟩
        simp only [source, mem_product, mem_univ, and_true, oddBinomialIndices,
          mem_filter, mem_range]
        constructor
        · omega
        · exact (odd_choose_two_mul_left n k).1 hj.2
      · subst j
        refine ⟨(k, true), ?_, by simp⟩
        simp only [source, mem_product, mem_univ, and_true, oddBinomialIndices,
          mem_filter, mem_range]
        constructor
        · omega
        · exact (odd_choose_two_mul_add_one_left n k).1 hj.2
  rw [← hcard]
  simp [source, mul_comm]

/-- Row `n` of Pascal's triangle has exactly `2 ^ binaryWeight n` odd entries. -/
theorem card_oddBinomialIndices (n : ℕ) :
    (oddBinomialIndices n).card = 2 ^ binaryWeight n := by
  induction n using Nat.binaryRecFromOne with
  | zero => decide
  | one => decide
  | bit b n hn ih =>
      cases b with
      | false =>
          have hw := binaryWeight_bit false n hn
          simp [Nat.bit] at hw
          simpa [Nat.bit, hw] using card_oddBinomialIndices_two_mul n |>.trans ih
      | true =>
          have hw := binaryWeight_bit true n hn
          simp [Nat.bit] at hw
          rw [(show Nat.bit true n = 2 * n + 1 by simp [Nat.bit])]
          rw [card_oddBinomialIndices_two_mul_add_one, ih, hw]
          simp [pow_succ, mul_comm]

/--
The two odd-binomial-coefficient counts of Proposition 18.  The result is
valid also at `n = 0`, so no positivity hypothesis is needed here.
-/
theorem odd_binomial_coefficient_counts (n : ℕ) :
    ((range (n + 1)).filter
      (fun k => Odd (Nat.choose (2 * n + 1) (2 * k)))).card =
        2 ^ binaryWeight n ∧
    ((range (2 * n + 2)).filter
      (fun k => Odd (Nat.choose (2 * n + 1) k))).card =
        2 ^ (binaryWeight n + 1) := by
  constructor
  · simpa only [odd_choose_two_mul_left, oddBinomialIndices]
      using card_oddBinomialIndices n
  · change (oddBinomialIndices (2 * n + 1)).card = 2 ^ (binaryWeight n + 1)
    rw [card_oddBinomialIndices_two_mul_add_one, card_oddBinomialIndices]
    simp [pow_succ, mul_comm]

/-- The exact number of odd inner coefficients in row `2m + 1` of Pascal's
triangle after removing the constant term.  Relative to the full row, the
three discarded odd coefficients occur at indices `0`, `2m`, and `2m + 1`. -/
theorem card_odd_inner_binomial_coefficients (m : ℕ) (hm : 1 ≤ m) :
    ((range (2 * m)).filter (fun k =>
      k ≠ 0 ∧ Odd (Nat.choose (2 * m + 1) k))).card =
        2 ^ (binaryWeight m + 1) - 3 := by
  let p : ℕ → Prop := fun k => Odd (Nat.choose (2 * m + 1) k)
  let coeff : Finset ℕ := (range (2 * m)).filter p
  have hfull := (odd_binomial_coefficient_counts m).2
  have hlast : p (2 * m + 1) := by simp [p]
  have hpenultimate : p (2 * m) := by
    dsimp [p]
    rw [Nat.choose_succ_self_right]
    exact odd_two_mul_add_one m
  rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, Finset.range_add_one,
    Finset.filter_insert, if_pos hlast,
    Finset.card_insert_of_notMem (by simp)] at hfull
  rw [Finset.range_add_one, Finset.filter_insert, if_pos hpenultimate,
    Finset.card_insert_of_notMem (by simp)] at hfull
  have hzero : 0 ∈ coeff := by
    have hmpos : 0 < m := by omega
    simp [coeff, p, hmpos]
  have herase :
      (range (2 * m)).filter (fun k => k ≠ 0 ∧ p k) = coeff.erase 0 := by
    ext k
    simp only [mem_filter, mem_range, mem_erase, coeff, p]
    tauto
  rw [show ((range (2 * m)).filter (fun k =>
    k ≠ 0 ∧ Odd (Nat.choose (2 * m + 1) k))) = coeff.erase 0 by
      simpa only [p] using herase]
  have hcard := Finset.card_erase_add_one hzero
  change coeff.card + 1 + 1 = 2 ^ (binaryWeight m + 1) at hfull
  omega

/-- All-index form of `card_odd_inner_binomial_coefficients`: the count of odd
inner coefficients in row `2m + 1` of Pascal's triangle needs no positivity
hypothesis on `m`.  At `m = 0` the left-hand side filters the empty range and
the right-hand side is `2 ^ (0 + 1) - 3 = 0` by truncated natural subtraction,
so both sides vanish.  This mirrors `odd_binomial_coefficient_counts`, which is
likewise stated for every index. -/
theorem card_odd_inner_binomial_coefficients_all (m : ℕ) :
    ((range (2 * m)).filter (fun k =>
      k ≠ 0 ∧ Odd (Nat.choose (2 * m + 1) k))).card =
        2 ^ (binaryWeight m + 1) - 3 := by
  cases m with
  | zero => decide
  | succ m => exact card_odd_inner_binomial_coefficients (m + 1) (by omega)

/-! ## Oddness of the moment numerators -/

private lemma sum_modEq_card_filter_odd {alpha : Type*} [DecidableEq alpha]
    (s : Finset alpha) (f : alpha → ℕ) :
    (∑ x ∈ s, f x) ≡ (s.filter (fun x => Odd (f x))).card [MOD 2] := by
  induction s using Finset.induction_on with
  | empty => simp [Nat.ModEq.refl]
  | @insert a s ha ih =>
      by_cases hodd : Odd (f a)
      · have hfa : f a ≡ 1 [MOD 2] := by
          change f a % 2 = 1
          exact Nat.odd_iff.mp hodd
        rw [sum_insert ha, Finset.filter_insert, if_pos hodd,
          Finset.card_insert_of_notMem (by simp [ha]), Nat.add_comm]
        simpa [Nat.add_comm] using hfa.add ih
      · have hfa : f a ≡ 0 [MOD 2] := by
          change f a % 2 = 0
          exact Nat.mod_two_not_eq_one.mp (by simpa [Nat.odd_iff] using hodd)
        rw [sum_insert ha, Finset.filter_insert, if_neg hodd]
        simpa using hfa.add ih

private lemma binaryWeight_pos (n : ℕ) (hn : 0 < n) : 0 < binaryWeight n := by
  induction n using Nat.binaryRecFromOne with
  | zero => omega
  | one => decide
  | bit b n hn0 ih =>
      rw [binaryWeight_bit b n hn0]
      exact lt_of_lt_of_le (ih (Nat.pos_of_ne_zero hn0)) (Nat.le_add_right _ _)

/-- Filtering `Fin N` by a predicate on values has the same cardinality as
filtering `range N` by that predicate. -/
theorem card_filter_fin_eq_range (N : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ((Finset.univ : Finset (Fin N)).filter (fun k => p k.val)).card =
      ((range N).filter p).card := by
  apply Finset.card_bij (fun k _ => k.val)
  · intro k hk
    simp only [mem_filter, mem_univ, true_and] at hk
    exact mem_filter.2 ⟨mem_range.2 k.isLt, hk⟩
  · intro a ha b hb hab
    exact Fin.ext hab
  · intro j hj
    simp only [mem_filter, mem_range] at hj
    refine ⟨⟨j, hj.1⟩, ?_, rfl⟩
    simp only [mem_filter, mem_univ, true_and]
    exact hj.2

private lemma odd_oddFactorProduct (a b : ℕ) : Odd (oddFactorProduct a b) := by
  unfold oddFactorProduct
  apply Finset.prod_induction (fun j : ℕ => 2 * j + 1) Odd
  · exact fun _ _ => Odd.mul
  · exact odd_one
  · intro j hj
    exact odd_two_mul_add_one j

private lemma odd_mersenne_product (a b : ℕ) (ha : 1 ≤ a) :
    Odd (∏ j ∈ Ico a b, (2 ^ (2 * j) - 1)) := by
  apply Finset.prod_induction (fun j : ℕ => 2 ^ (2 * j) - 1) Odd
  · exact fun _ _ => Odd.mul
  · exact odd_one
  · intro j hj
    exact two_pow_sub_one_odd (by simp only [mem_Ico] at hj; omega)

/-- Every integral moment numerator `F_n` from Proposition 1 is odd. -/
theorem momentNumerator_odd (n : ℕ) : Odd (momentNumerator n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [momentNumerator]
    | succ n =>
      rw [momentNumerator_succ]
      let term : Fin (n + 1) → ℕ := fun k =>
        momentNumerator k.val * Nat.choose (2 * (n + 1) + 1) (2 * k.val) *
          oddFactorProduct (k.val + 1) (n + 1) *
          (∏ j ∈ Ico (k.val + 1) (n + 1), (2 ^ (2 * j) - 1))
      have hterm (k : Fin (n + 1)) :
          Odd (term k) ↔ Odd (Nat.choose (2 * (n + 1) + 1) (2 * k.val)) := by
        have hFk : Odd (momentNumerator k.val) := ih k.val k.isLt
        have hoddFactors : Odd (oddFactorProduct (k.val + 1) (n + 1)) :=
          odd_oddFactorProduct _ _
        have hoddMersenne :
            Odd (∏ j ∈ Ico (k.val + 1) (n + 1), (2 ^ (2 * j) - 1)) :=
          odd_mersenne_product _ _ (by omega)
        simp only [term, Nat.odd_mul]
        simp [hFk, hoddFactors, hoddMersenne]
      have hmod := sum_modEq_card_filter_odd
        (Finset.univ : Finset (Fin (n + 1))) term
      simp_rw [hterm] at hmod
      have hfinCard := card_filter_fin_eq_range (n + 1)
        (fun k => Odd (Nat.choose (2 * (n + 1) + 1) (2 * k)))
      have hfull := (odd_binomial_coefficient_counts (n + 1)).1
      have hlast : Odd (Nat.choose (2 * (n + 1) + 1) (2 * (n + 1))) := by
        exact (odd_choose_two_mul_left (n + 1) (n + 1)).2 (by simp)
      have hcount :
          ((range (n + 1)).filter
            (fun k => Odd (Nat.choose (2 * (n + 1) + 1) (2 * k)))).card + 1 =
            2 ^ binaryWeight (n + 1) := by
        rw [Finset.range_add_one, Finset.filter_insert, if_pos hlast,
          Finset.card_insert_of_notMem (by simp)] at hfull
        omega
      have htruncated :
          ((range (n + 1)).filter
            (fun k => Odd (Nat.choose (2 * (n + 1) + 1) (2 * k)))).card =
            2 ^ binaryWeight (n + 1) - 1 := by
        omega
      have hcardOdd :
          Odd (((Finset.univ : Finset (Fin (n + 1))).filter
            (fun k => Odd (Nat.choose (2 * (n + 1) + 1) (2 * k.val)))).card) := by
        rw [hfinCard, htruncated]
        exact two_pow_sub_one_odd (binaryWeight_pos (n + 1) (by omega))
      rw [Nat.odd_iff]
      change (∑ k : Fin (n + 1), term k) % 2 = 1
      calc
        (∑ k : Fin (n + 1), term k) % 2 =
            ((Finset.univ : Finset (Fin (n + 1))).filter
              (fun k => Odd (Nat.choose (2 * (n + 1) + 1) (2 * k.val)))).card % 2 := hmod
        _ = 1 := Nat.odd_iff.mp hcardOdd

/-- The integral moment numerator is congruent to one modulo two. -/
@[simp] theorem momentNumerator_mod_two (n : ℕ) : momentNumerator n % 2 = 1 :=
  Nat.odd_iff.mp (momentNumerator_odd n)

/-- Every integral moment numerator is strictly positive. -/
theorem momentNumerator_pos (n : ℕ) : 0 < momentNumerator n :=
  (momentNumerator_odd n).pos

/-- In particular, no integral moment numerator vanishes. -/
theorem momentNumerator_ne_zero (n : ℕ) : momentNumerator n ≠ 0 :=
  Nat.ne_of_gt (momentNumerator_pos n)

end Fabius

```

### `UpstreamTwoAdic.lean`

```lean
import UpstreamNormalizedEvenMoments
import UpstreamParity
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Two-adic parity of the half moments

This file proves the exact numerator and denominator parity asserted in
Theorem 20 of Arias de Reyna's *Arithmetic of the Fabius function*.  The odd
indices reduce to the normalized even moments.  At an even index, the
recurrence for `halfMoment` reduces parity to the number of odd entries in an
odd-indexed row of Pascal's triangle, supplied by `FabiusFunction.Parity`.

The final section converts the parity result into the dyadic valuation of the
Fabius value at `2⁻ⁿ`, the valuation component of Theorem 21.  Parameter-free
forms isolate the exceptional zeroth half moment, and Legendre's formula at
`p = 2` removes the remaining factorial valuation in favor of binary weight.
Reducedness then turns the negative rational valuation into the exact
two-adic valuation of the inverse-dyadic value's denominator.
Kummer's theorem identifies the binary-weight loss under arbitrary addition
with the two-adic valuation of one binomial coefficient.  This gives a
carry-twisted multiplication law for the Thue--Morse sign and, on the diagonal,
the central-binomial formula.
-/

set_option autoImplicit false

open scoped BigOperators Interval
open Finset

namespace Fabius

private lemma odd_num_mul_iff {q r : ℚ} (hq : Odd q.den) (hr : Odd r.den) :
    Odd (q * r).num ↔ Odd q.num ∧ Odd r.num := by
  have hprod := Rat.mul_num_den' q r
  have hq' : Odd (q.den : ℤ) := by exact_mod_cast hq
  have hr' : Odd (r.den : ℤ) := by exact_mod_cast hr
  have hqr' : Odd ((q * r).den : ℤ) := by
    exact_mod_cast rat_den_mul_odd hq hr
  have hparity :
      Odd ((q * r).num * q.den * r.den) ↔
        Odd (q.num * r.num * (q * r).den) := by
    rw [hprod]
  simpa only [Int.odd_mul, hq', hr', hqr', and_true] using hparity

private lemma odd_num_add_iff {q r : ℚ} (hq : Odd q.den) (hr : Odd r.den) :
    Odd (q + r).num ↔ (Odd q.num ↔ Even r.num) := by
  have hadd := Rat.add_num_den' q r
  have hq' : Odd (q.den : ℤ) := by exact_mod_cast hq
  have hr' : Odd (r.den : ℤ) := by exact_mod_cast hr
  have hnq' : ¬ Even (q.den : ℤ) := Int.not_even_iff_odd.mpr hq'
  have hsum' : Odd ((q + r).den : ℤ) := by
    exact_mod_cast rat_den_add_odd hq hr
  have hparity :
      Odd ((q + r).num * q.den * r.den) ↔
        Odd ((q.num * r.den + r.num * q.den) * (q + r).den) := by
    rw [hadd]
  simp only [Int.odd_mul, Int.odd_add, Int.even_mul, hq', hr', hnq', hsum',
    and_true, or_false] at hparity
  exact hparity

private lemma odd_den_sum_and_odd_num_iff_card {alpha : Type*}
    [DecidableEq alpha] (s : Finset alpha) (f : alpha → ℚ)
    (hden : ∀ x ∈ s, Odd (f x).den) :
    Odd (∑ x ∈ s, f x).den ∧
      (Odd (∑ x ∈ s, f x).num ↔
        Odd (s.filter (fun x => Odd (f x).num)).card) := by
  induction s using Finset.induction_on with
  | empty => norm_num
  | @insert a s ha ih =>
      have hfa : Odd (f a).den := hden a (mem_insert_self a s)
      have hrest : ∀ x ∈ s, Odd (f x).den := by
        intro x hx
        exact hden x (mem_insert_of_mem hx)
      have hi := ih hrest
      rw [sum_insert ha]
      constructor
      · exact rat_den_add_odd hfa hi.1
      · rw [odd_num_add_iff hfa hi.1]
        by_cases hodd : Odd (f a).num
        · have hanot : a ∉ s.filter (fun x => Odd (f x).num) :=
            fun h => ha (mem_of_mem_filter a h)
          simp only [hodd, true_iff, Finset.filter_insert, if_true,
            Finset.card_insert_of_notMem hanot]
          calc
            Even (∑ x ∈ s, f x).num ↔ ¬ Odd (∑ x ∈ s, f x).num :=
              Int.not_odd_iff_even.symm
            _ ↔ ¬ Odd (s.filter (fun x => Odd (f x).num)).card :=
              not_congr hi.2
            _ ↔ Even (s.filter (fun x => Odd (f x).num)).card :=
              Nat.not_odd_iff_even
            _ ↔ Odd ((s.filter (fun x => Odd (f x).num)).card + 1) := by
              constructor <;> rintro ⟨k, hk⟩ <;> exact ⟨k, by omega⟩
        · simp [Finset.filter_insert, hodd, hi.2]

private lemma odd_num_den_of_eq_divInt {q : ℚ} {a d : ℤ}
    (hq : q = Rat.divInt a d) (ha : Odd a) (hd : Odd d) :
    Odd q.num.natAbs ∧ Odd q.den := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    norm_num at hd
  obtain ⟨c, hnum, hden⟩ := Rat.num_den_mk hd0 hq
  have hdenProd : Odd (c * (q.den : ℤ)) := by rwa [← hden]
  have hnumProd : Odd (c * q.num) := by rwa [← hnum]
  have hqdenInt : Odd (q.den : ℤ) := (Int.odd_mul.mp hdenProd).2
  have hqnum : Odd q.num := (Int.odd_mul.mp hnumProd).2
  constructor
  · exact Int.natAbs_odd.mpr hqnum
  · exact_mod_cast hqdenInt

private lemma odd_num_den_of_eq_nat_div {q : ℚ} {a d : ℕ}
    (hq : q = (a : ℚ) / d) (ha : Odd a) (hd : Odd d) :
    Odd q.num.natAbs ∧ Odd q.den := by
  apply odd_num_den_of_eq_divInt (a := (a : ℤ)) (d := (d : ℤ))
  · simpa [Rat.divInt_eq_div] using hq
  · exact_mod_cast ha
  · exact_mod_cast hd

/-- Both the reduced numerator and denominator of every even moment are odd. -/
theorem moment_num_den_odd (n : ℕ) :
    Odd (moment n).num.natAbs ∧ Odd (moment n).den := by
  rw [moment_eq_momentNumerator_div]
  apply odd_num_den_of_eq_nat_div
  · rfl
  · exact momentNumerator_odd n
  · exact (odd_oddDoubleFactorial (n + 1)).mul
      (odd_evenMersenneProduct n)

private lemma nat_mul_odd_den_and_num_iff (a : ℕ) {q : ℚ}
    (hqden : Odd q.den) :
    Odd (((a : ℚ) * q).den) ∧
      (Odd (((a : ℚ) * q).num) ↔ Odd a ∧ Odd q.num) := by
  constructor
  · exact rat_den_mul_odd (by simp) hqden
  · simpa using odd_num_mul_iff (q := (a : ℚ)) (r := q) (by simp) hqden

private lemma two_mul_halfMoment_odd_index_num_den (n : ℕ) :
    Odd (2 * halfMoment (2 * n + 1)).num.natAbs ∧
      Odd (2 * halfMoment (2 * n + 1)).den := by
  have heq :
      2 * halfMoment (2 * n + 1) = ((2 * n + 1 : ℕ) : ℚ) * moment n := by
    rw [halfMoment_odd_eq_moment]
    ring
  rw [heq]
  have hm := moment_num_den_odd n
  have hmnum : Odd (moment n).num := Int.natAbs_odd.mp hm.1
  have hmul := nat_mul_odd_den_and_num_iff (2 * n + 1) hm.2
  constructor
  · apply Int.natAbs_odd.mpr
    exact hmul.2.2 ⟨odd_two_mul_add_one n, hmnum⟩
  · exact hmul.1

/-- All-index form of equation (31) of *Arithmetic of the Fabius function*:
the isolated half-moment recurrence after multiplying every term by two.
At `N = 0`, both sides are zero. -/
theorem two_mul_halfMoment_recurrence_all (N : ℕ) :
    ((((N + 1) * (2 ^ N - 1) : ℕ) : ℚ) * (2 * halfMoment N)) =
      ∑ k : Fin N,
        (Nat.choose (N + 1) k.val : ℚ) * (2 * halfMoment k.val) := by
  by_cases hN : N = 0
  · subst N
    norm_num
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le
    (Nat.one_le_iff_ne_zero.mpr hN)
  rw [show 1 + m = m + 1 by omega, halfMoment_succ]
  have hpow : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
  push_cast [Nat.cast_sub hpow]
  rw [show (∑ k : Fin (m + 1),
        (Nat.choose (m + 2) k.val : ℚ) * (2 * halfMoment k.val)) =
      2 * ∑ k : Fin (m + 1),
        (Nat.choose (m + 2) k.val : ℚ) * halfMoment k.val by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring]
  rw [show (m : ℚ) + 1 + 1 = (m : ℚ) + 2 by ring]
  let D : ℚ := ((m : ℚ) + 2) * ((2 : ℚ) ^ (m + 1) - 1)
  let S : ℚ := ∑ k : Fin (m + 1),
    (Nat.choose (m + 2) k.val : ℚ) * halfMoment k.val
  change D * (2 * (S / D)) = 2 * S
  have hD : D ≠ 0 := by
    dsimp [D]
    apply mul_ne_zero
    · positivity
    · exact sub_ne_zero.mpr (ne_of_gt (one_lt_pow₀ (by norm_num) (by omega)))
  field_simp [hD]

/-- Positive-index form of equation (31), retained with its original
signature for source compatibility. -/
theorem two_mul_halfMoment_recurrence (N : ℕ) (hN : 1 ≤ N) :
    ((((N + 1) * (2 ^ N - 1) : ℕ) : ℚ) * (2 * halfMoment N)) =
      ∑ k : Fin N,
        (Nat.choose (N + 1) k.val : ℚ) * (2 * halfMoment k.val) := by
  have _hN0 : N ≠ 0 := Nat.one_le_iff_ne_zero.mp hN
  exact two_mul_halfMoment_recurrence_all N

private lemma odd_inner_binomial_count (m : ℕ) (hm : 1 ≤ m) :
    Odd (((range (2 * m)).filter (fun k =>
      k ≠ 0 ∧ Odd (Nat.choose (2 * m + 1) k))).card) := by
  rw [card_odd_inner_binomial_coefficients m hm]
  have hpowEven : Even (2 ^ (binaryWeight m + 1)) := by
    rw [pow_succ]
    exact even_two.mul_left _
  have hcardPos : 0 < ((range (2 * m)).filter (fun k =>
      k ≠ 0 ∧ Odd (Nat.choose (2 * m + 1) k))).card := by
    apply Finset.card_pos.mpr
    refine ⟨1, ?_⟩
    simp only [mem_filter, mem_range, Nat.choose_one_right]
    exact ⟨by omega, by norm_num, odd_two_mul_add_one m⟩
  rw [card_odd_inner_binomial_coefficients m hm] at hcardPos
  exact Nat.Even.sub_odd (by omega) hpowEven (by decide)

/-- For a positive index, both reduced numerator and denominator of
`2 * halfMoment n` are odd. -/
theorem two_mul_halfMoment_num_den_odd (n : ℕ) (hn : 0 < n) :
    Odd (2 * halfMoment n).num.natAbs ∧ Odd (2 * halfMoment n).den := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · have hm : 1 ≤ m := by omega
      let term : Fin (2 * m) → ℚ := fun k =>
        (Nat.choose (2 * m + 1) k.val : ℚ) * (2 * halfMoment k.val)
      let S : ℚ := ∑ k : Fin (2 * m), term k
      have htermDen (k : Fin (2 * m)) : Odd (term k).den := by
        by_cases hk0 : k.val = 0
        · norm_num [term, hk0, halfMoment]
        · have hk := ih k.val k.isLt (Nat.pos_of_ne_zero hk0)
          exact (nat_mul_odd_den_and_num_iff
            (Nat.choose (2 * m + 1) k.val) hk.2).1
      have htermNum (k : Fin (2 * m)) :
          Odd (term k).num ↔
            k.val ≠ 0 ∧ Odd (Nat.choose (2 * m + 1) k.val) := by
        by_cases hk0 : k.val = 0
        · norm_num [term, hk0, halfMoment]
        · have hk := ih k.val k.isLt (Nat.pos_of_ne_zero hk0)
          have hknum : Odd (2 * halfMoment k.val).num := Int.natAbs_odd.mp hk.1
          have hmul := (nat_mul_odd_den_and_num_iff
            (Nat.choose (2 * m + 1) k.val) hk.2).2
          simpa [term, hk0, hknum] using hmul
      have hsum := odd_den_sum_and_odd_num_iff_card
        (Finset.univ : Finset (Fin (2 * m))) term (by
          intro k hk
          exact htermDen k)
      simp_rw [htermNum] at hsum
      have hcount :
          Odd (((Finset.univ : Finset (Fin (2 * m))).filter (fun k =>
            k.val ≠ 0 ∧ Odd (Nat.choose (2 * m + 1) k.val))).card) := by
        let p : ℕ → Prop := fun k =>
          k ≠ 0 ∧ Odd (Nat.choose (2 * m + 1) k)
        have hcard := card_filter_fin_eq_range (2 * m) p
        have hrange : Odd (((range (2 * m)).filter p).card) := by
          simpa only [p] using odd_inner_binomial_count m hm
        exact hcard.symm ▸ hrange
      have hSden : Odd S.den := hsum.1
      have hSnum : Odd S.num.natAbs := by
        exact Int.natAbs_odd.mpr (hsum.2.mpr hcount)
      let A : ℕ := (2 * m + 1) * (2 ^ (2 * m) - 1)
      have hAodd : Odd A := by
        exact (odd_two_mul_add_one m).mul
          (two_pow_sub_one_odd (by omega))
      have hA0 : A ≠ 0 := Nat.ne_of_gt hAodd.pos
      have hrec := two_mul_halfMoment_recurrence_all (2 * m)
      change (A : ℚ) * (2 * halfMoment (2 * m)) = S at hrec
      have hquot : 2 * halfMoment (2 * m) = S / (A : ℚ) := by
        apply (eq_div_iff (by exact_mod_cast hA0)).2
        simpa [mul_comm] using hrec
      have hrepr :
          2 * halfMoment (2 * m) =
            Rat.divInt S.num ((S.den * A : ℕ) : ℤ) := by
        calc
          2 * halfMoment (2 * m) = S / (A : ℚ) := hquot
          _ = Rat.divInt S.num ((S.den * A : ℕ) : ℤ) := by
            nth_rw 1 [← Rat.num_div_den S]
            simp only [Rat.divInt_eq_div]
            push_cast
            field_simp [hA0, S.den_ne_zero]
      apply odd_num_den_of_eq_divInt (d := ((S.den * A : ℕ) : ℤ))
      · exact hrepr
      · exact Int.natAbs_odd.mp hSnum
      · exact_mod_cast hSden.mul hAodd
    · exact two_mul_halfMoment_odd_index_num_den m

private lemma padicValRat_two_eq_zero_of_odd_num_den {q : ℚ}
    (hnum : Odd q.num.natAbs) (hden : Odd q.den) :
    padicValRat 2 q = 0 := by
  rw [padicValRat_def]
  unfold padicValInt
  rw [padicValNat.eq_zero_of_not_dvd hnum.not_two_dvd_nat,
    padicValNat.eq_zero_of_not_dvd hden.not_two_dvd_nat]
  norm_num

/-- Every even moment is a two-adic unit. -/
theorem moment_padicVal_two (n : ℕ) : padicValRat 2 (moment n) = 0 := by
  have hodd := moment_num_den_odd n
  exact padicValRat_two_eq_zero_of_odd_num_den hodd.1 hodd.2

/-- Theorem 20's exact-arithmetic content: `2 * halfMoment n` is a two-adic
unit, witnessed by its odd reduced numerator and denominator. -/
theorem two_mul_halfMoment_padicVal_two_and_odd (n : ℕ) (hn : 1 ≤ n) :
    padicValRat 2 (2 * halfMoment n) = 0 ∧
      Odd (2 * halfMoment n).num.natAbs ∧
      Odd (2 * halfMoment n).den := by
  have hodd := two_mul_halfMoment_num_den_odd n (by omega)
  exact ⟨padicValRat_two_eq_zero_of_odd_num_den hodd.1 hodd.2, hodd⟩

/-- The reduced numerator of `2 * halfMoment n` is odd exactly at the
positive indices.  This packages the exceptional value at `n = 0` into a
parameter-free characterization. -/
theorem two_mul_halfMoment_num_odd_iff_pos (n : ℕ) :
    Odd (2 * halfMoment n).num.natAbs ↔ 0 < n := by
  constructor
  · intro hodd
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    norm_num [halfMoment] at hodd
    exact (Nat.not_odd_iff_even.mpr even_two) hodd
  · intro hn
    exact (two_mul_halfMoment_num_den_odd n hn).1

/-- Every positive-index half moment has two-adic valuation `-1`. -/
theorem halfMoment_padicVal_two (n : ℕ) (hn : 0 < n) :
    padicValRat 2 (halfMoment n) = -1 := by
  have htwenty := two_mul_halfMoment_padicVal_two_and_odd n (by omega)
  have hhalfMomentNe : halfMoment n ≠ 0 := ne_of_gt (halfMoment_pos n)
  have hvalTwo : padicValRat 2 (2 : ℚ) = 1 := by
    simpa using padicValRat.self (p := 2) (by omega)
  have hmul := padicValRat.mul (p := 2) (q := (2 : ℚ))
    (r := halfMoment n) (by norm_num) hhalfMomentNe
  rw [hvalTwo, htwenty.1] at hmul
  omega

/-- Parameter-free two-adic valuation of the half-moment sequence, including
the exceptional zeroth value. -/
theorem halfMoment_padicVal_two_eq_ite (n : ℕ) :
    padicValRat 2 (halfMoment n) = if n = 0 then 0 else -1 := by
  by_cases hn : n = 0
  · subst n
    norm_num [halfMoment]
  · rw [if_neg hn]
    exact halfMoment_padicVal_two n (Nat.pos_of_ne_zero hn)

/-- Multiplication preserves oddness of both reduced numerators and
denominators. -/
theorem odd_num_den_mul {q r : ℚ}
    (hq : Odd q.num.natAbs ∧ Odd q.den)
    (hr : Odd r.num.natAbs ∧ Odd r.den) :
    Odd (q * r).num.natAbs ∧ Odd (q * r).den := by
  constructor
  · apply Int.natAbs_odd.mpr
    exact (odd_num_mul_iff hq.2 hr.2).2
      ⟨Int.natAbs_odd.mp hq.1, Int.natAbs_odd.mp hr.1⟩
  · exact rat_den_mul_odd hq.2 hr.2

/-- Multiplication by an odd natural preserves oddness of the reduced
numerator and denominator of a rational. -/
theorem odd_num_den_mul_nat {q : ℚ} (a : ℕ)
    (hq : Odd q.num.natAbs ∧ Odd q.den) (ha : Odd a) :
    Odd (q * (a : ℚ)).num.natAbs ∧ Odd (q * (a : ℚ)).den := by
  rw [mul_comm]
  have hmul := nat_mul_odd_den_and_num_iff a hq.2
  constructor
  · apply Int.natAbs_odd.mpr
    exact hmul.2.2 ⟨ha, Int.natAbs_odd.mp hq.1⟩
  · exact hmul.1

/-- A natural rational with odd reduced numerator is an odd natural. -/
theorem isOddNatural_of_isNatural_of_odd_num {q : ℚ}
    (hnat : IsNatural q) (hodd : Odd q.num.natAbs) : IsOddNatural q := by
  rcases hnat with ⟨m, rfl⟩
  refine ⟨m, ?_, rfl⟩
  simpa using hodd

/-- An odd divisor of a power of two is one. -/
theorem odd_eq_one_of_dvd_two_pow {d e : ℕ} (hd : Odd d)
    (hdvd : d ∣ 2 ^ e) : d = 1 := by
  obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hk0 : k = 0 := by
    by_contra hk0
    have heven : Even (2 ^ k) := Nat.even_pow.mpr ⟨even_two, hk0⟩
    exact (Nat.not_even_iff_odd.mpr hd) heven
  simp [hk0]

/-- A nonnegative rational with reduced denominator one is natural. -/
theorem isNatural_of_den_eq_one_of_nonneg {q : ℚ} (hden : q.den = 1)
    (hq : 0 ≤ q) : IsNatural q := by
  refine ⟨q.num.natAbs, ?_⟩
  have hnum : 0 ≤ q.num := Rat.num_nonneg.mpr hq
  calc
    q = (q.num : ℚ) := (Rat.coe_int_num_of_den_eq_one hden).symm
    _ = (q.num.natAbs : ℕ) := by
      calc
        (q.num : ℚ) = ((q.num.natAbs : ℤ) : ℚ) :=
          congrArg (fun z : ℤ => (z : ℚ)) (Int.natAbs_of_nonneg hnum).symm
        _ = (q.num.natAbs : ℕ) := by norm_num

/-- Legendre's formula at `p = 2`: the valuation of `n!` is `n` minus the
binary digit sum of `n`. -/
theorem factorial_padicVal_two (n : ℕ) :
    padicValRat 2 (n.factorial : ℚ) =
      ((n - binaryWeight n : ℕ) : ℤ) := by
  rw [padicValRat.of_nat]
  have h := sub_one_mul_padicValNat_factorial (p := 2) n
  simpa [binaryWeight] using congrArg (fun k : ℕ => (k : ℤ)) h

/-- Kummer's digit-sum formula at two for an arbitrary binomial coefficient. -/
theorem addChoose_padicValNat_two (a b : ℕ) :
    padicValNat 2 (Nat.choose (a + b) a) =
      binaryWeight a + binaryWeight b - binaryWeight (a + b) := by
  rw [add_comm a b]
  simpa [binaryWeight] using
    (sub_one_mul_padicValNat_choose_eq_sub_sum_digits'
      (p := 2) (n := b) (k := a))

/-- **Additive form of Kummer's theorem at two.**  The binary weight lost
in an addition is exactly the two-adic valuation of the binomial
coefficient that counts its carries:
`w(a + b) + ν₂((a+b).choose a) = w(a) + w(b)`.

This is the truncation-free companion of `addChoose_padicValNat_two`:
stated as an equation between natural numbers with no subtraction, so that
every rearrangement -- in particular the subadditivity
`w(a + b) ≤ w(a) + w(b)` -- is available to `omega`.  Proved from Legendre's
formula applied to the three factorials of
`(a+b).choose a * a! * b! = (a+b)!`. -/
theorem binaryWeight_add_addChoose_padicValNat_two (a b : ℕ) :
    binaryWeight (a + b) +
        padicValNat 2 (Nat.choose (a + b) a) =
      binaryWeight a + binaryWeight b := by
  have hweight_le (n : ℕ) : binaryWeight n ≤ n := by
    simpa [binaryWeight] using Nat.digit_sum_le 2 n
  have hchoose : Nat.choose (a + b) a ≠ 0 :=
    Nat.choose_ne_zero (Nat.le_add_right a b)
  have hfactorialIdentity :
      Nat.choose (a + b) a * a.factorial * b.factorial =
        (a + b).factorial := by
    rw [Nat.choose_symm_add (a := a) (b := b)]
    exact Nat.add_choose_mul_factorial_mul_factorial a b
  have h := congrArg (padicValNat 2) hfactorialIdentity
  rw [padicValNat.mul
        (mul_ne_zero hchoose (Nat.factorial_ne_zero a))
        (Nat.factorial_ne_zero b),
      padicValNat.mul hchoose (Nat.factorial_ne_zero a)] at h
  change padicValNat 2 (Nat.choose (a + b) a) +
          padicValNat 2 a.factorial + padicValNat 2 b.factorial =
        padicValNat 2 (a + b).factorial at h
  have hfactorialNat (n : ℕ) :
      padicValNat 2 n.factorial = n - binaryWeight n := by
    have hn := sub_one_mul_padicValNat_factorial (p := 2) n
    simpa [binaryWeight] using hn
  rw [hfactorialNat a, hfactorialNat b, hfactorialNat (a + b)] at h
  have ha := hweight_le a
  have hb := hweight_le b
  have hab := hweight_le (a + b)
  omega

/-- Ordinary addition is Thue--Morse multiplicative up to the two-adic carry
valuation of its binomial coefficient. -/
theorem thueMorseSign_add_valuation (a b : ℕ) :
    thueMorseSign (a + b) =
      thueMorseSign a * thueMorseSign b *
        (-1 : ℤ) ^ padicValNat 2 (Nat.choose (a + b) a) := by
  let v : ℕ := padicValNat 2 (Nat.choose (a + b) a)
  change thueMorseSign (a + b) =
    thueMorseSign a * thueMorseSign b * (-1 : ℤ) ^ v
  have hbalance :
      binaryWeight (a + b) + v = binaryWeight a + binaryWeight b := by
    simpa only [v] using binaryWeight_add_addChoose_padicValNat_two a b
  simp only [thueMorseSign]
  calc
    (-1 : ℤ) ^ binaryWeight (a + b) =
        (-1 : ℤ) ^ binaryWeight (a + b) * (-1 : ℤ) ^ (v + v) := by
      rw [(Even.add_self v).neg_one_pow, mul_one]
    _ = (-1 : ℤ) ^ ((binaryWeight (a + b) + v) + v) := by
      rw [← pow_add, ← add_assoc]
    _ = (-1 : ℤ) ^ ((binaryWeight a + binaryWeight b) + v) := by
      rw [hbalance]
    _ = (-1 : ℤ) ^ binaryWeight a * (-1 : ℤ) ^ binaryWeight b *
          (-1 : ℤ) ^ v := by
      rw [pow_add, pow_add]

/-- Kummer's theorem at `p = 2`: the two-adic valuation of the central
binomial coefficient is the binary weight. -/
theorem centralChoose_padicValNat_two (n : ℕ) :
    padicValNat 2 (Nat.choose (2 * n) n) = binaryWeight n := by
  have hKummer :=
    sub_one_mul_padicValNat_choose_eq_sub_sum_digits'
      (p := 2) (n := n) (k := n)
  have hdouble :
      (Nat.digits 2 (2 * n)).sum = (Nat.digits 2 n).sum := by
    by_cases hn : n = 0
    · simp [hn]
    · rw [Nat.digits_base_mul Nat.one_lt_two (Nat.pos_of_ne_zero hn)]
      simp
  calc
    padicValNat 2 (Nat.choose (2 * n) n) =
        (Nat.digits 2 n).sum + (Nat.digits 2 n).sum -
          (Nat.digits 2 (2 * n)).sum := by
      simpa [two_mul] using hKummer
    _ = binaryWeight n := by
      rw [hdouble]
      simp [binaryWeight]

/-- A single central binomial coefficient recovers the Thue--Morse sign. -/
theorem thueMorseSign_centralChoose (n : ℕ) :
    thueMorseSign n =
      (-1 : ℤ) ^ padicValNat 2 (Nat.choose (2 * n) n) := by
  rw [centralChoose_padicValNat_two, thueMorseSign]

/-- The two-adic valuation of the Fabius value at `2⁻ⁿ`, i.e. the
valuation equality in Theorem 21. -/
theorem fabiusAtInverseTwoPow_padicVal_two (n : ℕ) (hn : 1 ≤ n) :
    padicValRat 2 (fabiusAtInverseTwoPow n) =
      -(n.choose 2 : ℤ) - 1 - padicValRat 2 (n.factorial : ℚ) := by
  have hhalfMomentNe : halfMoment n ≠ 0 := ne_of_gt (halfMoment_pos n)
  have hvalTwo : padicValRat 2 (2 : ℚ) = 1 := by
    simpa using padicValRat.self (p := 2) (by omega)
  have hhalfMomentVal := halfMoment_padicVal_two n (by omega)
  have hfactorialNe : (n.factorial : ℚ) ≠ 0 := by positivity
  have hpowNe : (2 : ℚ) ^ n.choose 2 ≠ 0 := by positivity
  rw [fabiusAtInverseTwoPow_eq_halfMoment, halfMomentFabiusValue,
    padicValRat.div hhalfMomentNe (mul_ne_zero hfactorialNe hpowNe),
    padicValRat.mul hfactorialNe hpowNe, padicValRat.pow,
    hvalTwo, hhalfMomentVal]
  ring

/-- The exact two-adic valuation of the reduced denominator of the
inverse-dyadic Fabius value. -/
theorem fabiusAtInverseTwoPow_den_padicVal_two (n : ℕ) (hn : 1 ≤ n) :
    padicValNat 2 (fabiusAtInverseTwoPow n).den =
      n.choose 2 + 1 + padicValNat 2 n.factorial := by
  have hval := fabiusAtInverseTwoPow_padicVal_two n hn
  rw [padicValRat.of_nat] at hval
  have hnumNot : ¬ 2 ∣ (fabiusAtInverseTwoPow n).num.natAbs := by
    intro hnumDvd
    have hcop : Nat.Coprime 2 (fabiusAtInverseTwoPow n).den :=
      (fabiusAtInverseTwoPow n).reduced.of_dvd_left hnumDvd
    have hdenNot : ¬ 2 ∣ (fabiusAtInverseTwoPow n).den :=
      Nat.prime_two.coprime_iff_not_dvd.mp hcop
    rw [padicValRat_def,
      padicValNat.eq_zero_of_not_dvd hdenNot] at hval
    omega
  rw [padicValRat_def] at hval
  unfold padicValInt at hval
  rw [padicValNat.eq_zero_of_not_dvd hnumNot] at hval
  omega

/-- Closed binary-weight form of the valuation at `2⁻ⁿ`, with the factorial
valuation eliminated by Legendre's formula. -/
theorem fabiusAtInverseTwoPow_padicVal_two_closed (n : ℕ) (hn : 1 ≤ n) :
    padicValRat 2 (fabiusAtInverseTwoPow n) =
      -(n.choose 2 : ℤ) - 1 - ((n - binaryWeight n : ℕ) : ℤ) := by
  rw [fabiusAtInverseTwoPow_padicVal_two n hn, factorial_padicVal_two]

end Fabius
```

### `DyadicAppellBridge.lean`

```lean
import SourceAppell
import UpstreamTwoAdic

namespace FabiusProofLane
open Finset

lemma centeredMomentSeries_eq_half_rescale :
    Fabius.centeredMomentPowerSeries = PowerSeries.rescale (1/2 : ℚ) momentSeries := by
  ext n
  obtain ⟨r,hr|hr⟩ := Nat.even_or_odd' n
  · subst n
    rw [Fabius.coeff_centeredMomentPowerSeries_even,PowerSeries.coeff_rescale,momentSeries_even]
    have hp : (1/2 : ℚ)^(2*r)=1/(4 : ℚ)^r := by
      rw [pow_mul]
      norm_num [div_pow]
    rw [hp]
    unfold sourceCoefficient
    ring
  · subst n
    rw [Fabius.coeff_centeredMomentPowerSeries_odd,PowerSeries.coeff_rescale,momentSeries_odd,mul_zero]

lemma appellSeries_half_rescale (x : ℚ) :
    PowerSeries.rescale (1/2 : ℚ) (appellSeries x) =
      PowerSeries.rescale (x/2) (PowerSeries.exp ℚ)*Fabius.centeredMomentPowerSeries := by
  rw [appellSeries,map_mul,← centeredMomentSeries_eq_half_rescale,PowerSeries.rescale_rescale]
  have hx : x*(1/2 : ℚ)=x/2 := by ring
  rw [hx,mul_comm]

lemma sourceAppellPolynomial_formula (n : ℕ) (x : ℚ) :
    (sourceAppellPolynomial n).eval x =
      (∑ k ∈ range (n/2+1), (Nat.choose n (2*k) : ℚ)*x^(n-2*k)*Fabius.moment k) /
        (n.factorial : ℚ) := by
  have h := congrArg (PowerSeries.coeff n) (appellSeries_half_rescale x)
  rw [PowerSeries.coeff_rescale,← sourceAppellPolynomial_eval,
    Fabius.coeff_exp_mul_centeredMomentPowerSeries] at h
  rw [show (2 : ℚ)*(x/2)=x by ring] at h
  have hpow : (1/2 : ℚ)^n=1/(2 : ℚ)^n := by simp [div_pow]
  rw [hpow] at h
  have hp : (2 : ℚ)^n ≠ 0 := by positivity
  have hf : (n.factorial : ℚ) ≠ 0 := by positivity
  field_simp at h ⊢
  exact h

lemma sourceAppellPolynomial_halfMoment (n : ℕ) :
    (sourceAppellPolynomial n).eval 1/(2 : ℚ)^n = Fabius.halfMoment n/(n.factorial : ℚ) := by
  have h := congrArg (PowerSeries.coeff n) (appellSeries_half_rescale 1)
  rw [PowerSeries.coeff_rescale,← sourceAppellPolynomial_eval,
    Fabius.coeff_expHalf_mul_centeredMomentPowerSeries_eq_halfMoment] at h
  have hp : (1/2 : ℚ)^n=((2 : ℚ)^n)⁻¹ := by simp only [one_div,inv_pow]
  rw [hp] at h
  simpa only [div_eq_mul_inv,mul_comm] using h

lemma fabiusDyadic_appell (n a : ℕ) :
    (2 : ℚ)^n.choose 2*Fabius.fabiusDyadic n a =
      (∑ h ∈ range a, (Fabius.thueMorseSign h : ℚ)*
        (sourceAppellPolynomial n).eval ((2 : ℚ)*a-2*h-1))/(2 : ℚ)^n := by
  have hinner (h : ℕ) :
      (∑ k : Fin (n/2+1), (Nat.choose n (2*k.val) : ℚ)*
        ((2 : ℚ)*a-2*h-1)^(n-2*k.val)*Fabius.moment k.val) =
      (n.factorial : ℚ)*(sourceAppellPolynomial n).eval ((2 : ℚ)*a-2*h-1) := by
    rw [Fin.sum_univ_eq_sum_range (fun k => (Nat.choose n (2*k) : ℚ)*
      ((2 : ℚ)*a-2*h-1)^(n-2*k)*Fabius.moment k) (n/2+1)]
    rw [sourceAppellPolynomial_formula,mul_div_cancel₀ _ (by positivity)]
  rw [Fabius.fabiusDyadic]
  simp_rw [hinner]
  rw [Fin.sum_univ_eq_sum_range (fun h => (Fabius.thueMorseSign h : ℚ)*
    ((n.factorial : ℚ)*(sourceAppellPolynomial n).eval ((2 : ℚ)*a-2*h-1))) a]
  have hsum : (∑ h ∈ range a, (Fabius.thueMorseSign h : ℚ)*
      ((n.factorial : ℚ)*(sourceAppellPolynomial n).eval ((2 : ℚ)*a-2*h-1))) =
      (n.factorial : ℚ)*∑ h ∈ range a, (Fabius.thueMorseSign h : ℚ)*
        (sourceAppellPolynomial n).eval ((2 : ℚ)*a-2*h-1) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro h hh
    ring
  rw [hsum,zpow_neg,zpow_natCast,Fabius.choose_succ_two,pow_add]
  have hf : (n.factorial : ℚ) ≠ 0 := by positivity
  have hp : (2 : ℚ)^n.choose 2 ≠ 0 := by positivity
  have hpn : (2 : ℚ)^n ≠ 0 := by positivity
  field_simp

#print axioms fabiusDyadic_appell
end FabiusProofLane
```

### `ThueMorseConvolution.lean`

```lean
import DyadicAppellBridge

namespace FabiusProofLane
open Finset

lemma sum_even_odd (F : ℕ → ℚ) (b : ℕ) :
    (∑ i ∈ range (2*b), F i) = ∑ j ∈ range b, (F (2*j)+F (2*j+1)) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [show 2*(b+1)=2*b+1+1 by omega,sum_range_succ,sum_range_succ,ih,sum_range_succ]
    ring

lemma binaryWeight_even (n : ℕ) : Fabius.binaryWeight (2*n)=Fabius.binaryWeight n := by
  by_cases hn : n=0
  · simp [hn]
  unfold Fabius.binaryWeight
  rw [← zero_add (2*n),Nat.digits_add 2 (by decide) 0 n (by decide) (Or.inr hn)]
  simp

lemma binaryWeight_odd (n : ℕ) : Fabius.binaryWeight (2*n+1)=Fabius.binaryWeight n+1 := by
  unfold Fabius.binaryWeight
  rw [Nat.add_comm (2*n) 1,Nat.digits_add 2 (by decide) 1 n (by decide) (Or.inl (by decide))]
  simp [add_comm]

lemma thueMorseSign_even (n : ℕ) : Fabius.thueMorseSign (2*n)=Fabius.thueMorseSign n := by
  simp [Fabius.thueMorseSign,binaryWeight_even]
lemma thueMorseSign_odd (n : ℕ) : Fabius.thueMorseSign (2*n+1) = -Fabius.thueMorseSign n := by
  simp [Fabius.thueMorseSign,binaryWeight_odd,pow_succ]

noncomputable def dyadicNormalized (n b : ℕ) : ℚ :=
  (2 : ℚ)^n.choose 2*Fabius.fabiusDyadic n (2*b+1)
noncomputable def dyadicCore (n b : ℕ) : ℚ :=
  if b=0 then Fabius.halfMoment n/(n.factorial : ℚ)
  else (sourceAppellPolynomial (n-1)).eval ((2*b : ℕ) : ℚ)

lemma dyadicNormalized_pair_sum (n b : ℕ) :
    dyadicNormalized (n+1) b =
      (∑ j ∈ range b, (Fabius.thueMorseSign j : ℚ)*
        (sourceAppellPolynomial n).eval ((2 : ℚ)*(b-j))) +
      (Fabius.thueMorseSign b : ℚ)*(Fabius.halfMoment (n+1)/((n+1).factorial : ℚ)) := by
  rw [dyadicNormalized,fabiusDyadic_appell,sum_range_succ,sum_even_odd]
  have hlast : ((2 : ℚ)*((2*b+1 : ℕ) : ℚ)-2*((2*b : ℕ) : ℚ)-1)=1 := by push_cast; ring
  simp only [thueMorseSign_even,thueMorseSign_odd,Int.cast_neg]
  rw [hlast]
  have hpair (j : ℕ) (hj : j ∈ range b) :
      (Fabius.thueMorseSign j : ℚ)*(sourceAppellPolynomial (n+1)).eval
        ((2 : ℚ)*((2*b+1 : ℕ) : ℚ)-2*((2*j : ℕ) : ℚ)-1)+
      (-(Fabius.thueMorseSign j : ℚ))*(sourceAppellPolynomial (n+1)).eval
        ((2 : ℚ)*((2*b+1 : ℕ) : ℚ)-2*((2*j+1 : ℕ) : ℚ)-1) =
      (2 : ℚ)^(n+1)*((Fabius.thueMorseSign j : ℚ)*
        (sourceAppellPolynomial n).eval ((2 : ℚ)*(b-j))) := by
    have hjb : j ≤ b := le_of_lt (mem_range.mp hj)
    have hsub : ((b-j : ℕ) : ℚ)=(b : ℚ)-j := Nat.cast_sub hjb
    have hrec := sourceAppellPolynomial_difference n ((4 : ℚ)*((b : ℚ)-j))
    have hp : ((2 : ℚ)*((2*b+1 : ℕ) : ℚ)-2*((2*j : ℕ) : ℚ)-1)=(4 : ℚ)*((b : ℚ)-j)+1 := by push_cast; ring
    have hm : ((2 : ℚ)*((2*b+1 : ℕ) : ℚ)-2*((2*j+1 : ℕ) : ℚ)-1)=(4 : ℚ)*((b : ℚ)-j)-1 := by push_cast; ring
    rw [hp,hm]
    have he : ((4 : ℚ)*((b : ℚ)-j))/2=(2 : ℚ)*((b : ℚ)-j) := by ring
    rw [he] at hrec
    linear_combination (Fabius.thueMorseSign j : ℚ)*hrec
  rw [Finset.sum_congr rfl hpair,← mul_sum]
  rw [add_div]
  rw [show (Fabius.thueMorseSign b : ℚ)*(sourceAppellPolynomial (n+1)).eval 1/(2 : ℚ)^(n+1) =
    (Fabius.thueMorseSign b : ℚ)*((sourceAppellPolynomial (n+1)).eval 1/(2 : ℚ)^(n+1)) by ring,
    sourceAppellPolynomial_halfMoment]
  have hp : (2 : ℚ)^(n+1) ≠ 0 := by positivity
  field_simp


lemma dyadicNormalized_convolution (n b : ℕ) :
    dyadicNormalized (n+1) b =
      ∑ j ∈ range (b+1), (Fabius.thueMorseSign j : ℚ)*dyadicCore (n+1) (b-j) := by
  rw [dyadicNormalized_pair_sum,sum_range_succ]
  simp only [Nat.sub_self,dyadicCore,ite_true,Nat.add_sub_cancel]
  congr 1
  apply sum_congr rfl
  intro j hj
  have hjb : j < b := mem_range.mp hj
  rw [if_neg (by omega : b-j ≠ 0)]
  have harg : ((2*(b-j) : ℕ) : ℚ)=(2 : ℚ)*((b : ℚ)-j) := by
    rw [Nat.cast_mul,Nat.cast_sub (by omega),Nat.cast_ofNat]
  rw [harg]

#print axioms dyadicNormalized_convolution
end FabiusProofLane

```

### `TriangularDenominators.lean`

```lean
import FiniteSampling

namespace FabiusProofLane
open Finset

/-- An integral triangular convolution with diagonal one preserves every
local common-denominator condition, for an arbitrary rational scale. -/
theorem triangular_prefix_integrality {p : ℕ} [hp : Fact p.Prime]
    (u : ℚ) (sigma : ℕ → ℤ) (V r : ℕ → ℚ)
    (hrec : ∀ b, V b=r b+∑ i ∈ range b, (sigma (i+1) : ℚ)*r (b-(i+1)))
    (L : ℕ) :
    (∀ b, b < L → IntegralAt p (u*V b)) ↔
      ∀ b, b < L → IntegralAt p (u*r b) := by
  have hscaled (b : ℕ) : u*V b=u*r b+
      ∑ i ∈ range b, (sigma (i+1) : ℚ)*(u*r (b-(i+1))) := by
    rw [hrec,mul_add,mul_sum]
    congr 1
    apply sum_congr rfl
    intro i hi
    ring
  constructor
  · intro hV b
    induction b using Nat.strong_induction_on with
    | h b ih =>
      intro hb
      have hsum : IntegralAt p (∑ i ∈ range b, (sigma (i+1) : ℚ)*(u*r (b-(i+1)))) := by
        apply integralAt_sum
        intro i hi
        have hi' := mem_range.mp hi
        exact integralAt_mul (integralAt_int p _) (ih _ (by omega) (by omega))
      have hh := integralAt_sub (hV b hb) hsum
      rw [hscaled] at hh
      have heq : u*r b+∑ i ∈ range b, (sigma (i+1) : ℚ)*(u*r (b-(i+1))) -
          (∑ i ∈ range b, (sigma (i+1) : ℚ)*(u*r (b-(i+1))))=u*r b := by ring
      simpa only [heq] using hh
  · intro hr b hb
    rw [hscaled]
    apply integralAt_add (hr b hb)
    apply integralAt_sum
    intro i hi
    have hi' := mem_range.mp hi
    exact integralAt_mul (integralAt_int p _) (hr _ (by omega))

lemma convolution_to_triangular (sigma : ℕ → ℤ) (hs0 : sigma 0=1)
    (V r : ℕ → ℚ)
    (hrec : ∀ b, V b=∑ j ∈ range (b+1), (sigma j : ℚ)*r (b-j)) (b : ℕ) :
    V b=r b+∑ i ∈ range b, (sigma (i+1) : ℚ)*r (b-(i+1)) := by
  rw [hrec,sum_range_succ']
  simp only [hs0,Int.cast_one,one_mul,Nat.sub_zero]
  ring

#print axioms triangular_prefix_integrality
end FabiusProofLane
```

### `DyadicLocalCharacterization.lean`

```lean
import ThueMorseConvolution
import TriangularDenominators

namespace FabiusProofLane
open Finset Polynomial

lemma dyadic_prefix_core_iff {p : ℕ} [hp : Fact p.Prime]
    (u : ℚ) (n L : ℕ) :
    (∀ b, b < L → IntegralAt p (u*dyadicNormalized (n+1) b)) ↔
      ∀ b, b < L → IntegralAt p (u*dyadicCore (n+1) b) := by
  have hs0 : Fabius.thueMorseSign 0=1 := by simp [Fabius.thueMorseSign,Fabius.binaryWeight]
  have hrec := convolution_to_triangular Fabius.thueMorseSign hs0
    (dyadicNormalized (n+1)) (dyadicCore (n+1)) (dyadicNormalized_convolution n)
  exact triangular_prefix_integrality u Fabius.thueMorseSign
    (dyadicNormalized (n+1)) (dyadicCore (n+1)) hrec L

lemma halfMoment_local_iff {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (u : ℚ) (n : ℕ) :
    IntegralAt p (u*(Fabius.halfMoment n/(n.factorial : ℚ))) ↔
      IntegralAt p (u*(sourceAppellPolynomial n).eval 1) := by
  rw [← sourceAppellPolynomial_halfMoment]
  have heq : (2 : ℚ)^n*(u*((sourceAppellPolynomial n).eval 1/(2 : ℚ)^n)) =
      u*(sourceAppellPolynomial n).eval 1 := by
    have hp0 : (2 : ℚ)^n ≠ 0 := by positivity
    field_simp
  rw [← heq]
  exact (integralAt_two_pow_iff hp2 n _).symm

lemma dyadic_core_local_iff {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (u : ℚ) (n L : ℕ) (hL : n+2 ≤ L) :
    (∀ b, b < L → IntegralAt p (u*dyadicCore (n+1) b)) ↔
      ClearsLocal p u (sourceAppellPolynomial (n+1)) := by
  constructor
  · intro hcore
    have hbase : IntegralAt p (u*(sourceAppellPolynomial (n+1)).eval 1) := by
      apply (halfMoment_local_iff hp2 u (n+1)).mp
      simpa only [dyadicCore,ite_true] using hcore 0 (by omega)
    let P : ℚ[X] := C u*(sourceAppellPolynomial n).comp (C 2*X)
    have hdeg : P.natDegree ≤ n := by
      have hcomp : ((sourceAppellPolynomial n).comp (C 2*X)).natDegree ≤ n := by
        have hh : ((sourceAppellPolynomial n).comp (C (2 : ℚ)*X)).natDegree ≤
            (sourceAppellPolynomial n).natDegree*(C (2 : ℚ)*X).natDegree := Polynomial.natDegree_comp_le
        have harg : (C (2 : ℚ)*X).natDegree=1 := by simp
        rw [harg,Nat.mul_one] at hh
        exact le_trans hh (sourceAppellPolynomial_degree n)
      exact le_trans (Polynomial.natDegree_C_mul_le _ _) hcomp
    have hsamp (i : ℕ) (hi : i ≤ n) : IntegralAt p (P.eval ((1+i : ℤ) : ℚ)) := by
      have hh := hcore (i+1) (by omega)
      simp only [dyadicCore,ite_eq_right (by omega : i+1 ≠ 0),Nat.add_sub_cancel] at hh
      have heq : P.eval ((1+i : ℤ) : ℚ) =
          u*(sourceAppellPolynomial n).eval ((2*(i+1) : ℕ) : ℚ) := by
        simp only [P,Polynomial.eval_C_mul,Polynomial.eval_comp,
          Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
        congr 2
        push_cast
        ring
      rw [heq]
      exact hh
    have hlower : ClearsLocal p u (sourceAppellPolynomial n) := by
      intro x hx
      have hxhalf : IntegralAt p (x/2) := by
        rw [div_eq_mul_inv]
        exact integralAt_mul hx (integralAt_two_inv hp2)
      have hv := consecutive_samples_local hp2 n P hdeg 1 hsamp (x/2) hxhalf
      have heq : P.eval (x/2)=u*(sourceAppellPolynomial n).eval x := by
        simp only [P,Polynomial.eval_C_mul,Polynomial.eval_comp,
          Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
        rw [show (2 : ℚ)*(x/2)=x by ring]
      rwa [heq] at hv
    exact clearsLocal_upper hp2 u (sourceAppellPolynomial (n+1)) (sourceAppellPolynomial n)
      (n+1) 1 (sourceAppellPolynomial_difference n) hlower hbase
  · intro hQ b hb
    obtain ⟨hlower,hbase⟩ := (clearsLocal_step hp2 u (sourceAppellPolynomial (n+1))
      (sourceAppellPolynomial n) (n+1) 1 (sourceAppellPolynomial_difference n)).mp hQ
    by_cases hb0 : b=0
    · subst b
      simp only [dyadicCore,ite_true]
      exact (halfMoment_local_iff hp2 u (n+1)).mpr hbase
    · simp only [dyadicCore,ite_eq_right hb0,Nat.add_sub_cancel]
      apply hlower
      unfold IntegralAt
      rw [padicValRat.of_nat]
      exact Int.natCast_nonneg _

/-- Exact odd-prime common-denominator characterization on the actual finite
source dyadic evaluator, with an explicit sufficient grid size. -/
theorem dyadic_local_coefficients_iff {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (u : ℚ) (n L : ℕ) (hL : n+2 ≤ L) :
    (∀ b, b < L → IntegralAt p (u*dyadicNormalized (n+1) b)) ↔
      ∀ i, i ≤ n+1 → IntegralAt p (u*PowerSeries.coeff i momentSeries) := by
  rw [dyadic_prefix_core_iff u n L,dyadic_core_local_iff hp2 u n L hL,
    sourceAppell_local_characterization hp2]

lemma grid_size_bound (n : ℕ) : n+4 ≤ 2^(n+2) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [show n+1+2=(n+2)+1 by omega,pow_succ]
    omega

/-- The full printed odd-numerator grid at every level >=3. -/
theorem full_dyadic_grid_local_coefficients_iff {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (u : ℚ) (n : ℕ) :
    (∀ b, b < 2^(n+2) → IntegralAt p (u*dyadicNormalized (n+3) b)) ↔
      ∀ i, i ≤ n+3 → IntegralAt p (u*PowerSeries.coeff i momentSeries) := by
  simpa only [Nat.add_assoc] using
    dyadic_local_coefficients_iff hp2 u (n+2) (2^(n+2)) (grid_size_bound n)

#print axioms full_dyadic_grid_local_coefficients_iff
end FabiusProofLane
```

### `RationalLCM.lean`

```lean
import DyadicLocalCharacterization
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Data.Nat.Factorization.Basic

namespace FabiusProofLane
open Finset

lemma prime_scale_integral_iff {p : ℕ} [hp : Fact p.Prime] (a : ℕ) (q : ℚ) :
    IntegralAt p ((p : ℚ)^a*q) ↔ q.den.factorization p ≤ a := by
  rw [Nat.factorization_def _ hp.out]
  by_cases hq : q=0
  · simp [hq,IntegralAt]
  unfold IntegralAt
  rw [padicValRat.mul (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)) hq,
    padicValRat.pow,padicValRat.self hp.out.one_lt,mul_one]
  unfold padicValRat
  have hn : (0 : ℤ) ≤ padicValInt p q.num := Int.natCast_nonneg _
  have hd : (0 : ℤ) ≤ padicValNat p q.den := Int.natCast_nonneg _
  rcases Rat.num_or_den_zero_padicVal q hp.out with hnum | hden
  · rw [hnum]
    constructor <;> intro h <;> omega
  · simp [hden]
    omega

noncomputable def rationalLCM (S : Finset ℕ) (q : ℕ → ℚ) : ℕ := S.lcm (fun i => (q i).den)

lemma rationalLCM_ne_zero (S : Finset ℕ) (q : ℕ → ℚ) : rationalLCM S q ≠ 0 := by
  apply Finset.lcm_ne_zero_iff.mpr
  intro i hi
  exact Rat.den_nz (q i)

lemma rationalLCM_prime_scale_iff {p : ℕ} [hp : Fact p.Prime]
    (S : Finset ℕ) (q : ℕ → ℚ) (a : ℕ) :
    (rationalLCM S q).factorization p ≤ a ↔
      ∀ i ∈ S, IntegralAt p ((p : ℚ)^a*q i) := by
  rw [rationalLCM,Finset.factorization_lcm (fun i _ => Rat.den_nz (q i)),Finset.sup_le_iff]
  constructor
  · intro h i hi
    exact (prime_scale_integral_iff a (q i)).mpr (h i hi)
  · intro h i hi
    exact (prime_scale_integral_iff a (q i)).mp (h i hi)

noncomputable def normalizedGridLCM (n : ℕ) : ℕ :=
  rationalLCM (range (2^(n-1))) (dyadicNormalized n)

lemma normalizedGridLCM_ne_zero (n : ℕ) : normalizedGridLCM n ≠ 0 :=
  rationalLCM_ne_zero _ _

/-- Literal finite-denominator exponent characterization, at every level >=3. -/
theorem normalizedGridLCM_odd_prime_iff {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (n a : ℕ) :
    (normalizedGridLCM (n+3)).factorization p ≤ a ↔
      ∀ i, i ≤ n+3 → IntegralAt p ((p : ℚ)^a*PowerSeries.coeff i momentSeries) := by
  rw [normalizedGridLCM,rationalLCM_prime_scale_iff]
  simp only [mem_range,show n+3-1=n+2 by omega]
  exact full_dyadic_grid_local_coefficients_iff hp2 _ n

lemma prefix_odd_coefficient_iff {p : ℕ} [hp : Fact p.Prime] (u : ℚ) (m : ℕ) :
    (∀ i, i ≤ 2*m+1 → IntegralAt p (u*PowerSeries.coeff i momentSeries)) ↔
      ∀ i, i ≤ 2*m → IntegralAt p (u*PowerSeries.coeff i momentSeries) := by
  constructor
  · intro h i hi
    exact h i (by omega)
  · intro h i hi
    by_cases hil : i ≤ 2*m
    · exact h i hil
    · have heq : i=2*m+1 := by omega
      rw [heq,momentSeries_odd,mul_zero]
      exact integralAt_zero p

/-- The odd-prime part of the printed even/odd level equality. -/
theorem normalizedGridLCM_pair_odd_prime {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (m : ℕ) :
    (normalizedGridLCM (2*m+4)).factorization p =
      (normalizedGridLCM (2*m+5)).factorization p := by
  have hequiv (a : ℕ) : (normalizedGridLCM (2*m+4)).factorization p ≤ a ↔
      (normalizedGridLCM (2*m+5)).factorization p ≤ a := by
    have h1 := normalizedGridLCM_odd_prime_iff hp2 (2*m+1) a
    have h2 := normalizedGridLCM_odd_prime_iff hp2 (2*m+2) a
    simp only [show 2*m+1+3=2*m+4 by omega] at h1
    simp only [show 2*m+2+3=2*m+5 by omega] at h2
    rw [h1,h2]
    have h := prefix_odd_coefficient_iff (p:=p) ((p : ℚ)^a) (m+2)
    simpa only [Nat.mul_add,Nat.mul_one] using h.symm
  exact le_antisymm ((hequiv _).mpr (le_refl _)) ((hequiv _).mp (le_refl _))

#print axioms normalizedGridLCM_pair_odd_prime
end FabiusProofLane
```

### `TwoAdicGrid.lean`

```lean
import RationalLCM

namespace FabiusProofLane
open Finset

local instance primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

lemma factorial_appell_integral_two (n : ℕ) (z : ℤ) :
    IntegralAt 2 ((n.factorial : ℚ)*(sourceAppellPolynomial n).eval (z : ℚ)) := by
  rw [sourceAppellPolynomial_formula,mul_div_cancel₀ _ (by positivity)]
  apply integralAt_sum
  intro k hk
  apply integralAt_mul
  · apply integralAt_mul
    · unfold IntegralAt
      rw [padicValRat.of_nat]
      exact Int.natCast_nonneg _
    · exact (integralSubring 2).pow_mem (integralAt_int 2 z) _
  · unfold IntegralAt
    rw [Fabius.moment_padicVal_two]

lemma factorial_core_integral_two (n b : ℕ) :
    IntegralAt 2 ((2*((n+1).factorial : ℚ))*dyadicCore (n+1) b) := by
  by_cases hb : b=0
  · simp only [dyadicCore,ite_eq_left hb]
    have heq : (2*((n+1).factorial : ℚ))*(Fabius.halfMoment (n+1)/((n+1).factorial : ℚ)) =
        2*Fabius.halfMoment (n+1) := by
      have hf : (((n+1).factorial : ℕ) : ℚ) ≠ 0 := by positivity
      field_simp
    rw [heq]
    unfold IntegralAt
    rw [(Fabius.two_mul_halfMoment_padicVal_two_and_odd (n+1) (by omega)).1]
  · simp only [dyadicCore,ite_eq_right hb,Nat.add_sub_cancel]
    have hh : IntegralAt 2 ((n.factorial : ℚ)*(sourceAppellPolynomial n).eval ((2*b : ℕ) : ℚ)) := by
      simpa using factorial_appell_integral_two n ((2*b : ℕ) : ℤ)
    have hz : IntegralAt 2 ((2*((n+1) : ℚ)) : ℚ) := by
      have h := integralAt_int 2 ((2*(n+1) : ℕ) : ℤ)
      simpa using h
    have hmul := integralAt_mul hz hh
    have heq : (2*((n+1) : ℚ))*((n.factorial : ℚ)*
        (sourceAppellPolynomial n).eval ((2*b : ℕ) : ℚ)) =
        (2*((n+1).factorial : ℚ))*(sourceAppellPolynomial n).eval ((2*b : ℕ) : ℚ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hm : IntegralAt 2 ((2*((n+1) : ℚ))*((n.factorial : ℚ)*
        (sourceAppellPolynomial n).eval ((2*b : ℕ) : ℚ))) := by
      simpa only [Nat.cast_add,Nat.cast_one] using hmul
    rwa [heq] at hm

lemma two_factorial_valuation (n : ℕ) :
    padicValRat 2 (2*(n.factorial : ℚ)) = 1+(padicValNat 2 n.factorial : ℤ) := by
  rw [padicValRat.mul (by norm_num) (by positivity),
    show (2 : ℚ)=((2 : ℕ) : ℚ) by norm_num,padicValRat.of_nat,padicValNat_self,
    padicValRat.of_nat]
  rfl

lemma core_zero_prime_scale_two (n a : ℕ) :
    IntegralAt 2 ((2 : ℚ)^a*dyadicCore (n+1) 0) ↔
      1+padicValNat 2 (n+1).factorial ≤ a := by
  simp only [dyadicCore,ite_true]
  unfold IntegralAt
  rw [padicValRat.mul (by positivity)
    (div_ne_zero (ne_of_gt (Fabius.halfMoment_pos (n+1))) (by positivity)),
    padicValRat.pow,show padicValRat 2 (2 : ℚ)=1 from padicValRat.self (by decide),mul_one,
    padicValRat.div (ne_of_gt (Fabius.halfMoment_pos (n+1))) (by positivity),
    Fabius.halfMoment_padicVal_two (n+1) (by omega),padicValRat.of_nat]
  constructor <;> intro h <;> omega

lemma core_prefix_prime_scale_two (n a L : ℕ) (hL : 0 < L) :
    (∀ b, b < L → IntegralAt 2 ((2 : ℚ)^a*dyadicCore (n+1) b)) ↔
      1+padicValNat 2 (n+1).factorial ≤ a := by
  constructor
  · intro h
    exact (core_zero_prime_scale_two n a).mp (h 0 hL)
  · intro ha b hb
    have hratio : IntegralAt 2 ((2 : ℚ)^a/(2*((n+1).factorial : ℚ))) := by
      unfold IntegralAt
      rw [padicValRat.div (by positivity) (by positivity),padicValRat.pow,
        show padicValRat 2 (2 : ℚ)=1 from padicValRat.self (by decide),mul_one,two_factorial_valuation]
      have hh : (1 : ℤ)+padicValNat 2 (n+1).factorial ≤ a := by exact_mod_cast ha
      omega
    have hh := integralAt_mul hratio (factorial_core_integral_two n b)
    have heq : ((2 : ℚ)^a/(2*((n+1).factorial : ℚ)))*
        ((2*((n+1).factorial : ℚ))*dyadicCore (n+1) b) =
        (2 : ℚ)^a*dyadicCore (n+1) b := by
      have hf : (((n+1).factorial : ℕ) : ℚ) ≠ 0 := by positivity
      field_simp
    simpa only [heq] using hh

/-- Exact 2-primary exponent of the common normalized dyadic denominator. -/
theorem normalizedGridLCM_two (n : ℕ) :
    (normalizedGridLCM (n+1)).factorization 2=1+padicValNat 2 (n+1).factorial := by
  have hequiv (a : ℕ) : (normalizedGridLCM (n+1)).factorization 2 ≤ a ↔
      1+padicValNat 2 (n+1).factorial ≤ a := by
    rw [normalizedGridLCM,rationalLCM_prime_scale_iff]
    simp only [mem_range,Nat.add_sub_cancel]
    rw [dyadic_prefix_core_iff]
    exact core_prefix_prime_scale_two n a (2^n) (by positivity)
  exact le_antisymm ((hequiv _).mpr (le_refl _)) ((hequiv _).mp (le_refl _))

#print axioms normalizedGridLCM_two
end FabiusProofLane
```

### `NaturalGridResults.lean`

```lean
import TwoAdicGrid

namespace FabiusProofLane
open Finset

lemma odd_factorial_padic_two (m : ℕ) :
    padicValNat 2 (2*m+5).factorial=padicValNat 2 (2*m+4).factorial := by
  have heq : 2*m+5=(2*m+4)+1 := by omega
  rw [heq,Nat.factorial_succ,padicValNat.mul (by omega) (Nat.factorial_ne_zero _)]
  have hnot : ¬2 ∣ 2*m+5 := by omega
  rw [padicValNat.eq_zero_of_not_dvd hnot,zero_add]

/-- Full adjacent-level equality for the normalized finite-grid lcm, from level 4. -/
theorem normalizedGridLCM_pair (m : ℕ) :
    normalizedGridLCM (2*m+4)=normalizedGridLCM (2*m+5) := by
  apply Nat.factorization_inj (normalizedGridLCM_ne_zero _) (normalizedGridLCM_ne_zero _)
  ext p
  by_cases hp : p.Prime
  · letI : Fact p.Prime := ⟨hp⟩
    by_cases hp2 : p=2
    · subst p
      have h1 := normalizedGridLCM_two (2*m+3)
      have h2 := normalizedGridLCM_two (2*m+4)
      simp only [show 2*m+3+1=2*m+4 by omega] at h1
      simp only [show 2*m+4+1=2*m+5 by omega] at h2
      rw [h1,h2,odd_factorial_padic_two]
    · exact normalizedGridLCM_pair_odd_prime hp2 m
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

lemma normalizedGridLCM_one : normalizedGridLCM 1=2 := by
  norm_num [normalizedGridLCM,rationalLCM,dyadicNormalized,Fabius.fabiusDyadic,
    Fabius.thueMorseSign,Fabius.binaryWeight,Fabius.moment,Fin.sum_univ_succ,
    Finset.range_add_one,lcm_eq_nat_lcm,Nat.choose,Nat.factorial]
lemma normalizedGridLCM_two_value : normalizedGridLCM 2=36 := by
  norm_num [normalizedGridLCM,rationalLCM,dyadicNormalized,Fabius.fabiusDyadic,
    Fabius.thueMorseSign,Fabius.binaryWeight,Fabius.moment,Fin.sum_univ_succ,
    Finset.range_add_one,lcm_eq_nat_lcm,Nat.choose,Nat.factorial]
lemma normalizedGridLCM_three : normalizedGridLCM 3=36 := by
  norm_num [normalizedGridLCM,rationalLCM,dyadicNormalized,Fabius.fabiusDyadic,
    Fabius.thueMorseSign,Fabius.binaryWeight,Fabius.moment,Fin.sum_univ_succ,
    Finset.range_add_one,lcm_eq_nat_lcm,Nat.choose,Nat.factorial]

theorem normalizedGridLCM_even_odd (n : ℕ) (hn : 1 ≤ n) :
    normalizedGridLCM (2*n)=normalizedGridLCM (2*n+1) := by
  by_cases h1 : n=1
  · subst n
    rw [normalizedGridLCM_two_value,normalizedGridLCM_three]
  · have hm : 2*(n-2)+4=2*n := by omega
    have hm' : 2*(n-2)+5=2*n+1 := by omega
    simpa only [hm,hm'] using normalizedGridLCM_pair (n-2)

/-- The new weighted coefficient witness forces the missing odd-prime divisor. -/
lemma normalizedGridLCM_odd_factorial_prime {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (m : ℕ) :
    (2*m+3).factorial.factorization p ≤ (normalizedGridLCM (2*m+3)).factorization p := by
  let a := (normalizedGridLCM (2*m+3)).factorization p
  have hc := (normalizedGridLCM_odd_prime_iff hp2 (2*m) a).mp (le_refl a)
  obtain ⟨j,hj,hv⟩ := source_moment_denominator_witness p (2*m+2) hp2
  have hi := hc (2*j) (by omega)
  rw [momentSeries_even] at hi
  have hj0 : sourceCoefficient j ≠ 0 := by
    rw [sourceCoefficient_eq_explicit]
    exact ne_of_gt (evenCoefficient_pos j)
  unfold IntegralAt at hi
  rw [padicValRat.mul (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)) hj0,
    padicValRat.pow,padicValRat.self hp.out.one_lt,mul_one] at hi
  change (padicValNat p (2*m+2+1).factorial : ℤ) ≤ -padicValRat p (sourceCoefficient j) at hv
  rw [show 2*m+2+1=2*m+3 by omega] at hv
  rw [Nat.factorization_def _ hp.out]
  have hh : (padicValNat p (2*m+3).factorial : ℤ) ≤ a := by omega
  exact_mod_cast hh

/-- The printed factorial divisor for every odd level >=3, on the actual normalized grid. -/
theorem normalizedGridLCM_odd_factorial (m : ℕ) :
    2*(2*m+3).factorial ∣ normalizedGridLCM (2*m+3) := by
  apply (Nat.factorization_le_iff_dvd (by positivity) (normalizedGridLCM_ne_zero _)).mp
  intro p
  by_cases hp : p.Prime
  · letI : Fact p.Prime := ⟨hp⟩
    rw [Nat.factorization_mul (by decide) (Nat.factorial_ne_zero _),Finsupp.add_apply]
    by_cases hp2 : p=2
    · subst p
      have hh := normalizedGridLCM_two (2*m+2)
      simp only [show 2*m+2+1=2*m+3 by omega] at hh
      rw [Nat.factorization_def _ Nat.prime_two,Nat.factorization_def _ Nat.prime_two,
        padicValNat_self,hh]
    · have hnot : ¬p ∣ 2 := by
        intro h
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
      rw [Nat.factorization_def 2 hp,padicValNat.eq_zero_of_not_dvd hnot,zero_add]
      exact normalizedGridLCM_odd_factorial_prime hp2 m
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

#print axioms normalizedGridLCM_even_odd
#print axioms normalizedGridLCM_odd_factorial
end FabiusProofLane
```

### `RawGridNormalization.lean`

```lean
import TwoAdicGrid

namespace FabiusProofLane
open Finset

noncomputable def rawGridLCM (n : ℕ) : ℕ :=
  rationalLCM (range (2^(n-1))) (fun b => Fabius.fabiusDyadic n (2*b+1))
lemma rawGridLCM_ne_zero (n : ℕ) : rawGridLCM n ≠ 0 := rationalLCM_ne_zero _ _

lemma rawGridLCM_odd_prime {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (n : ℕ) :
    (rawGridLCM n).factorization p=(normalizedGridLCM n).factorization p := by
  have hequiv (a : ℕ) : (rawGridLCM n).factorization p ≤ a ↔
      (normalizedGridLCM n).factorization p ≤ a := by
    rw [rawGridLCM,normalizedGridLCM,rationalLCM_prime_scale_iff,rationalLCM_prime_scale_iff]
    apply forall_congr'
    intro b
    apply imp_congr_right
    intro hb
    have heq : (2 : ℚ)^n.choose 2*((p : ℚ)^a*Fabius.fabiusDyadic n (2*b+1)) =
        (p : ℚ)^a*dyadicNormalized n b := by dsimp [dyadicNormalized]; ring
    rw [← heq]
    exact (integralAt_two_pow_iff hp2 (n.choose 2) _).symm
  exact le_antisymm ((hequiv _).mpr (le_refl _)) ((hequiv _).mp (le_refl _))

lemma rawGridLCM_two (n : ℕ) :
    (rawGridLCM (n+1)).factorization 2=(n+1).choose 2+
      (normalizedGridLCM (n+1)).factorization 2 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let a := (normalizedGridLCM (n+1)).factorization 2
  have hclear : ∀ b ∈ range (2^n), IntegralAt 2 ((2 : ℚ)^a*dyadicNormalized (n+1) b) := by
    apply (rationalLCM_prime_scale_iff _ _ a).mp
    have heq : rationalLCM (range (2^n)) (dyadicNormalized (n+1))=normalizedGridLCM (n+1) := by
      simp only [normalizedGridLCM,Nat.add_sub_cancel]
    rw [heq]
  have hupper : (rawGridLCM (n+1)).factorization 2 ≤ (n+1).choose 2+a := by
    apply (rationalLCM_prime_scale_iff _ _ _).mpr
    intro b hb
    have hh := hclear b (by simpa only [Nat.add_sub_cancel] using hb)
    have heq : (2 : ℚ)^((n+1).choose 2+a)*Fabius.fabiusDyadic (n+1) (2*b+1)=
        (2 : ℚ)^a*dyadicNormalized (n+1) b := by
      rw [pow_add,dyadicNormalized]
      ring
    rw [← heq] at hh
    simpa only [Nat.cast_ofNat] using hh
  have hfirst : (Fabius.fabiusAtInverseTwoPow (n+1)).den.factorization 2 ≤
      (rawGridLCM (n+1)).factorization 2 := by
    have hz : 0 ∈ range (2^(n+1-1)) := by simp
    have hh : (Fabius.fabiusDyadic (n+1) (2*0+1)).den.factorization 2 ≤
        (rawGridLCM (n+1)).factorization 2 := by
      rw [rawGridLCM,rationalLCM,Finset.factorization_lcm (fun i _ => Rat.den_nz _)]
      exact Finset.le_sup (f:=fun b => (Fabius.fabiusDyadic (n+1) (2*b+1)).den.factorization 2) hz
    simpa only [Fabius.fabiusAtInverseTwoPow,Nat.mul_zero,Nat.zero_add] using hh
  rw [Nat.factorization_def _ Nat.prime_two,
    Fabius.fabiusAtInverseTwoPow_den_padicVal_two (n+1) (by omega)] at hfirst
  have ha : a=1+padicValNat 2 (n+1).factorial := normalizedGridLCM_two n
  omega

/-- Scaling by the printed power of two gives precisely the normalized common denominator. -/
theorem rawGridLCM_eq_scale (n : ℕ) :
    rawGridLCM (n+1)=2^((n+1).choose 2)*normalizedGridLCM (n+1) := by
  apply Nat.factorization_inj (rawGridLCM_ne_zero _)
    (mul_ne_zero (by positivity) (normalizedGridLCM_ne_zero _))
  ext p
  rw [Nat.factorization_mul (by positivity) (normalizedGridLCM_ne_zero _),Finsupp.add_apply,
    Nat.prime_two.factorization_pow,Finsupp.single_apply]
  by_cases hp : p.Prime
  · letI : Fact p.Prime := ⟨hp⟩
    by_cases hp2 : p=2
    · subst p
      simp only [ite_true]
      exact rawGridLCM_two n
    · rw [if_neg (Ne.symm hp2),zero_add]
      exact rawGridLCM_odd_prime hp2 (n+1)
  · have hp2 : 2 ≠ p := by intro h; subst p; exact hp Nat.prime_two
    rw [if_neg hp2,zero_add]
    simp [Nat.factorization_eq_zero_of_not_prime _ hp]

#print axioms rawGridLCM_eq_scale
end FabiusProofLane
```

### `SourceNormalization.lean`

```lean
import RawGridNormalization

namespace FabiusProofLane
open Finset

lemma oddNumerators_image (n : ℕ) :
    Fabius.oddDyadicNumerators (n+1)=(range (2^n)).image (fun b => 2*b+1) := by
  ext a
  simp only [Fabius.oddDyadicNumerators,mem_filter,mem_Icc,mem_image,mem_range]
  rw [pow_succ]
  constructor
  · rintro ⟨⟨ha,hb⟩,⟨b,hb'⟩⟩
    exact ⟨b,by omega,by omega⟩
  · rintro ⟨b,hb,rfl⟩
    refine ⟨⟨by omega,by omega⟩,⟨b,by omega⟩⟩

lemma fabiusDenominator_eq_raw (n : ℕ) :
    Fabius.fabiusDyadicDenominator (n+1)=rawGridLCM (n+1) := by
  rw [Fabius.fabiusDyadicDenominator,oddNumerators_image,Finset.lcm_image]
  simp only [rawGridLCM,rationalLCM,Nat.add_sub_cancel]
  rfl

lemma rvachev_den_reflection (n a : ℕ) (ha : a ∈ Fabius.oddDyadicNumerators n) :
    (Fabius.rvachevDyadic n (a : ℤ)).den=(Fabius.fabiusDyadic n (2^n-a)).den := by
  have hb : a ≤ 2^n := by
    have h := (mem_Icc.mp (mem_filter.mp ha).1).2
    exact le_trans h (Nat.sub_le _ _)
  simp [Fabius.rvachevDyadic,hb]

lemma sourceDenominator_eq_fabius (n : ℕ) (hn : 1 ≤ n) :
    Fabius.dyadicDenominator n=Fabius.fabiusDyadicDenominator n := by
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro a ha
    rw [rvachev_den_reflection n a ha]
    exact Finset.dvd_lcm (Fabius.oddDyadicNumerators_reflect_mem n a hn ha)
  · apply Finset.lcm_dvd
    intro a ha
    have hb := Fabius.oddDyadicNumerators_reflect_mem n a hn ha
    have hbound : a ≤ 2^n := by
      have h := (mem_Icc.mp (mem_filter.mp ha).1).2
      exact le_trans h (Nat.sub_le _ _)
    have hh : (Fabius.rvachevDyadic n ((2^n-a : ℕ) : ℤ)).den ∣
        Fabius.dyadicDenominator n := Finset.dvd_lcm hb
    rw [rvachev_den_reflection n _ hb,Nat.sub_sub_self hbound] at hh
    exact hh

/-- The source's literal A_n is the natural lcm used in the local proof. -/
theorem source_normalization (n : ℕ) :
    Fabius.normalizedDyadicDenominator (n+1)=(normalizedGridLCM (n+1) : ℚ) := by
  rw [Fabius.normalizedDyadicDenominator,sourceDenominator_eq_fabius _ (by omega),
    fabiusDenominator_eq_raw,rawGridLCM_eq_scale,Nat.cast_mul,Nat.cast_pow]
  norm_num only [Nat.cast_ofNat]
  field_simp

#print axioms source_normalization
end FabiusProofLane
```

### `LiteralConjectureSixteen.lean`

```lean
import SourceNormalization
import NaturalGridResults

/- This proposition is copied verbatim from the public ProveIt PaperStatements.lean,
   lines 676--684 (its import there includes analytic material irrelevant here).
   Its arithmetic definitions come from the unchanged public Arithmetic.lean. -/
namespace Fabius
def conjecture_sixteen : Prop :=
  (∀ n : ℕ, 1 ≤ n →
    normalizedDyadicDenominator (2 * n) =
      normalizedDyadicDenominator (2 * n + 1)) ∧
  (∀ n : ℕ, 2 ≤ n →
    conjecturalK n = normalizedDyadicDenominator (2 * n - 2)) ∧
  (∀ n : ℕ, 1 ≤ n →
    ∃ q : ℕ, conjecturalK n = (2 * (2 * n - 1).factorial * q : ℕ)) ∧
  (∀ n : ℕ, 1 ≤ n → IsOddNatural (conjecturalH n))
end Fabius

namespace FabiusProofLane

lemma normalizedGridLCM_odd_quotient (m : ℕ) :
    ∃ q : ℕ, Odd q ∧ normalizedGridLCM (2*m+3)=2*(2*m+3).factorial*q := by
  obtain ⟨q,hq⟩ := normalizedGridLCM_odd_factorial m
  have hq0 : q ≠ 0 := by
    intro hz
    apply normalizedGridLCM_ne_zero (2*m+3)
    simpa [hz] using hq
  have hT0 : 2*(2*m+3).factorial ≠ 0 := by positivity
  have hv := congrArg (fun x : ℕ => x.factorization 2) hq
  rw [Nat.factorization_mul hT0 hq0,Finsupp.add_apply,
    Nat.factorization_mul (by decide) (Nat.factorial_ne_zero _),Finsupp.add_apply,
    Nat.factorization_def 2 Nat.prime_two,padicValNat_self,
    Nat.factorization_def (2*m+3).factorial Nat.prime_two] at hv
  have hM := normalizedGridLCM_two (2*m+2)
  simp only [show 2*m+2+1=2*m+3 by omega] at hM
  have hqv : q.factorization 2=0 := by omega
  have hodd : Odd q := by
    rw [← Nat.not_even_iff_odd,even_iff_two_dvd]
    intro hd
    have hh := one_le_padicValNat_of_dvd hq0 hd
    rw [Nat.factorization_def _ Nat.prime_two] at hqv
    omega
  exact ⟨q,hodd,hq⟩

lemma source_normalization_pos (n : ℕ) (hn : 1 ≤ n) :
    Fabius.normalizedDyadicDenominator n=(normalizedGridLCM n : ℚ) := by
  have heq : n-1+1=n := by omega
  simpa only [heq] using source_normalization (n-1)

lemma source_A_pair (n : ℕ) (hn : 1 ≤ n) :
    Fabius.normalizedDyadicDenominator (2*n)=
      Fabius.normalizedDyadicDenominator (2*n+1) := by
  rw [source_normalization_pos _ (by omega),source_normalization_pos _ (by omega),
    normalizedGridLCM_even_odd n hn]

lemma source_K_odd_quotient (n : ℕ) (hn : 1 ≤ n) :
    ∃ q : ℕ, Odd q ∧ Fabius.conjecturalK n=(2*(2*n-1).factorial*q : ℕ) := by
  rw [Fabius.conjecturalK,source_normalization_pos _ (by omega)]
  by_cases h1 : n=1
  · subst n
    exact ⟨1,by decide,by norm_num [normalizedGridLCM_one]⟩
  · have heq : 2*(n-2)+3=2*n-1 := by omega
    obtain ⟨q,hodd,hq⟩ := normalizedGridLCM_odd_quotient (n-2)
    rw [heq] at hq
    exact ⟨q,hodd,by exact_mod_cast hq⟩

/-- All clauses of the source's Conjecture 16, with its literal rational definitions. -/
theorem conjecture_sixteen_proved : Fabius.conjecture_sixteen := by
  refine ⟨source_A_pair,?_,?_,?_⟩
  · intro n hn
    unfold Fabius.conjecturalK
    have h := source_A_pair (n-1) (by omega)
    have h1 : 2*(n-1)=2*n-2 := by omega
    have h2 : 2*(n-1)+1=2*n-1 := by omega
    rw [h2,h1] at h
    exact h.symm
  · intro n hn
    obtain ⟨q,hodd,hq⟩ := source_K_odd_quotient n hn
    exact ⟨q,hq⟩
  · intro n hn
    obtain ⟨q,hodd,hq⟩ := source_K_odd_quotient n hn
    refine ⟨q,hodd,?_⟩
    rw [Fabius.conjecturalH,hq]
    norm_num only [Nat.cast_mul,Nat.cast_ofNat]
    have hfact : (Nat.factorial (2*n-1) : ℚ) ≠ 0 := by positivity
    field_simp

#print axioms conjecture_sixteen_proved
end FabiusProofLane
```

### `ArithmeticEndpoint.lean`

```lean
import LiteralConjectureSixteen

namespace FabiusProofLane

/-- The three printed clauses for the recurrence-defined rational dyadic grid.
This endpoint imports no analytic Fabius module and assumes no function exists. -/
theorem mathdb335354_arithmetic :
    (∀ n : ℕ, 1 ≤ n →
      Fabius.normalizedDyadicDenominator (2 * n) =
        Fabius.normalizedDyadicDenominator (2 * n + 1)) ∧
    (∀ n : ℕ, 1 ≤ n → ∃ q : ℕ,
      Fabius.conjecturalK n = (2 * (2 * n - 1).factorial * q : ℕ)) ∧
    (∀ n : ℕ, 1 ≤ n → Fabius.IsOddNatural (Fabius.conjecturalH n)) :=
  ⟨conjecture_sixteen_proved.1, conjecture_sixteen_proved.2.2⟩

#print mathdb335354_arithmetic
#print axioms mathdb335354_arithmetic
end FabiusProofLane
```

### `UpstreamBasic.lean`

```lean
import UpstreamArithmetic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Analytic definitions for the Fabius function

This file deliberately separates two functions that are both denoted by `F` in
the literature:

* `BoundedFabius` is the type of cumulative-distribution candidates taking
  values in `[0, 1]`.  `IsFabius` records, among other properties, that the
  function is zero to the left of the unit interval and one to its right.
* `extendedFabius` is the signed smooth extension to all of `ℝ` used in Juan
  Arias de Reyna, *Arithmetic of the Fabius function*, arXiv:1702.06487v3,
  equation (1).  It need not take values in `[0, 1]` outside that interval.

Keeping these objects distinct prevents the global codomain mismatch in the
paper while retaining a convenient subtype-valued API for the bounded
function.  `IsFabius` records the standard characterization used on the unit
interval.  Existence and uniqueness, and the analytic identities relating the
integrals below to the exact rational sequences in `FabiusFunction.Arithmetic`,
are intentionally left to subsequent files.
-/

set_option autoImplicit false

open scoped BigOperators ContDiff
open Set

namespace Fabius

/-- The closed unit interval, used as the codomain of the bounded Fabius function. -/
abbrev UnitInterval := Set.Icc (0 : ℝ) 1

/-- A bounded Fabius candidate, defined on all reals and valued in `[0, 1]`. -/
abbrev BoundedFabius := ℝ → UnitInterval

/-- Forget the interval-valued codomain of a bounded Fabius candidate. -/
abbrev fabiusReal (F : BoundedFabius) : ℝ → ℝ :=
  fun x => F x

/-- The real-valued view of a bounded Fabius candidate is its underlying
coercion.  This is definitional, and is a `simp` lemma so that statements
about `fabiusReal F` and about `(F x : ℝ)` normalize to the same form. -/
@[simp]
theorem fabiusReal_apply (F : BoundedFabius) (x : ℝ) :
    fabiusReal F x = (F x : ℝ) :=
  rfl

/-- Every bounded Fabius candidate is nonnegative after coercion to `ℝ`. -/
theorem fabiusReal_nonneg (F : BoundedFabius) (x : ℝ) :
    0 ≤ fabiusReal F x :=
  (F x).property.1

/-- Every bounded Fabius candidate is at most one after coercion to `ℝ`. -/
theorem fabiusReal_le_one (F : BoundedFabius) (x : ℝ) :
    fabiusReal F x ≤ 1 :=
  (F x).property.2

/--
The standard bounded/CDF characterization of the Fabius function.

The derivative equation is asserted only on `[0, 1/2]`; the global signed
extension has a different role and is defined separately below.
-/
structure IsFabius (F : BoundedFabius) : Prop where
  zero_of_nonpos : ∀ x, x ≤ 0 → fabiusReal F x = 0
  one_of_one_le : ∀ x, 1 ≤ x → fabiusReal F x = 1
  contDiff : ContDiff ℝ ∞ (fabiusReal F)
  symmetry : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    fabiusReal F (1 - x) = 1 - fabiusReal F x
  hasDerivAt : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2),
    HasDerivAt (fabiusReal F) (2 * fabiusReal F (2 * x)) x

/-- The reflection identity in `IsFabius` automatically extends from the
unit interval to all real arguments using the two constant tails. -/
theorem IsFabius.symmetry_all {F : BoundedFabius} (hF : IsFabius F) (x : ℝ) :
    fabiusReal F (1 - x) = 1 - fabiusReal F x := by
  by_cases hx0 : x ≤ 0
  · rw [hF.one_of_one_le (1 - x) (by linarith), hF.zero_of_nonpos x hx0]
    norm_num
  · by_cases hx1 : 1 ≤ x
    · rw [hF.zero_of_nonpos (1 - x) (by linarith), hF.one_of_one_le x hx1]
      norm_num
    · exact hF.symmetry x ⟨le_of_not_ge hx0, le_of_not_ge hx1⟩

/-- A bounded Fabius function bundled with its defining properties. -/
abbrev FabiusFunction := {F : BoundedFabius // IsFabius F}

/--
Rvachev's `up` function obtained by folding the bounded Fabius function about
zero.  Under `IsFabius F`, its support is contained in `[-1, 1]`.
-/
noncomputable def rvachevUp (F : BoundedFabius) (x : ℝ) : ℝ :=
  if x ≤ 0 then fabiusReal F (x + 1) else fabiusReal F (1 - x)

/-!
## Elementary values and bounds for Rvachev's function

These facts require no calculus: they follow from the two branches of the
definition of `rvachevUp` together with the unit-interval codomain of
`BoundedFabius`.  Collecting them next to the definition avoids the four
separate re-derivations that previously appeared downstream.
-/

/-- Unfolding of `rvachevUp` on the left branch. -/
theorem rvachevUp_of_nonpos (F : BoundedFabius) {x : ℝ} (hx : x ≤ 0) :
    rvachevUp F x = fabiusReal F (x + 1) := by
  rw [rvachevUp, if_pos hx]

/-- Unfolding of `rvachevUp` on the right branch. -/
theorem rvachevUp_of_pos (F : BoundedFabius) {x : ℝ} (hx : 0 < x) :
    rvachevUp F x = fabiusReal F (1 - x) := by
  rw [rvachevUp, if_neg (by linarith : ¬ x ≤ 0)]

/-- Rvachev's up function is nonnegative. -/
theorem rvachevUp_nonneg (F : BoundedFabius) (x : ℝ) : 0 ≤ rvachevUp F x := by
  rw [rvachevUp]
  split_ifs <;> exact fabiusReal_nonneg F _

/-- Rvachev's up function is at most one. -/
theorem rvachevUp_le_one (F : BoundedFabius) (x : ℝ) : rvachevUp F x ≤ 1 := by
  rw [rvachevUp]
  split_ifs <;> exact fabiusReal_le_one F _

/-- Rvachev's up function coincides with its own absolute value. -/
@[simp]
theorem abs_rvachevUp (F : BoundedFabius) (x : ℝ) :
    |rvachevUp F x| = rvachevUp F x :=
  abs_of_nonneg (rvachevUp_nonneg F x)

/-- Rvachev's up function is bounded by one in absolute value. -/
theorem abs_rvachevUp_le_one (F : BoundedFabius) (x : ℝ) :
    |rvachevUp F x| ≤ 1 := by
  rw [abs_rvachevUp]
  exact rvachevUp_le_one F x

/-- Rvachev's up function is bounded by one in norm. -/
theorem norm_rvachevUp_le_one (F : BoundedFabius) (x : ℝ) :
    ‖rvachevUp F x‖ ≤ 1 :=
  abs_rvachevUp_le_one F x

/-- Rvachev's up function takes its normalized value at the origin. -/
theorem rvachevUp_zero (F : BoundedFabius) (hF : IsFabius F) :
    rvachevUp F 0 = 1 := by
  rw [rvachevUp, if_pos le_rfl]
  simpa using hF.one_of_one_le 1 le_rfl

/-- The complex coercion of Rvachev's up function is bounded by one in norm. -/
theorem norm_coe_rvachevUp_le_one (F : BoundedFabius) (x : ℝ) :
    ‖(rvachevUp F x : ℂ)‖ ≤ 1 := by
  simpa [Complex.norm_real, Real.norm_eq_abs] using abs_rvachevUp_le_one F x
/-- Folding a bounded candidate about zero always produces an even function;
this fact does not require any of the Fabius equations. -/
theorem rvachevUp_even (F : BoundedFabius) : Function.Even (rvachevUp F) := by
  intro x
  by_cases hx : x = 0
  · subst x
    simp
  by_cases hxpos : 0 < x
  · have hnx : -x ≤ 0 := by linarith
    have hxnot : ¬ x ≤ 0 := not_le.mpr hxpos
    simp only [rvachevUp, if_pos hnx, if_neg hxnot]
    congr 1
    ring
  · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hxpos) hx
    have hnxnot : ¬ -x ≤ 0 := by linarith
    have hxle : x ≤ 0 := hxneg.le
    simp only [rvachevUp, if_neg hnxnot, if_pos hxle]
    congr 1
    ring

/-- Rvachev's function vanishes at and to the left of its lower support endpoint. -/
theorem rvachevUp_eq_zero_of_le_neg_one (F : BoundedFabius)
    (hF : IsFabius F) {x : ℝ} (hx : x ≤ -1) : rvachevUp F x = 0 := by
  rw [rvachevUp, if_pos (by linarith), hF.zero_of_nonpos _ (by linarith)]

/-- Rvachev's function vanishes at and to the right of its upper support endpoint. -/
theorem rvachevUp_eq_zero_of_one_le (F : BoundedFabius)
    (hF : IsFabius F) {x : ℝ} (hx : 1 ≤ x) : rvachevUp F x = 0 := by
  rw [rvachevUp, if_neg (by linarith), hF.zero_of_nonpos _ (by linarith)]

/-- Rvachev's function vanishes outside the open interval `(-1,1)`, including
at both endpoints. -/
theorem rvachevUp_eq_zero_of_not_mem_Ioo (F : BoundedFabius)
    (hF : IsFabius F) {x : ℝ} (hx : x ∉ Ioo (-1 : ℝ) 1) : rvachevUp F x = 0 := by
  rw [mem_Ioo, not_and_or] at hx
  rcases hx with hx | hx
  · exact rvachevUp_eq_zero_of_le_neg_one F hF (le_of_not_gt hx)
  · exact rvachevUp_eq_zero_of_one_le F hF (le_of_not_gt hx)

/-- The pointwise support of Rvachev's function is contained in the open
interval `(-1,1)`.  Its topological support is the closed interval `[-1,1]`. -/
theorem support_rvachev_subset_Ioo (F : BoundedFabius) (hF : IsFabius F) :
    Function.support (rvachevUp F) ⊆ Ioo (-1 : ℝ) 1 := by
  intro x hx
  by_contra hmem
  exact hx (rvachevUp_eq_zero_of_not_mem_Ioo F hF hmem)

/--
The signed global extension from equation (1) of Arias de Reyna's paper:
`F(x) = ∑ n, (-1)^w(n) up(x - 2n - 1)`.

For a function satisfying `IsFabius`, the summand is pointwise supported at
only finitely many indices.  The summability and agreement with the bounded
function on `[0, 1]` are exposed as later theorems rather than built into the
definition.
-/
noncomputable def extendedFabius (F : BoundedFabius) (x : ℝ) : ℝ :=
  ∑' n : ℕ, (-1 : ℝ) ^ binaryWeight n *
    rvachevUp F (x - 2 * (n : ℝ) - 1)

/-- The removable entire function `sin z / z`, normalized to `1` at zero. -/
noncomputable def complexSinc (z : ℂ) : ℂ :=
  if z = 0 then 1 else Complex.sin z / z

/-- The Fourier transform of Rvachev's function, with the paper's convention. -/
noncomputable def rvachevFourier (F : BoundedFabius) (z : ℂ) : ℂ :=
  ∫ t : ℝ, (rvachevUp F t : ℂ) *
    Complex.exp (-2 * Real.pi * Complex.I * t * z)

/-- The infinite sinc product in equation (5). -/
noncomputable def rvachevFourierProduct (z : ℂ) : ℂ :=
  ∏' n : ℕ, complexSinc (Real.pi * z / (2 : ℂ) ^ n)

/-- The moment power series on the right side of equation (7). -/
noncomputable def rvachevMomentSeries (z : ℂ) : ℂ :=
  ∑' n : ℕ, (-1 : ℂ) ^ n * (moment n : ℂ) /
    (Nat.factorial (2 * n) : ℂ) * (2 * Real.pi * z) ^ (2 * n)

/-- The exponential generating series `∑ d_n z^n / n!` in equation (17). -/
noncomputable def halfMomentGeneratingSeries (z : ℂ) : ℂ :=
  ∑' n : ℕ, (halfMoment n : ℂ) / (n.factorial : ℂ) * z ^ n

/-- The removable extension of `(exp x - 1) / x`, with value `1` at zero. -/
noncomputable def expm1Div (x : ℝ) : ℝ :=
  if x = 0 then 1 else (Real.exp x - 1) / x

/-- The removable singularity is filled with the correct value: the limit of
`(exp x - 1) / x` at the origin is `1`. -/
@[simp]
theorem expm1Div_zero : expm1Div 0 = 1 := by
  simp [expm1Div]

/-- Away from the origin the removable extension is the quotient itself. -/
theorem expm1Div_of_ne {x : ℝ} (hx : x ≠ 0) :
    expm1Div x = (Real.exp x - 1) / x := by
  simp [expm1Div, hx]

/-- The complex removable extension of `(exp z - 1) / z`. -/
noncomputable def complexExpm1Div (z : ℂ) : ℂ :=
  if z = 0 then 1 else (Complex.exp z - 1) / z

/-- The complex removable extension takes the value `1` at the origin, in
agreement with `expm1Div_zero`. -/
@[simp]
theorem complexExpm1Div_zero : complexExpm1Div 0 = 1 := by
  simp [complexExpm1Div]

/-- Away from the origin the complex removable extension is the quotient
itself. -/
theorem complexExpm1Div_of_ne {z : ℂ} (hz : z ≠ 0) :
    complexExpm1Div z = (Complex.exp z - 1) / z := by
  simp [complexExpm1Div, hz]

/-- The complex removable quotient restricts to the real removable quotient. -/
@[simp]
theorem complexExpm1Div_ofReal (x : ℝ) :
    complexExpm1Div (x : ℂ) = (expm1Div x : ℂ) := by
  by_cases hx : x = 0
  · subst x
    simp
  rw [complexExpm1Div_of_ne (by exact_mod_cast hx), expm1Div_of_ne hx]
  push_cast
  rfl

/-- The even moment `∫_ℝ t^(2n) up(t) dt`, denoted `c_n` in the paper. -/
noncomputable def momentIntegral (F : BoundedFabius) (n : ℕ) : ℝ :=
  ∫ t : ℝ, t ^ (2 * n) * rvachevUp F t

/--
The half moment denoted `d_n` in the paper.  Its zeroth term is normalized to
`1`; at a successor index it is `(n+1) ∫_0^1 t^n up(t) dt`.
-/
noncomputable def halfMomentIntegral (F : BoundedFabius) : ℕ → ℝ
  | 0 => 1
  | n + 1 =>
      ((n + 1 : ℕ) : ℝ) * ∫ t in (0 : ℝ)..1, t ^ n * rvachevUp F t

/-- The half-moment recursion is normalized to start at `1`, matching
`Arithmetic.halfMoment_zero` on the rational side. -/
@[simp]
theorem halfMomentIntegral_zero (F : BoundedFabius) :
    halfMomentIntegral F 0 = 1 :=
  rfl

/-- The defining equation of a positive-index half moment, unfolded.  The
integral is over `[0,1]` only, which is what makes these *half* moments;
the factor `n + 1` is the paper's normalization. -/
@[simp]
theorem halfMomentIntegral_succ (F : BoundedFabius) (n : ℕ) :
    halfMomentIntegral F (n + 1) =
      ((n + 1 : ℕ) : ℝ) * ∫ t in (0 : ℝ)..1, t ^ n * rvachevUp F t :=
  rfl

/--
The exponential generating function
`1 + x ∫_0^1 up(t) exp(x t) dt` used to define the half moments.
-/
noncomputable def generatingFunction (F : BoundedFabius) (x : ℝ) : ℝ :=
  1 + x * ∫ t in (0 : ℝ)..1, rvachevUp F t * Real.exp (x * t)

/--
The entire complex generating function used in Proposition 2.  Its
restriction to the real axis is `generatingFunction` after the usual cast.
-/
noncomputable def complexGeneratingFunction (F : BoundedFabius) (z : ℂ) : ℂ :=
  1 + z * ∫ t in (0 : ℝ)..1,
    (rvachevUp F t : ℂ) * Complex.exp (z * t)

/-- The complex half-moment generating function restricts to its real version. -/
@[simp]
theorem complexGeneratingFunction_ofReal (F : BoundedFabius) (x : ℝ) :
    complexGeneratingFunction F (x : ℂ) = (generatingFunction F x : ℂ) := by
  unfold complexGeneratingFunction generatingFunction
  push_cast
  congr 1
  congr 1
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro t _ht
  push_cast
  rfl

end Fabius
```

### `UpstreamThueMorseBitSupport.lean`

```lean
import UpstreamArithmetic
import Mathlib.Combinatorics.Colex

/-!
# Binary supports and the Boolean cube of a dyadic block

Mathlib's `Finset.equivBitIndices` is the canonical equivalence between
natural numbers and finite sets of binary positions.  This module gives that
equivalence the project-facing name `bitSupport` and records its inverse,
weight, sign, and bounded-range consequences.

The global dictionary has no artificial bound on a finite set of positions.
Restricting it to subsets of `Finset.range m` gives an equivalence with
`Fin (2 ^ m)` and the corresponding finite-sum reindexing theorem.  All
statements include the zero-level boundary: the empty support encodes zero,
and the Boolean cube at level zero is a singleton.

No second global equivalence is introduced: constructions and proofs use
`Finset.equivBitIndices` itself.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

/-! ## The global binary-support dictionary -/

/-- The finite set of positions at which the binary expansion of `n` has a
one.  This is exactly the forward map of Mathlib's canonical
`Finset.equivBitIndices`. -/
def bitSupport (n : ℕ) : Finset ℕ :=
  Finset.equivBitIndices n

/-- The project-facing bit support is Mathlib's finset of binary indices. -/
theorem bitSupport_eq_toFinset_bitIndices (n : ℕ) :
    bitSupport n = n.bitIndices.toFinset := by
  rfl

/-- Membership in the bit support is exactly the corresponding bit test. -/
theorem mem_bitSupport {n j : ℕ} :
    j ∈ bitSupport n ↔ n.testBit j = true := by
  simp [bitSupport, Finset.equivBitIndices]

/-- Zero has empty binary support. -/
@[simp] theorem bitSupport_zero : bitSupport 0 = ∅ := by
  rw [bitSupport_eq_toFinset_bitIndices]
  simp

private theorem toFinset_map_succ (l : List ℕ) :
    (l.map (· + 1)).toFinset = l.toFinset.image (· + 1) := by
  ext j
  simp

/-- Doubling shifts every bit-support position up by one. -/
theorem bitSupport_two_mul (k : ℕ) :
    bitSupport (2 * k) = (bitSupport k).image (· + 1) := by
  rw [bitSupport_eq_toFinset_bitIndices, bitSupport_eq_toFinset_bitIndices,
    Nat.bitIndices_two_mul, toFinset_map_succ]

/-- Doubling and adding one inserts the low bit and shifts every old
bit-support position up by one. -/
theorem bitSupport_two_mul_add_one (k : ℕ) :
    bitSupport (2 * k + 1) = insert 0 ((bitSupport k).image (· + 1)) := by
  rw [bitSupport_eq_toFinset_bitIndices, bitSupport_eq_toFinset_bitIndices,
    Nat.bitIndices_two_mul_add_one, List.toFinset_cons, toFinset_map_succ]

/-- Summing the two-powers at the bit-support positions reconstructs the
original natural number. -/
@[simp] theorem sum_two_pow_bitSupport (n : ℕ) :
    ∑ j ∈ bitSupport n, 2 ^ j = n := by
  change ∑ j ∈ n.bitIndices.toFinset, 2 ^ j = n
  exact Finset.sum_toFinset_bitIndices_two_pow n

/-- Encoding a finite set by distinct two-powers and then taking its bit
support returns the original set. -/
@[simp] theorem bitSupport_sum_two_pow (T : Finset ℕ) :
    bitSupport (∑ j ∈ T, 2 ^ j) = T := by
  change (∑ j ∈ T, 2 ^ j).bitIndices.toFinset = T
  exact Finset.toFinset_bitIndices_sum_two_pow T

/-- The encoding of finite sets by sums of distinct two-powers is globally
injective. -/
theorem sum_two_pow_injective :
    Function.Injective (fun T : Finset ℕ => ∑ j ∈ T, 2 ^ j) := by
  intro S T h
  have h' := congrArg bitSupport h
  simpa using h'

/-- A sum of distinct two-powers has a one exactly at the positions in the
encoded finite set. -/
theorem testBit_sum_two_pow (T : Finset ℕ) (i : ℕ) :
    (∑ j ∈ T, 2 ^ j).testBit i = decide (i ∈ T) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, ← mem_bitSupport,
    bitSupport_sum_two_pow]

/-- The bit support is empty exactly for the natural number zero. -/
theorem bitSupport_eq_empty_iff (n : ℕ) :
    bitSupport n = ∅ ↔ n = 0 := by
  constructor
  · intro h
    calc
      n = ∑ j ∈ bitSupport n, 2 ^ j := (sum_two_pow_bitSupport n).symm
      _ = 0 := by simp [h]
  · rintro rfl
    exact bitSupport_zero

/-! ## Weight and sign -/

private theorem binaryWeight_bit_of_ne_zero (b : Bool) (n : ℕ) (hn : n ≠ 0) :
    binaryWeight (Nat.bit b n) = binaryWeight n + if b then 1 else 0 := by
  unfold binaryWeight
  rw [Nat.digits_two_eq_bits, Nat.digits_two_eq_bits,
    Nat.bits_append_bit n b (fun h => (hn h).elim)]
  cases b <;> simp [Nat.add_comm]

/-- The number of positions in the bit support is the binary weight.  In
particular, this includes `card (bitSupport 0) = 0`. -/
theorem card_bitSupport (n : ℕ) :
    (bitSupport n).card = binaryWeight n := by
  induction n using Nat.binaryRecFromOne with
  | zero =>
      rw [bitSupport_zero]
      simp [binaryWeight]
  | one =>
      rw [bitSupport_eq_toFinset_bitIndices, Nat.bitIndices_one]
      simp [binaryWeight]
  | bit b n hn ih =>
      have hsucc : Function.Injective (fun j : ℕ => j + 1) := by
        intro a c h
        exact Nat.add_right_cancel h
      cases b with
      | false =>
          rw [binaryWeight_bit_of_ne_zero false n hn]
          rw [show Nat.bit false n = 2 * n by simp [Nat.bit],
            bitSupport_two_mul,
            Finset.card_image_of_injective _ hsucc, ih]
          simp
      | true =>
          rw [binaryWeight_bit_of_ne_zero true n hn]
          have hzero : 0 ∉ (bitSupport n).image (fun j => j + 1) := by
            simp
          rw [show Nat.bit true n = 2 * n + 1 by simp [Nat.bit],
            bitSupport_two_mul_add_one, Finset.card_insert_of_notMem hzero,
            Finset.card_image_of_injective _ hsucc, ih]
          simp

/-- The binary weight of a sum of distinct two-powers is the cardinality of
the set of exponents, with no boundedness hypothesis. -/
theorem binaryWeight_sum_two_pow_eq_card (T : Finset ℕ) :
    binaryWeight (∑ j ∈ T, 2 ^ j) = T.card := by
  rw [← card_bitSupport, bitSupport_sum_two_pow]

/-- Bounded compatibility form of `binaryWeight_sum_two_pow_eq_card`.  The
bound records that the encoded number lies in the dyadic block but is not
needed for the weight identity itself. -/
theorem binaryWeight_sum_two_pow {m : ℕ} {T : Finset ℕ}
    (hT : T ⊆ range m) :
    binaryWeight (∑ j ∈ T, 2 ^ j) = T.card := by
  have _hbounded := hT
  exact binaryWeight_sum_two_pow_eq_card T

/-- The Thue--Morse sign of an encoded finite set is `-1` to the cardinality
of that set. -/
theorem thueMorseSign_sum_two_pow (T : Finset ℕ) :
    thueMorseSign (∑ j ∈ T, 2 ^ j) = (-1 : ℤ) ^ T.card := by
  rw [thueMorseSign, binaryWeight_sum_two_pow_eq_card]

/-! ## Restriction to a dyadic block -/

/-- A sum of distinct two-powers with all exponents below `m` lies strictly
below `2 ^ m`.  This includes the empty-set case at `m = 0`. -/
theorem sum_two_pow_lt_two_pow {m : ℕ} {T : Finset ℕ}
    (hT : T ⊆ range m) :
    ∑ j ∈ T, 2 ^ j < 2 ^ m :=
  Nat.geomSum_lt le_rfl fun _ hj => mem_range.mp (hT hj)

/-- A natural number lies below `2 ^ m` exactly when every position in its
bit support lies below `m`. -/
theorem bitSupport_subset_range_iff_lt_two_pow (n m : ℕ) :
    bitSupport n ⊆ range m ↔ n < 2 ^ m := by
  constructor
  · intro h
    have hsum := sum_two_pow_lt_two_pow (T := bitSupport n) h
    rwa [sum_two_pow_bitSupport] at hsum
  · intro hn j hj
    rw [mem_range]
    have hjpow : 2 ^ j ≤ n :=
      Nat.two_pow_le_of_mem_bitIndices
        (Nat.mem_bitIndices.mpr (mem_bitSupport.mp hj))
    by_contra hjm
    have hmj : m ≤ j := Nat.le_of_not_gt hjm
    have hpow : 2 ^ m ≤ 2 ^ j :=
      Nat.pow_le_pow_right (by omega) hmj
    omega

/-- Setting a fresh leading binary bit raises the digit sum by one:
`binaryWeight (2 ^ b + h) = binaryWeight h + 1` whenever `h < 2 ^ b`.

The support-level reason is that the new bit `b` lies outside the support of
`h`, so the support of the sum is obtained by adjoining one fresh position. -/
theorem binaryWeight_add_pow_two (b h : ℕ) (hh : h < 2 ^ b) :
    binaryWeight (2 ^ b + h) = binaryWeight h + 1 := by
  have hsupp : bitSupport h ⊆ range b :=
    (bitSupport_subset_range_iff_lt_two_pow h b).2 hh
  have hbnot : b ∉ bitSupport h := by
    intro hb
    exact (Nat.lt_irrefl b) (mem_range.mp (hsupp hb))
  have hsum :
      2 ^ b + h = ∑ j ∈ insert b (bitSupport h), 2 ^ j := by
    rw [sum_insert hbnot, sum_two_pow_bitSupport]
  rw [hsum, binaryWeight_sum_two_pow_eq_card,
    card_insert_of_notMem hbnot, card_bitSupport]

/-- The Boolean cube of subsets of `range m` is canonically equivalent to
the dyadic block `Fin (2 ^ m)`.  The forward map sums distinct two-powers;
the inverse map takes bit support. -/
def powersetRangeEquivFin (m : ℕ) :
    ↥((range m).powerset) ≃ Fin (2 ^ m) where
  toFun T :=
    ⟨∑ j ∈ (T : Finset ℕ), 2 ^ j,
      sum_two_pow_lt_two_pow (Finset.mem_powerset.mp T.property)⟩
  invFun n :=
    ⟨bitSupport n,
      Finset.mem_powerset.mpr
        ((bitSupport_subset_range_iff_lt_two_pow (n : ℕ) m).mpr n.isLt)⟩
  left_inv T := by
    apply Subtype.ext
    exact bitSupport_sum_two_pow (T : Finset ℕ)
  right_inv n := by
    apply Fin.ext
    exact sum_two_pow_bitSupport (n : ℕ)

/-- The natural value of `powersetRangeEquivFin` is the sum of the
two-powers indexed by the subset. -/
@[simp] theorem powersetRangeEquivFin_apply_coe
    (m : ℕ) (T : ↥((range m).powerset)) :
    ((powersetRangeEquivFin m T : Fin (2 ^ m)) : ℕ) =
      ∑ j ∈ (T : Finset ℕ), 2 ^ j := by
  rfl

/-- The subset underlying the inverse of `powersetRangeEquivFin` is the bit
support of the dyadic-block index. -/
@[simp] theorem powersetRangeEquivFin_symm_apply_coe
    (m : ℕ) (n : Fin (2 ^ m)) :
    (((powersetRangeEquivFin m).symm n :
        ↥((range m).powerset)) : Finset ℕ) = bitSupport n := by
  rfl

/-- At level zero the bounded Boolean-cube equivalence sends its unique
subset to zero. -/
@[simp] theorem powersetRangeEquivFin_zero_apply
    (T : ↥((range 0).powerset)) :
    ((powersetRangeEquivFin 0 T : Fin (2 ^ 0)) : ℕ) = 0 := by
  rw [powersetRangeEquivFin_apply_coe]
  have hT : (T : Finset ℕ) = ∅ :=
    Finset.subset_empty.mp (Finset.mem_powerset.mp T.property)
  simp [hT]

/-- The image of the bounded powerset under two-power encoding is exactly
the corresponding dyadic range. -/
theorem image_sum_two_pow_powerset_range (m : ℕ) :
    ((range m).powerset).image
        (fun T : Finset ℕ => ∑ j ∈ T, 2 ^ j) =
      range (2 ^ m) := by
  ext n
  simp only [Finset.mem_image, Finset.mem_powerset, Finset.mem_range]
  constructor
  · rintro ⟨T, hT, rfl⟩
    exact sum_two_pow_lt_two_pow hT
  · intro hn
    refine ⟨bitSupport n,
      (bitSupport_subset_range_iff_lt_two_pow n m).mpr hn, ?_⟩
    exact sum_two_pow_bitSupport n

/-- Reindexing a finite sum over subsets of `range m` by distinct
two-powers gives the same sum over the dyadic block `range (2 ^ m)`. -/
theorem sum_powerset_two_pow {M : Type*} [AddCommMonoid M]
    (m : ℕ) (f : ℕ → M) :
    ∑ T ∈ (range m).powerset, f (∑ j ∈ T, 2 ^ j) =
      ∑ n ∈ range (2 ^ m), f n := by
  classical
  apply Finset.sum_bij (fun T _ => ∑ j ∈ T, 2 ^ j)
  · intro T hT
    exact Finset.mem_range.mpr
      (sum_two_pow_lt_two_pow (Finset.mem_powerset.mp hT))
  · intro T _ S _ h
    exact sum_two_pow_injective h
  · intro n hn
    refine ⟨bitSupport n, ?_, ?_⟩
    · exact Finset.mem_powerset.mpr
        ((bitSupport_subset_range_iff_lt_two_pow n m).mpr
          (Finset.mem_range.mp hn))
    · exact sum_two_pow_bitSupport n
  · intro T _
    rfl

end Fabius
```

### `UpstreamAffineDifferenceOrbit.lean`

```lean
import UpstreamThueMorseBitSupport
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Affine-difference iterates and derivative orbits

This module isolates the finite algebra behind two-branch differential
refinement equations.  For

`Δ_{b,c} f (z) = f (b*z+c) - f (b*z-c)`,

the `n`-fold iterate is a signed sum over the Boolean cube.  If an open set is
invariant under both affine branches and `f' = a • Δ_{b,c} f` there, the same
finite orbit gives every iterated derivative, with the exact chain-rule factor
`a^n b^(n choose 2)`.  No global smoothness hypothesis is needed: the
one-step derivative identity bootstraps all differentiability used in the
proof.

The specialization `b = 2`, `c = 1` reindexes the Boolean cube by binary
support and gives the usual finite Thue--Morse affine orbit.  The generic
results are valid for functions into an arbitrary normed space over a
nontrivially normed field.

## Main results

* `affineDifference_iterate_apply` expands every finite iterate over a
  powerset.
* `iteratedDeriv_eq_affineDifference_iterate_on` propagates a one-step
  derivative identity on an invariant open set.
* `affineDifference_iterate_two_one_apply` is the dyadic Thue--Morse form.
-/

set_option autoImplicit false

open Finset Set
open scoped BigOperators

namespace Fabius

section Algebra

variable {𝕜 E : Type*} [CommRing 𝕜] [AddCommGroup E]

/-- The two-branch affine difference
`f (b*z+c) - f (b*z-c)`. -/
def affineDifference (b c : 𝕜) (f : 𝕜 → E) (z : 𝕜) : E :=
  f (b * z + c) - f (b * z - c)

/-- The affine point indexed by a Boolean-cube vertex `T`.

The first sum is the all-positive geometric shift; membership in `T` flips
the corresponding digit, which subtracts twice that power.  In applications
`T` is a subset of `range n`. -/
def affineCubePoint (b c : 𝕜) (n : ℕ) (T : Finset ℕ) (z : 𝕜) : 𝕜 :=
  b ^ n * z + c *
    (∑ k ∈ range n, b ^ k) - 2 * c * (∑ k ∈ T, b ^ k)

private theorem affineCubePoint_succ_notMem
    (b c : 𝕜) (n : ℕ) {T : Finset ℕ} (hT : T ⊆ range n) (z : 𝕜) :
    affineCubePoint b c (n + 1) T z =
      affineCubePoint b c n T (b * z + c) := by
  have hnT : n ∉ T := by
    intro hn
    exact (Nat.lt_irrefl n) (mem_range.mp (hT hn))
  simp only [affineCubePoint, sum_range_succ, pow_succ]
  ring

private theorem affineCubePoint_succ_insert
    (b c : 𝕜) (n : ℕ) {T : Finset ℕ} (hT : T ⊆ range n) (z : 𝕜) :
    affineCubePoint b c (n + 1) (insert n T) z =
      affineCubePoint b c n T (b * z - c) := by
  have hnT : n ∉ T := by
    intro hn
    exact (Nat.lt_irrefl n) (mem_range.mp (hT hn))
  simp only [affineCubePoint, sum_range_succ, sum_insert hnT, pow_succ]
  ring

/-- A constant scalar commutes with every iterate of an affine difference. -/
theorem affineDifference_iterate_const_smul
    [Module 𝕜 E] (b c a : 𝕜) (f : 𝕜 → E) (n : ℕ) :
    (affineDifference b c)^[n] (fun z => a • f z) =
      fun z => a • ((affineDifference b c)^[n] f) z := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      funext z
      simp only [affineDifference, smul_sub]

/-- **Boolean-cube formula for an affine-difference iterate.**  The result is
pure finite algebra: it needs no topology, differentiability, or division. -/
theorem affineDifference_iterate_apply
    (b c : 𝕜) (f : 𝕜 → E) (n : ℕ) (z : 𝕜) :
    ((affineDifference b c)^[n] f) z =
      ∑ T ∈ (range n).powerset,
        ((-1 : ℤ) ^ T.card) • f (affineCubePoint b c n T z) := by
  classical
  induction n generalizing z with
  | zero => simp [affineCubePoint]
  | succ n ih =>
      rw [Function.iterate_succ_apply', affineDifference, ih, ih]
      rw [Finset.range_add_one]
      rw [Finset.powerset_insert (range n) n]
      have hdisj : Disjoint (range n).powerset
          ((range n).powerset.image (insert n)) := by
        rw [Finset.disjoint_left]
        intro T hT hTi
        rcases mem_image.mp hTi with ⟨U, hU, rfl⟩
        have hsub := mem_powerset.mp hT
        have : n ∈ range n := hsub (mem_insert_self n U)
        simp at this
      rw [sum_union hdisj]
      rw [sum_image]
      · rw [← sum_sub_distrib]
        rw [← sum_add_distrib]
        refine sum_congr rfl fun T hT => ?_
        have hsub : T ⊆ range n := mem_powerset.mp hT
        have hnT : n ∉ T := by
          intro hn
          exact (Nat.lt_irrefl n) (mem_range.mp (hsub hn))
        rw [affineCubePoint_succ_notMem b c n hsub z,
          affineCubePoint_succ_insert b c n hsub z,
          card_insert_of_notMem hnT, pow_succ]
        simp only [mul_neg, mul_one, neg_smul, sub_eq_add_neg]
      · intro T hT U hU hEq
        have hnT : n ∉ T := by
          intro hn
          exact (Nat.lt_irrefl n)
            (mem_range.mp ((mem_powerset.mp hT) hn))
        have hnU : n ∉ U := by
          intro hn
          exact (Nat.lt_irrefl n)
            (mem_range.mp ((mem_powerset.mp hU) hn))
        have hErase := congrArg (fun V : Finset ℕ => V.erase n) hEq
        simpa [hnT, hnU] using hErase

end Algebra

section Calculus

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

private theorem hasDerivAt_affineDifference_iterate
    {s : Set 𝕜} {b c : 𝕜}
    (hp : MapsTo (fun z : 𝕜 => b * z + c) s s)
    (hm : MapsTo (fun z : 𝕜 => b * z - c) s s)
    {f f' : 𝕜 → E}
    (hf : ∀ z ∈ s, HasDerivAt f (f' z) z)
    (n : ℕ) {z : 𝕜} (hz : z ∈ s) :
    HasDerivAt ((affineDifference b c)^[n] f)
      (b ^ n • ((affineDifference b c)^[n] f') z) z := by
  induction n generalizing z with
  | zero => simpa using hf z hz
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hplus := (ih (hp hz)).scomp z
        (((hasDerivAt_id z).const_mul b).add_const c)
      have hminus := (ih (hm hz)).scomp z
        (((hasDerivAt_id z).const_mul b).sub_const c)
      have hraw := hplus.sub hminus
      have hfun : affineDifference b c ((affineDifference b c)^[n] f) =
          (((affineDifference b c)^[n] f) ∘ fun x => b * id x + c) -
            (((affineDifference b c)^[n] f) ∘ fun x => b * id x - c) := by
        funext y
        rfl
      rw [hfun]
      convert hraw using 1
      rw [Function.iterate_succ_apply', affineDifference, pow_succ, smul_sub]
      simp only [smul_smul, mul_one]
      rw [mul_comm (b ^ n) b]

/-- **All-order affine-difference derivative propagation on an open invariant
domain.**  If both affine branches preserve `s` and
`f' = a • (f(bz+c)-f(bz-c))` on `s`, then every derivative is the matching
finite operator iterate with coefficient `a^n b^(n choose 2)`.

The one-step `HasDerivAt` hypothesis supplies all regularity needed by the
induction; no separate `ContDiff` assumption is imposed. -/
theorem iteratedDeriv_eq_affineDifference_iterate_on
    {s : Set 𝕜} (hs : IsOpen s) {a b c : 𝕜}
    (hp : MapsTo (fun z : 𝕜 => b * z + c) s s)
    (hm : MapsTo (fun z : 𝕜 => b * z - c) s s)
    (f : 𝕜 → E)
    (hD : ∀ z ∈ s,
      HasDerivAt f (a • affineDifference b c f z) z)
    (n : ℕ) {z : 𝕜} (hz : z ∈ s) :
    iteratedDeriv n f z =
      (a ^ n * b ^ n.choose 2) •
        ((affineDifference b c)^[n] f) z := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have heq : iteratedDeriv n f =ᶠ[nhds z]
          (a ^ n * b ^ n.choose 2) •
            ((affineDifference b c)^[n] f) := by
        filter_upwards [hs.mem_nhds hz] with y hy
        simpa only [Pi.smul_apply] using ih hy
      rw [heq.deriv_eq]
      have horbit := hasDerivAt_affineDifference_iterate hp hm hD n hz
      have hscaled := horbit.const_smul (a ^ n * b ^ n.choose 2)
      rw [affineDifference_iterate_const_smul,
        ← Function.iterate_succ_apply] at hscaled
      have hchoose : (n + 1).choose 2 = n.choose 2 + n := by
        rw [Nat.choose_succ_succ]
        simp [add_comm]
      rw [hscaled.deriv, hchoose, pow_succ, pow_add]
      simp only [smul_smul]
      congr 1
      ring

/-- Global form of `iteratedDeriv_eq_affineDifference_iterate_on`. -/
theorem iteratedDeriv_eq_affineDifference_iterate
    {a b c : 𝕜} (f : 𝕜 → E)
    (hD : ∀ z : 𝕜,
      HasDerivAt f (a • affineDifference b c f z) z)
    (n : ℕ) (z : 𝕜) :
    iteratedDeriv n f z =
      (a ^ n * b ^ n.choose 2) •
        ((affineDifference b c)^[n] f) z := by
  exact iteratedDeriv_eq_affineDifference_iterate_on isOpen_univ
    (mapsTo_univ _ _) (mapsTo_univ _ _) f (fun y _ => hD y) n (mem_univ z)

end Calculus

section Dyadic

variable {𝕜 E : Type*} [CommRing 𝕜] [AddCommGroup E]

/-- **Dyadic Thue--Morse form of the affine-difference iterate.**  The shift
is evaluated in the coefficient ring, so there is no truncated natural
subtraction in `2^n - 1 - 2j`. -/
theorem affineDifference_iterate_two_one_apply
    (f : 𝕜 → E) (n : ℕ) (z : 𝕜) :
    ((affineDifference (2 : 𝕜) 1)^[n] f) z =
      ∑ j ∈ range (2 ^ n), thueMorseSign j •
        f ((2 : 𝕜) ^ n * z + (2 : 𝕜) ^ n - 1 - 2 * (j : 𝕜)) := by
  classical
  rw [affineDifference_iterate_apply]
  rw [← sum_powerset_two_pow n (fun j => thueMorseSign j •
    f ((2 : 𝕜) ^ n * z + (2 : 𝕜) ^ n - 1 - 2 * (j : 𝕜)))]
  refine sum_congr rfl fun T hT => ?_
  rw [thueMorseSign_sum_two_pow]
  congr 1
  unfold affineCubePoint
  have hgeom : ∑ k ∈ range n, (2 : 𝕜) ^ k = (2 : 𝕜) ^ n - 1 := by
    have h := geom_sum_mul (2 : 𝕜) n
    norm_num at h
    exact h
  have hcast :
      ((∑ k ∈ T, 2 ^ k : ℕ) : 𝕜) = ∑ k ∈ T, (2 : 𝕜) ^ k := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert k T hk _ => simp [hk]
  rw [hgeom]
  rw [hcast]
  ring_nf

end Dyadic

end Fabius
```

### `UpstreamDifferential.lean`

```lean
import UpstreamBasic
import UpstreamAffineDifferenceOrbit
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Differential identities for the Fabius and Rvachev functions

This module derives the global differential equation for Rvachev's compactly
supported `up` function from the bounded Fabius derivative identity and
left-tail vanishing alone.  The proof handles the fold point at zero by gluing
the two one-sided derivatives, then bootstraps the differential equation to
smoothness of every finite order.
It also records the closed constant-tail forms of the Fabius derivative and
the exact midpoint derivative, so endpoint arguments do not need to reopen
the global folded formula.  The generic affine-difference orbit calculus is
then specialized to express every derivative of `up` as a finite
Thue--Morse-signed affine orbit, globally on the real line.
-/

set_option autoImplicit false

open scoped ContDiff
open Set

namespace Fabius

set_option linter.unusedVariables false in
/-- Backwards-compatible form of `rvachevUp_even` for an `IsFabius` candidate. -/
theorem rvachev_even (F : BoundedFabius) (hF : IsFabius F) :
    Function.Even (rvachevUp F) :=
  rvachevUp_even F

/-- Folding preserves the pointwise range `[0,1]` of a bounded candidate. -/
theorem rvachevUp_mem_unitInterval (F : BoundedFabius) (x : ℝ) :
    rvachevUp F x ∈ Icc (0 : ℝ) 1 :=
  ⟨rvachevUp_nonneg F x, rvachevUp_le_one F x⟩

/-- Rvachev's function vanishes at the right endpoint of its support. -/
theorem rvachevUp_one (F : BoundedFabius) (hF : IsFabius F) :
    rvachevUp F 1 = 0 :=
  rvachevUp_eq_zero_of_one_le F hF le_rfl

/-- Rvachev's function vanishes at the left endpoint of its support. -/
theorem rvachevUp_neg_one (F : BoundedFabius) (hF : IsFabius F) :
    rvachevUp F (-1) = 0 :=
  rvachevUp_eq_zero_of_le_neg_one F hF le_rfl

/-- The bounded Fabius function has a vanishing derivative at the right
endpoint of the unit interval, where it attains its global maximum. -/
theorem fabius_hasDerivAt_one (F : BoundedFabius) (hF : IsFabius F) :
    HasDerivAt (fabiusReal F) (0 : ℝ) (1 : ℝ) := by
  have hmax : IsMaxOn (fabiusReal F) Set.univ 1 := by
    intro y _hy
    rw [hF.one_of_one_le 1 le_rfl]
    exact fabiusReal_le_one F y
  have hderiv : deriv (fabiusReal F) 1 = 0 :=
    (hmax.isLocalMax Filter.univ_mem).deriv_eq_zero
  have hd := (hF.contDiff.differentiable (by simp) 1).hasDerivAt
  rwa [hderiv] at hd

private lemma fabius_hasDerivAt_secondHalf_aux (F : BoundedFabius)
    (hF : IsFabius F) {t : ℝ} (htlow : 1 / 2 < t) (hthigh : t < 1) :
    HasDerivAt (fabiusReal F) (2 * fabiusReal F (2 - 2 * t)) t := by
  have harg : 1 - t ∈ Icc (0 : ℝ) (1 / 2) := by
    constructor <;> linarith
  have hd := hF.hasDerivAt (1 - t) harg
  have hdpoint : HasDerivAt (fabiusReal F)
      (2 * fabiusReal F (2 * (1 - t))) ((1 : ℝ) - t) := by
    simpa using hd
  have hcomp := hdpoint.comp_const_sub 1 t
  have hrhs : HasDerivAt (fun y : ℝ => 1 - fabiusReal F (1 - y))
      (2 * fabiusReal F (2 - 2 * t)) t := by
    have hargEq : 2 * (1 - t) = (2 - 2 * t : ℝ) := by ring
    rw [hargEq] at hcomp
    simpa only [neg_neg] using hcomp.const_sub (1 : ℝ)
  apply hrhs.congr_of_eventuallyEq
  filter_upwards with y
  have hs := hF.symmetry_all (1 - y)
  convert hs using 1
  ring_nf

/-- To the left of the unit interval the bounded Fabius function is locally
constant, hence has vanishing derivative. -/
theorem fabius_hasDerivAt_of_neg (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx : x < 0) : HasDerivAt (fabiusReal F) 0 x := by
  apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hx] with y hy
  exact hF.zero_of_nonpos y (le_of_lt hy)

/-- To the right of the unit interval the bounded Fabius function is locally
constant, hence has vanishing derivative. -/
theorem fabius_hasDerivAt_of_one_lt (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx : 1 < x) : HasDerivAt (fabiusReal F) 0 x := by
  apply (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact hF.one_of_one_le y (le_of_lt hy)

/--
The bounded Fabius function satisfies one differential equation on all of `ℝ`:
`F'(x) = 2 up(2x - 1)`.

On `[0, 1/2]` this is the defining equation `F'(x) = 2 F(2x)`, on `[1/2, 1]` it
is its reflection `F'(x) = 2 F(2 - 2x)`, and outside `[0, 1]` both sides
vanish.  Folding the three cases into a single identity removes the case
analysis from every later derivative computation.
-/
theorem fabius_hasDerivAt (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    HasDerivAt (fabiusReal F) (2 * rvachevUp F (2 * x - 1)) x := by
  by_cases hx0 : 0 ≤ x
  · by_cases hxhalf : x ≤ 1 / 2
    · have h := hF.hasDerivAt x ⟨hx0, hxhalf⟩
      rwa [rvachevUp_of_nonpos F (show 2 * x - 1 ≤ 0 by linarith),
        show 2 * x - 1 + 1 = 2 * x by ring]
    · have hhalf : 1 / 2 < x := lt_of_not_ge hxhalf
      rcases lt_trichotomy x 1 with hx1 | hx1 | hx1
      · have h := fabius_hasDerivAt_secondHalf_aux F hF hhalf hx1
        rwa [rvachevUp_of_pos F (show (0 : ℝ) < 2 * x - 1 by linarith),
          show 1 - (2 * x - 1) = 2 - 2 * x by ring]
      · subst hx1
        rw [show 2 * (1 : ℝ) - 1 = 1 by norm_num, rvachevUp_one F hF, mul_zero]
        exact fabius_hasDerivAt_one F hF
      · rw [rvachevUp_eq_zero_of_one_le F hF (by linarith), mul_zero]
        exact fabius_hasDerivAt_of_one_lt F hF hx1
  · have hx : x < 0 := lt_of_not_ge hx0
    rw [rvachevUp_eq_zero_of_le_neg_one F hF (by linarith), mul_zero]
    exact fabius_hasDerivAt_of_neg F hF hx

/-- **`y ↦ F((y+1)/2)` is a global antiderivative of the up-function.**
This is the folded derivative identity `F'(x) = 2·up(2x-1)` of
`fabius_hasDerivAt` composed with the affine substitution: the factor
`2` is eaten by the inner derivative `1/2`, and the argument
`2·((y+1)/2) - 1` collapses to `y`. -/
theorem hasDerivAt_fabiusReal_half_shift (F : BoundedFabius)
    (hF : IsFabius F) (y : ℝ) :
    HasDerivAt (fun z : ℝ => fabiusReal F ((z + 1) / 2)) (rvachevUp F y) y := by
  have hinner : HasDerivAt (fun z : ℝ => (z + 1) / 2) (2⁻¹) y := by
    simpa using ((hasDerivAt_id y).add_const (1 : ℝ)).div_const 2
  have h := (fabius_hasDerivAt F hF ((y + 1) / 2)).comp y hinner
  have harg : 2 * ((y + 1) / 2) - 1 = y := by ring
  rw [harg] at h
  have hval : 2 * rvachevUp F y * 2⁻¹ = rvachevUp F y := by ring
  rw [hval] at h
  exact h

/-- On the whole closed left tail `(-∞, 0]`, including the gluing point, the
bounded Fabius function has derivative zero. -/
theorem fabius_hasDerivAt_of_nonpos (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx : x ≤ 0) : HasDerivAt (fabiusReal F) 0 x := by
  have h := fabius_hasDerivAt F hF x
  have hup : rvachevUp F (2 * x - 1) = 0 :=
    rvachevUp_eq_zero_of_le_neg_one F hF (by linarith)
  simpa [hup] using h

/-- On the whole closed right tail `[1, ∞)`, including the gluing point, the
bounded Fabius function has derivative zero. -/
theorem fabius_hasDerivAt_of_one_le (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx : 1 ≤ x) : HasDerivAt (fabiusReal F) 0 x := by
  have h := fabius_hasDerivAt F hF x
  have hup : rvachevUp F (2 * x - 1) = 0 :=
    rvachevUp_eq_zero_of_one_le F hF (by linarith)
  simpa [hup] using h

/-- Exact derivative at the left endpoint of the unit interval. -/
theorem fabius_hasDerivAt_zero (F : BoundedFabius) (hF : IsFabius F) :
    HasDerivAt (fabiusReal F) 0 0 :=
  fabius_hasDerivAt_of_nonpos F hF le_rfl

/-- The derivative reaches its exact maximum `2` at the midpoint. -/
theorem fabius_hasDerivAt_half (F : BoundedFabius) (hF : IsFabius F) :
    HasDerivAt (fabiusReal F) 2 (1 / 2) := by
  have h := fabius_hasDerivAt F hF (1 / 2)
  have harg : 2 * (1 / 2 : ℝ) - 1 = 0 := by norm_num
  simpa [harg, rvachevUp_zero F hF] using h

/-- Reflected form of the defining differential equation on the whole ray
`[1/2, ∞)`.  Beyond `1`, both the derivative and the reflected value vanish. -/
theorem fabius_hasDerivAt_reflected_of_half_le
    (F : BoundedFabius) (hF : IsFabius F) {t : ℝ} (ht : 1 / 2 ≤ t) :
    HasDerivAt (fabiusReal F) (2 * fabiusReal F (2 - 2 * t)) t := by
  have h := fabius_hasDerivAt F hF t
  have hup : rvachevUp F (2 * t - 1) = fabiusReal F (2 - 2 * t) := by
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ 2 * t - 1 by linarith) with h0 | h0
    · rw [← h0, rvachevUp_zero F hF, show (2 : ℝ) - 2 * t = 1 by linarith]
      exact (hF.one_of_one_le 1 le_rfl).symm
    · rw [rvachevUp_of_pos F h0]
      congr 1
      ring
  rwa [hup] at h

set_option linter.unusedVariables false in
/--
Closed-unit-interval compatibility form of
`fabius_hasDerivAt_reflected_of_half_le`.  The hypothesis `hthigh` is retained
for API compatibility.
-/
theorem fabius_hasDerivAt_secondHalf (F : BoundedFabius) (hF : IsFabius F)
    {t : ℝ} (htlow : 1 / 2 ≤ t) (hthigh : t ≤ 1) :
    HasDerivAt (fabiusReal F) (2 * fabiusReal F (2 - 2 * t)) t := by
  exact fabius_hasDerivAt_reflected_of_half_le F hF htlow

/-- Closed form for the derivative of the bounded Fabius function. -/
theorem deriv_fabiusReal (F : BoundedFabius) (hF : IsFabius F) :
    deriv (fabiusReal F) = fun x : ℝ => 2 * rvachevUp F (2 * x - 1) := by
  funext x
  exact (fabius_hasDerivAt F hF x).deriv

/-- The first derivative inherits the reflection symmetry of the Rvachev
bump: reflecting an argument across the midpoint leaves the derivative
unchanged.  The identity is global, including both constant exterior tails. -/
theorem deriv_fabiusReal_one_sub
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    deriv (fabiusReal F) (1 - x) = deriv (fabiusReal F) x := by
  rw [(fabius_hasDerivAt F hF (1 - x)).deriv,
    (fabius_hasDerivAt F hF x).deriv,
    show 2 * (1 - x) - 1 = -(2 * x - 1) by ring,
    rvachevUp_even F (2 * x - 1)]

/-- The bounded Fabius function is differentiable on all of `ℝ`. -/
theorem fabius_differentiable (F : BoundedFabius) (hF : IsFabius F) :
    Differentiable ℝ (fabiusReal F) :=
  fun x => (fabius_hasDerivAt F hF x).differentiableAt

private lemma rvachevUp_left_hasDerivAt_of_hasDerivAt (F : BoundedFabius)
    (hderiv : ∀ x : ℝ,
      HasDerivAt (fabiusReal F) (2 * rvachevUp F (2 * x - 1)) x)
    {x : ℝ} :
    HasDerivAt (fun y : ℝ => fabiusReal F (y + 1))
      (2 * rvachevUp F (2 * x + 1)) x := by
  have h := (hderiv (x + 1)).comp_add_const x 1
  rw [show 2 * (x + 1) - 1 = 2 * x + 1 by ring] at h
  exact h

private lemma rvachevUp_hasDerivAt_of_neg_of_hasDerivAt (F : BoundedFabius)
    (hderiv : ∀ x : ℝ,
      HasDerivAt (fabiusReal F) (2 * rvachevUp F (2 * x - 1)) x)
    {x : ℝ} (hx : x < 0) :
    HasDerivAt (rvachevUp F) (2 * rvachevUp F (2 * x + 1)) x := by
  have hl := rvachevUp_left_hasDerivAt_of_hasDerivAt F hderiv (x := x)
  apply hl.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hx] with y hy
  have hyle : y ≤ 0 := le_of_lt hy
  simp [rvachevUp, hyle]

/-- Rvachev's refinement equation follows from the global bounded-Fabius
derivative identity together with vanishing on the left tail; no smoothness,
symmetry, or fixed-point information is needed. -/
theorem rvachevUp_hasDerivAt_of_fabiusReal_hasDerivAt
    (F : BoundedFabius)
    (hzero : ∀ x : ℝ, x ≤ 0 → fabiusReal F x = 0)
    (hderiv : ∀ x : ℝ,
      HasDerivAt (fabiusReal F) (2 * rvachevUp F (2 * x - 1)) x)
    (x : ℝ) :
    HasDerivAt (rvachevUp F)
      (2 * (rvachevUp F (2 * x + 1) - rvachevUp F (2 * x - 1))) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hmain := rvachevUp_hasDerivAt_of_neg_of_hasDerivAt F hderiv hx
    have hsecond : rvachevUp F (2 * x - 1) = 0 := by
      rw [rvachevUp, if_pos (by linarith), hzero _ (by linarith)]
    rw [hsecond]
    simpa using hmain
  · have hupOne : rvachevUp F 1 = 0 := by
      rw [rvachevUp, if_neg (by norm_num), show (1 : ℝ) - 1 = 0 by norm_num]
      exact hzero 0 le_rfl
    have hupNegOne : rvachevUp F (-1) = 0 := by
      rw [rvachevUp, if_pos (by norm_num), show (-1 : ℝ) + 1 = 0 by norm_num]
      exact hzero 0 le_rfl
    have hl0 := rvachevUp_left_hasDerivAt_of_hasDerivAt F hderiv (x := 0)
    have hcoef : 2 * rvachevUp F (2 * (0 : ℝ) + 1) = 0 := by
      norm_num [hupOne]
    rw [hcoef] at hl0
    have hl : HasDerivWithinAt (rvachevUp F) 0 (Iic (0 : ℝ)) 0 := by
      have h : HasDerivWithinAt (fun y : ℝ => fabiusReal F (y + 1)) 0
          (Iic (0 : ℝ)) 0 := hl0.hasDerivWithinAt
      refine h.congr_of_mem ?_ (by simp)
      intro y hy
      change y ≤ 0 at hy
      rw [rvachevUp, if_pos hy]
    have hone : HasDerivAt (fabiusReal F) 0 1 := by
      have h := hderiv 1
      rw [show 2 * (1 : ℝ) - 1 = 1 by norm_num, hupOne, mul_zero] at h
      exact h
    have hone' : HasDerivAt (fabiusReal F) 0 ((1 : ℝ) - 0) := by simpa using hone
    have hr0 := hone'.comp_const_sub 1 (0 : ℝ)
    have hr : HasDerivWithinAt (rvachevUp F) 0 (Ici (0 : ℝ)) 0 := by
      have h : HasDerivWithinAt (fun y : ℝ => fabiusReal F (1 - y)) 0
          (Ici (0 : ℝ)) 0 := by simpa using hr0.hasDerivWithinAt
      refine h.congr_of_mem ?_ (by simp)
      intro y hy
      by_cases hy0 : y = 0
      · subst y
        simp [rvachevUp]
      · have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
        simp [rvachevUp, not_le.mpr hypos]
    have hu := hl.union hr
    rw [Iic_union_Ici] at hu
    simpa [hupOne, hupNegOne] using hu
  · have hneg := rvachevUp_hasDerivAt_of_neg_of_hasDerivAt F hderiv
      (show -x < 0 by linarith)
    have hneg' : HasDerivAt (rvachevUp F)
        (2 * rvachevUp F (2 * (-x) + 1)) ((0 : ℝ) - x) := by simpa using hneg
    have hcomp := hneg'.comp_const_sub 0 x
    have hup : HasDerivAt (rvachevUp F)
        (-(2 * rvachevUp F (2 * (-x) + 1))) x := by
      apply hcomp.congr_of_eventuallyEq
      filter_upwards with y
      simpa using (rvachevUp_even F y).symm
    convert hup using 1
    · have hfar : rvachevUp F (2 * x + 1) = 0 := by
        rw [rvachevUp, if_neg (by linarith), hzero _ (by linarith)]
      rw [hfar]
      have heven := rvachevUp_even F (2 * x - 1)
      have heq : rvachevUp F (2 * (-x) + 1) = rvachevUp F (2 * x - 1) := by
        convert heven using 1
        ring_nf
      rw [heq]
      ring

/-- The differential equation defining Rvachev's function. -/
theorem rvachev_hasDerivAt (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    HasDerivAt (rvachevUp F)
      (2 * (rvachevUp F (2 * x + 1) - rvachevUp F (2 * x - 1))) x :=
  rvachevUp_hasDerivAt_of_fabiusReal_hasDerivAt F hF.zero_of_nonpos
    (fabius_hasDerivAt F hF) x

/-- Pointwise derivative form of Rvachev's differential equation. -/
theorem deriv_rvachevUp (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    deriv (rvachevUp F) x =
      2 * (rvachevUp F (2 * x + 1) - rvachevUp F (2 * x - 1)) :=
  (rvachev_hasDerivAt F hF x).deriv

/-- **Every derivative of Rvachev's function is a finite Thue--Morse
affine orbit.**  Unlike the rescaled-global-Fabius formula, this identity is
valid at every real `x` and is expressed entirely in terms of `rvachevUp`.

It is the `a = b = 2`, `c = 1` specialization of the generic open-domain
affine-difference calculus in `AffineDifferenceOrbit`. -/
theorem iteratedDeriv_rvachevUp_eq_thueMorse_sum
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (rvachevUp F) x =
      (2 : ℝ) ^ (n + 1).choose 2 *
        ∑ j ∈ Finset.range (2 ^ n), (thueMorseSign j : ℝ) *
          rvachevUp F
            ((2 : ℝ) ^ n * x + (2 : ℝ) ^ n - 1 - 2 * (j : ℝ)) := by
  have h := iteratedDeriv_eq_affineDifference_iterate
    (a := (2 : ℝ)) (b := (2 : ℝ)) (c := (1 : ℝ)) (rvachevUp F)
    (fun y => by
      simpa only [affineDifference, smul_eq_mul] using
        rvachev_hasDerivAt F hF y) n x
  rw [affineDifference_iterate_two_one_apply] at h
  have hchoose : (n + 1).choose 2 = n.choose 2 + n := by
    rw [Nat.choose_succ_succ]
    simp [add_comm]
  simpa only [smul_eq_mul, zsmul_eq_mul, hchoose, pow_add, mul_comm] using h

/-- Any solution of Rvachev's dyadic differential refinement equation is smooth.

This isolates the regularity bootstrap from the construction and from the
particular folded representation of the canonical solution. -/
theorem contDiff_of_hasDerivAt_dyadic_refinement (u : ℝ → ℝ)
    (hu : ∀ x : ℝ, HasDerivAt u (2 * (u (2 * x + 1) - u (2 * x - 1))) x) :
    ContDiff ℝ ∞ u := by
  have hdifferentiable : Differentiable ℝ u :=
    fun x => (hu x).differentiableAt
  apply contDiff_infty.mpr
  intro n
  induction n with
  | zero => exact contDiff_zero.mpr hdifferentiable.continuous
  | succ n ih =>
      rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp,
        contDiff_succ_iff_deriv]
      refine ⟨hdifferentiable, by simp, ?_⟩
      have hderiv : deriv u = fun x : ℝ =>
          2 * (u (2 * x + 1) - u (2 * x - 1)) := by
        funext x
        exact (hu x).deriv
      rw [hderiv]
      have hplus : ContDiff ℝ n (fun x : ℝ => u (2 * x + 1)) :=
        ih.comp ((contDiff_const.mul contDiff_id).add contDiff_const)
      have hminus : ContDiff ℝ n (fun x : ℝ => u (2 * x - 1)) :=
        ih.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
      exact contDiff_const.mul (hplus.sub hminus)

/-- Rvachev's function is smooth. -/
theorem rvachev_contDiff (F : BoundedFabius) (hF : IsFabius F) :
    ContDiff ℝ ∞ (rvachevUp F) :=
  contDiff_of_hasDerivAt_dyadic_refinement _ (rvachev_hasDerivAt F hF)

end Fabius
```

### `UpstreamDyadicCorrectness.lean`

```lean
import UpstreamArithmetic
import Mathlib.Tactic.FieldSimp

/-!
# Correctness infrastructure for the executable dyadic evaluator

This module discharges the structural part of the evaluator proof.  Once the
single-step dyadic recurrence from Proposition 10 is established, strong
induction proves that the terminating bit recursion agrees with the exact
closed formula at every point of the unit dyadic grid.  The representation API
also shows that neither a surplus inverse-power table bound nor a different
dyadic numerator/exponent presentation changes the computed value.
-/

set_option autoImplicit false

namespace Fabius

/-- Equation (32) vanishes at numerator `0`, where its sum over `Fin a` is
empty.  Used in `DyadicClosedForm`, `DyadicAnalytic`, and `GlobalDyadic`. -/
@[simp]
theorem fabiusDyadic_arg_zero (n : ℕ) : fabiusDyadic n 0 = 0 := by
  simp [fabiusDyadic]

/-! ## Inverse-power table -/

/-- The normalized recurrence used to append the next inverse-power value. -/
lemma halfMomentFabiusValue_succ (n : ℕ) :
    halfMomentFabiusValue (n + 1) =
      (∑ k : Fin (n + 1),
          halfMomentFabiusValue k.val /
            ((2 : ℚ) ^ ((n + 1).choose 2 - k.val.choose 2) *
              ((n + 1 - k.val + 1).factorial : ℚ))) /
        ((2 : ℚ) ^ (n + 1) - 1) := by
  rw [halfMomentFabiusValue, halfMoment_succ]
  simp only [halfMomentFabiusValue]
  have hpow : (1 : ℚ) < 2 ^ (n + 1) := by
    exact one_lt_pow₀ (by norm_num) (Nat.succ_ne_zero n)
  have hden : (2 : ℚ) ^ (n + 1) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hpow)
  field_simp [hden]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k.val ≤ n + 1 := by omega
  have hchoose_le : k.val.choose 2 ≤ (n + 1).choose 2 := by
    exact Nat.choose_le_choose 2 hk_le
  have hsub : n + 1 - k.val + 1 = n + 2 - k.val := by omega
  have hpow_mul :
      (2 : ℚ) ^ k.val.choose 2 *
          2 ^ ((n + 1).choose 2 - k.val.choose 2) =
        2 ^ (n + 1).choose 2 := by
    rw [← pow_add, Nat.add_sub_of_le hchoose_le]
  have hchoose_fac := Nat.choose_mul_factorial_mul_factorial
    (n := n + 2) (k := k.val) (by omega : k.val ≤ n + 2)
  have hcoef :
      ((Nat.choose (n + 2) k.val : ℕ) : ℚ) * (k.val.factorial : ℚ) *
          ((n + 2 - k.val).factorial : ℚ) =
        (n + 2 : ℚ) * ((n + 1).factorial : ℚ) := by
    exact_mod_cast (show
      Nat.choose (n + 2) k.val * k.val.factorial * (n + 2 - k.val).factorial =
        (n + 2) * (n + 1).factorial by
      simpa [Nat.factorial_succ] using hchoose_fac)
  rw [hsub]
  field_simp
  calc
    _ = halfMoment k.val *
          (((Nat.choose (n + 2) k.val : ℕ) : ℚ) * (k.val.factorial : ℚ) *
            ((n + 2 - k.val).factorial : ℚ)) *
          ((2 : ℚ) ^ k.val.choose 2 *
            2 ^ ((n + 1).choose 2 - k.val.choose 2)) := by ring
    _ = halfMoment k.val * ((n + 2 : ℚ) * ((n + 1).factorial : ℚ)) *
          (2 : ℚ) ^ (n + 1).choose 2 := by rw [hcoef, hpow_mul]
    _ = _ := by
      push_cast
      ring

/-- The table for exponent `n` holds exactly `n + 1` entries, one for each
index from `0` to `n`. -/
@[simp]
lemma fabiusInversePowTwoTable_size (n : ℕ) :
    (fabiusInversePowTwoTable n).size = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [fabiusInversePowTwoTable, ih]

/-! ## Horner evaluation -/

/-- General loop invariant for the Horner evaluator. -/
lemma fabiusTaylorHorner_go_eq_sum
    (values : Array ℚ)
    (hzero : fabiusInversePowTwoTableValue values 0 = 1)
    (offset : ℚ) (m d : ℕ) :
    fabiusTaylorHorner.go values (d + m) offset m =
      ∑ k ∈ Finset.range (m + 1),
        (2 : ℚ) ^ (k * d + (k + 1).choose 2) *
          fabiusInversePowTwoTableValue values (m - k) * offset ^ k *
          (d.factorial : ℚ) / ((d + k).factorial : ℚ) := by
  induction m generalizing d with
  | zero =>
      simp [fabiusTaylorHorner.go.eq_1, hzero]
      rw [div_self (by positivity : (d.factorial : ℚ) ≠ 0)]
  | succ m ih =>
      rw [fabiusTaylorHorner.go.eq_2]
      have hnat : d + (m + 1) - m = d + 1 := by omega
      have hrat : ((d + (m + 1) : ℕ) : ℚ) - (m : ℚ) = (d + 1 : ℕ) := by
        push_cast
        ring
      have horder : d + (m + 1) = (d + 1) + m := by omega
      rw [hnat, hrat, horder, ih (d + 1)]
      have hdfact : (d.factorial : ℚ) ≠ 0 := by positivity
      conv_rhs => rw [Finset.sum_range_succ']
      norm_num [hdfact]
      rw [Finset.mul_sum, add_comm]
      apply congrArg₂ (· + ·) ?_ rfl
      apply Finset.sum_congr rfl
      intro k hk
      have hk_le : k ≤ m := by simpa using hk
      have hsub : m + 1 - (k + 1) = m - k := by omega
      have hchoose : (k + 1 + 1).choose 2 = (k + 1).choose 2 + (k + 1) := by
        rw [show 2 = 1 + 1 by omega, Nat.choose_succ_succ]
        simp [Nat.add_comm]
      have hexponent :
          d + 1 + (k * (d + 1) + (k + 1).choose 2) =
            (k + 1) * d + (k + 1 + 1).choose 2 := by
        rw [hchoose]
        ring
      have hfactorial :
          ((d + 1).factorial : ℚ) = (d + 1 : ℚ) * (d.factorial : ℚ) := by
        simp [Nat.factorial_succ]
      have hdenIndex : d + (k + 1) = d + 1 + k := by omega
      have hpowers :
          (2 : ℚ) ^ (d + 1) * 2 ^ (k * (d + 1) + (k + 1).choose 2) =
            2 ^ ((k + 1) * d + (k + 1 + 1).choose 2) := by
        rw [← pow_add, hexponent]
      have hoffset : offset * offset ^ k = offset ^ (k + 1) := by
        rw [pow_succ']
      field_simp
      calc
        _ = ((2 : ℚ) ^ (d + 1) *
              2 ^ (k * (d + 1) + (k + 1).choose 2)) *
              (offset * offset ^ k) *
              fabiusInversePowTwoTableValue values (m - k) *
              ((d + 1).factorial : ℚ) *
              ((d + (k + 1)).factorial : ℚ) := by ring
        _ = (2 : ℚ) ^ ((k + 1) * d + (k + 1 + 1).choose 2) *
              offset ^ (k + 1) *
              fabiusInversePowTwoTableValue values (m - k) *
              ((d + 1 : ℕ) : ℚ) * (d.factorial : ℚ) *
              ((d + 1 + k).factorial : ℚ) := by
          rw [hpowers, hoffset, hfactorial, hdenIndex]
          push_cast
          ring
        _ = _ := by
          push_cast
          ring

/-! ## Independence of dyadic representation -/

/-- Appending the next entry does not disturb the earlier ones: for `k ≤ n`
the optional lookups at index `k` in the tables for `n + 1` and `n` agree. -/
lemma fabiusInversePowTwoTable_succ_get (n k : ℕ) (hk : k ≤ n) :
    (fabiusInversePowTwoTable (n + 1))[k]? =
      (fabiusInversePowTwoTable n)[k]? := by
  have hne : k ≠ n + 1 := by omega
  rw [fabiusInversePowTwoTable]
  simp [Array.getElem?_push, fabiusInversePowTwoTable_size, hk, hne]

/-- Appending one entry to the inverse-power table leaves each Horner loop
step unchanged, provided the requested `order` fits in the smaller table
(`order ≤ n`) and the loop counter satisfies `m ≤ order`. -/
lemma fabiusTaylorHorner_go_table_succ (n order m : ℕ) (horder : order ≤ n)
    (hm : m ≤ order) (offset : ℚ) :
    fabiusTaylorHorner.go (fabiusInversePowTwoTable (n + 1)) order offset m =
      fabiusTaylorHorner.go (fabiusInversePowTwoTable n) order offset m := by
  induction m with
  | zero => rw [fabiusTaylorHorner.go.eq_1, fabiusTaylorHorner.go.eq_1]
  | succ m ih =>
      rw [fabiusTaylorHorner.go.eq_2, fabiusTaylorHorner.go.eq_2, ih (by omega)]
      unfold fabiusInversePowTwoTableValue
      rw [fabiusInversePowTwoTable_succ_get n (m + 1) (by omega)]

/-- Appending one entry to the inverse-power table leaves the whole Taylor
polynomial unchanged, provided the requested `order` already fits in the
smaller table. -/
lemma fabiusTaylorHorner_table_succ (n order : ℕ) (horder : order ≤ n)
    (offset : ℚ) :
    fabiusTaylorHorner (fabiusInversePowTwoTable (n + 1)) order offset =
      fabiusTaylorHorner (fabiusInversePowTwoTable n) order offset := by
  unfold fabiusTaylorHorner
  exact fabiusTaylorHorner_go_table_succ n order order horder le_rfl offset

/-- Extending the inverse-power table by any number of entries leaves every
Horner subcomputation within the original table unchanged. -/
lemma fabiusTaylorHorner_go_table_add (n extra order m : ℕ)
    (horder : order ≤ n) (hm : m ≤ order) (offset : ℚ) :
    fabiusTaylorHorner.go (fabiusInversePowTwoTable (n + extra)) order offset m =
      fabiusTaylorHorner.go (fabiusInversePowTwoTable n) order offset m := by
  induction extra with
  | zero => simp
  | succ extra ih =>
      calc
        fabiusTaylorHorner.go
              (fabiusInversePowTwoTable (n + (extra + 1))) order offset m =
            fabiusTaylorHorner.go
              (fabiusInversePowTwoTable (n + extra)) order offset m := by
          simpa [Nat.add_assoc] using
            fabiusTaylorHorner_go_table_succ (n + extra) order m
              (by omega) hm offset
        _ = fabiusTaylorHorner.go
              (fabiusInversePowTwoTable n) order offset m := ih

/-- Extending the inverse-power table by any number of entries does not change
a Taylor polynomial whose order already fits in the original table. -/
theorem fabiusTaylorHorner_table_add (n extra order : ℕ)
    (horder : order ≤ n) (offset : ℚ) :
    fabiusTaylorHorner (fabiusInversePowTwoTable (n + extra)) order offset =
      fabiusTaylorHorner (fabiusInversePowTwoTable n) order offset := by
  unfold fabiusTaylorHorner
  exact fabiusTaylorHorner_go_table_add n extra order order horder le_rfl offset

/-- The Horner evaluator is independent of the chosen table bound, provided
both bounds contain every coefficient requested by the polynomial. -/
theorem fabiusTaylorHorner_table_eq_of_le (n maxExponent order : ℕ)
    (hn : n ≤ maxExponent) (horder : order ≤ n) (offset : ℚ) :
    fabiusTaylorHorner (fabiusInversePowTwoTable maxExponent) order offset =
      fabiusTaylorHorner (fabiusInversePowTwoTable n) order offset := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact fabiusTaylorHorner_table_add n extra order horder offset

/-- The Horner polynomial is independent of either table bound once both
tables contain all coefficients through `order`.  Unlike
`fabiusTaylorHorner_table_eq_of_le`, this statement does not require the two
table bounds themselves to be ordered. -/
theorem fabiusTaylorHorner_table_eq_of_order_le
    (n m order : ℕ) (hn : order ≤ n) (hm : order ≤ m) (offset : ℚ) :
    fabiusTaylorHorner (fabiusInversePowTwoTable n) order offset =
      fabiusTaylorHorner (fabiusInversePowTwoTable m) order offset := by
  rcases le_total n m with hnm | hmn
  · exact (fabiusTaylorHorner_table_eq_of_le n m order hnm hn offset).symm
  · exact fabiusTaylorHorner_table_eq_of_le m n order hmn hm offset

private theorem log2_two_mul (a : ℕ) (ha : a ≠ 0) :
    Nat.log2 (2 * a) = Nat.log2 a + 1 := by
  rw [Nat.log2_eq_log_two, mul_comm, Nat.log_mul_base Nat.one_lt_two ha,
    ← Nat.log2_eq_log_two]

private theorem fabiusDyadicUnitAux_refine_direct (n a : ℕ) :
    fabiusDyadicUnitAux (fabiusInversePowTwoTable (n + 1)) (n + 1) (2 * a) =
      fabiusDyadicUnitAux (fabiusInversePowTwoTable n) n a := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
      cases a with
      | zero => simp [fabiusDyadicUnitAux]
      | succ a =>
          have hdouble : 2 * a + 1 + 1 = 2 * (a + 1) := by omega
          have hthreshold : 2 ^ (n + 1) ≤ 2 * (a + 1) ↔ 2 ^ n ≤ a + 1 := by
            rw [pow_succ]
            omega
          rw [show 2 * (a + 1) = (2 * a + 1) + 1 by omega,
            fabiusDyadicUnitAux, fabiusDyadicUnitAux]
          split <;> rename_i hleft
          · rw [hdouble] at hleft
            rw [if_pos (hthreshold.mp hleft)]
          · have hright : ¬ 2 ^ n ≤ a + 1 := by
              rw [hdouble] at hleft
              intro hbad
              exact hleft (hthreshold.mpr hbad)
            rw [if_neg hright]
            dsimp only
            have hx0 : a + 1 ≠ 0 := by omega
            have hxlt : a + 1 < 2 ^ n := Nat.lt_of_not_ge hright
            have hloglt : Nat.log2 (a + 1) < n := by
              rw [Nat.log2_eq_log_two]
              exact Nat.log_lt_of_lt_pow hx0 hxlt
            have hpowle : 2 ^ Nat.log2 (a + 1) ≤ a + 1 := by
              rw [Nat.log2_eq_log_two]
              exact Nat.pow_log_le_self 2 hx0
            have hlogdouble : Nat.log2 (2 * a + 1 + 1) = Nat.log2 (a + 1) + 1 := by
              rw [hdouble, log2_two_mul (a + 1) hx0]
            have horder : n + 1 - (Nat.log2 (a + 1) + 1) =
                n - Nat.log2 (a + 1) := by omega
            have hrem : 2 * a + 1 + 1 - 2 ^ (Nat.log2 (a + 1) + 1) =
                2 * (a + 1 - 2 ^ Nat.log2 (a + 1)) := by
              rw [hdouble, pow_succ]
              omega
            have hrem_lt : a + 1 - 2 ^ Nat.log2 (a + 1) < a + 1 := by
              have : 0 < 2 ^ Nat.log2 (a + 1) := by positivity
              omega
            have hoffset :
                ((2 * (a + 1 - 2 ^ Nat.log2 (a + 1)) : ℕ) : ℚ) /
                    (2 : ℚ) ^ (n + 1) =
                  (a + 1 - 2 ^ Nat.log2 (a + 1) : ℕ) / (2 : ℚ) ^ n := by
              push_cast
              rw [pow_succ]
              ring
            rw [hlogdouble, horder, hrem, hoffset,
              fabiusTaylorHorner_table_succ n (n - Nat.log2 (a + 1))
                (Nat.sub_le n _) _,
              ih (a + 1 - 2 ^ Nat.log2 (a + 1)) hrem_lt]

private theorem fabiusDyadicUnit_refine_direct (n a : ℕ) :
    fabiusDyadicUnit (n + 1) (2 * a) = fabiusDyadicUnit n a := by
  by_cases ha : a = 0
  · subst a
    simp
  have h2a : 2 * a ≠ 0 := mul_ne_zero (by omega) ha
  have hthreshold : 2 ^ (n + 1) ≤ 2 * a ↔ 2 ^ n ≤ a := by
    rw [pow_succ]
    omega
  unfold fabiusDyadicUnit
  rw [if_neg h2a, if_neg ha]
  by_cases h : 2 ^ n ≤ a
  · rw [if_pos h, if_pos (hthreshold.mpr h)]
  · rw [if_neg h, if_neg (fun hbad => h (hthreshold.mp hbad))]
    exact fabiusDyadicUnitAux_refine_direct n a

/-- Refining a dyadic representation does not change the bounded value. -/
theorem fabiusDyadicValue_refine (n : ℕ) (a : ℤ) :
    fabiusDyadicValue (n + 1) (2 * a) = fabiusDyadicValue n a := by
  by_cases ha : a ≤ 0
  · have h2a : 2 * a ≤ 0 := by omega
    simp [fabiusDyadicValue, ha, h2a]
  · have ha0 : 0 ≤ a := (lt_of_not_ge ha).le
    have h2a : ¬ 2 * a ≤ 0 := by omega
    rw [fabiusDyadicValue, if_neg h2a, fabiusDyadicValue, if_neg ha]
    rw [Int.toNat_mul (by omega : (0 : ℤ) ≤ 2) ha0]
    exact fabiusDyadicUnit_refine_direct n a.toNat

/-- Refining a dyadic representation does not change the global value. -/
theorem extendedFabiusDyadicValue_refine (n : ℕ) (a : ℤ) :
    extendedFabiusDyadicValue (n + 1) (2 * a) =
      extendedFabiusDyadicValue n a := by
  by_cases ha : a ≤ 0
  · have h2a : 2 * a ≤ 0 := by omega
    simp [extendedFabiusDyadicValue, ha, h2a]
  · have ha0 : 0 ≤ a := (lt_of_not_ge ha).le
    have h2a : ¬ 2 * a ≤ 0 := by omega
    rw [extendedFabiusDyadicValue, if_neg h2a,
      extendedFabiusDyadicValue, if_neg ha]
    dsimp only
    rw [Int.toNat_mul (by omega : (0 : ℤ) ≤ 2) ha0]
    have htwo : (2 : ℤ).toNat = 2 := by decide
    rw [htwo]
    have hscale : 2 ^ (n + 1) = 2 * 2 ^ n := by
      rw [pow_succ]
      omega
    rw [hscale]
    have hblock : 2 * a.toNat / (2 * (2 * 2 ^ n)) =
        a.toNat / (2 * 2 ^ n) := by
      exact Nat.mul_div_mul_left a.toNat (2 * 2 ^ n) (by omega)
    have hresidue : 2 * a.toNat % (2 * (2 * 2 ^ n)) =
        2 * (a.toNat % (2 * 2 ^ n)) := by
      exact Nat.mul_mod_mul_left 2 a.toNat (2 * 2 ^ n)
    rw [hblock, hresidue]
    by_cases hres : a.toNat % (2 * 2 ^ n) ≤ 2 ^ n
    · have htwice : 2 * (a.toNat % (2 * 2 ^ n)) ≤ 2 * 2 ^ n :=
        Nat.mul_le_mul_left 2 hres
      rw [if_pos hres, if_pos htwice, fabiusDyadicUnit_refine_direct]
    · have htwice : ¬ 2 * (a.toNat % (2 * 2 ^ n)) ≤ 2 * 2 ^ n := by
        intro hbad
        exact hres ((Nat.mul_le_mul_left_iff (by omega : 0 < 2)).mp hbad)
      rw [if_neg hres, if_neg htwice, ← Nat.mul_sub_left_distrib,
        fabiusDyadicUnit_refine_direct]

/-- Iterated form of `fabiusDyadicValue_refine`: multiplying the numerator by
`2 ^ k` while raising the exponent by `k` leaves the bounded value unchanged.
This is the step used by `fabiusDyadicValue_eq_of_rat_eq` below. -/
theorem fabiusDyadicValue_refine_iter (n k : ℕ) (a : ℤ) :
    fabiusDyadicValue (n + k) ((2 : ℤ) ^ k * a) = fabiusDyadicValue n a := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        fabiusDyadicValue (n + (k + 1)) ((2 : ℤ) ^ (k + 1) * a) =
            fabiusDyadicValue (n + k) ((2 : ℤ) ^ k * a) := by
          simpa [pow_succ, Nat.add_assoc, mul_assoc, mul_comm, mul_left_comm] using
            fabiusDyadicValue_refine (n + k) ((2 : ℤ) ^ k * a)
        _ = fabiusDyadicValue n a := ih

/-- Iterated form of `extendedFabiusDyadicValue_refine`: multiplying the
numerator by `2 ^ k` while raising the exponent by `k` leaves the global
value unchanged.  This is the step used by
`extendedFabiusDyadicValue_eq_of_rat_eq` below. -/
theorem extendedFabiusDyadicValue_refine_iter (n k : ℕ) (a : ℤ) :
    extendedFabiusDyadicValue (n + k) ((2 : ℤ) ^ k * a) =
      extendedFabiusDyadicValue n a := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        extendedFabiusDyadicValue (n + (k + 1)) ((2 : ℤ) ^ (k + 1) * a) =
            extendedFabiusDyadicValue (n + k) ((2 : ℤ) ^ k * a) := by
          simpa [pow_succ, Nat.add_assoc, mul_assoc, mul_comm, mul_left_comm] using
            extendedFabiusDyadicValue_refine (n + k) ((2 : ℤ) ^ k * a)
        _ = extendedFabiusDyadicValue n a := ih

private theorem integer_eq_pow_mul_of_dyadic_eq (n k : ℕ) (a b : ℤ)
    (h : (a : ℚ) / (2 : ℚ) ^ n = (b : ℚ) / (2 : ℚ) ^ (n + k)) :
    b = (2 : ℤ) ^ k * a := by
  have hcross : (a : ℚ) * (2 : ℚ) ^ (n + k) =
      (b : ℚ) * (2 : ℚ) ^ n :=
    (div_eq_div_iff (by positivity) (by positivity)).mp h
  rw [pow_add] at hcross
  have hcancel : (a : ℚ) * (2 : ℚ) ^ k = b := by
    apply mul_left_cancel₀ (a := (2 : ℚ) ^ n) (by positivity)
    calc
      (2 : ℚ) ^ n * ((a : ℚ) * (2 : ℚ) ^ k) =
          (a : ℚ) * ((2 : ℚ) ^ n * (2 : ℚ) ^ k) := by ring
      _ = (b : ℚ) * (2 : ℚ) ^ n := hcross
      _ = (2 : ℚ) ^ n * b := by ring
  have : b = a * (2 : ℤ) ^ k := by exact_mod_cast hcancel.symm
  simpa [mul_comm] using this

/-- The bounded evaluator depends only on the represented rational number. -/
theorem fabiusDyadicValue_eq_of_rat_eq (n m : ℕ) (a b : ℤ)
    (h : (a : ℚ) / (2 : ℚ) ^ n = (b : ℚ) / (2 : ℚ) ^ m) :
    fabiusDyadicValue n a = fabiusDyadicValue m b := by
  rcases le_total n m with hnm | hmn
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    have hb : b = (2 : ℤ) ^ k * a := integer_eq_pow_mul_of_dyadic_eq n k a b h
    subst b
    exact (fabiusDyadicValue_refine_iter n k a).symm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    have ha : a = (2 : ℤ) ^ k * b :=
      integer_eq_pow_mul_of_dyadic_eq m k b a h.symm
    subst a
    exact fabiusDyadicValue_refine_iter m k b

/-- The global evaluator depends only on the represented rational number. -/
theorem extendedFabiusDyadicValue_eq_of_rat_eq (n m : ℕ) (a b : ℤ)
    (h : (a : ℚ) / (2 : ℚ) ^ n = (b : ℚ) / (2 : ℚ) ^ m) :
    extendedFabiusDyadicValue n a = extendedFabiusDyadicValue m b := by
  rcases le_total n m with hnm | hmn
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    have hb : b = (2 : ℤ) ^ k * a := integer_eq_pow_mul_of_dyadic_eq n k a b h
    subst b
    exact (extendedFabiusDyadicValue_refine_iter n k a).symm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    have ha : a = (2 : ℤ) ^ k * b :=
      integer_eq_pow_mul_of_dyadic_eq m k b a h.symm
    subst a
    exact extendedFabiusDyadicValue_refine_iter m k b

/-- On nonnegative numerators, the signed-numerator bounded evaluator is
exactly the natural-numerator unit evaluator. -/
theorem fabiusDyadicValue_natCast (n a : ℕ) :
    fabiusDyadicValue n (a : ℤ) = fabiusDyadicUnit n a := by
  cases a with
  | zero => simp
  | succ a => simp [fabiusDyadicValue]

/-- The natural-numerator unit evaluator depends only on the represented
dyadic rational, even when the two denominator exponents are unrelated. -/
theorem fabiusDyadicUnit_eq_of_rat_eq (n m a b : ℕ)
    (h : (a : ℚ) / (2 : ℚ) ^ n = (b : ℚ) / (2 : ℚ) ^ m) :
    fabiusDyadicUnit n a = fabiusDyadicUnit m b := by
  have h' : ((a : ℤ) : ℚ) / (2 : ℚ) ^ n =
      ((b : ℤ) : ℚ) / (2 : ℚ) ^ m := by
    norm_num only [Int.cast_natCast]
    exact h
  simpa only [fabiusDyadicValue_natCast] using
    fabiusDyadicValue_eq_of_rat_eq n m (a : ℤ) (b : ℤ) h'

/-! ## Detection and rational wrappers -/

/-- `dyadicExponent?` succeeds exactly on dyadic rationals. -/
theorem dyadicExponent?_exists_iff (x : ℚ) :
    (∃ exponent, dyadicExponent? x = some exponent) ↔ IsDyadicRational x := by
  constructor
  · rintro ⟨exponent, hexponent⟩
    unfold dyadicExponent? at hexponent
    dsimp only at hexponent
    split at hexponent
    · rename_i hden
      injection hexponent with hexponent
      subst exponent
      exact ⟨_, hden⟩
    · simp at hexponent
  · rintro ⟨exponent, hden⟩
    refine ⟨x.den.log2, ?_⟩
    unfold dyadicExponent?
    dsimp only
    rw [if_pos]
    rw [hden, Nat.log2_eq_log_two, Nat.log_pow Nat.one_lt_two]

private theorem evalDyadic_eq_none_iff
    (evaluator : ℕ → ℤ → ℚ) (x : ℚ) :
    (match dyadicExponent? x with
      | none => none
      | some exponent => some (evaluator exponent x.num)) = none ↔
      ¬ IsDyadicRational x := by
  constructor
  · intro heval hdyadic
    obtain ⟨exponent, hexponent⟩ := (dyadicExponent?_exists_iff x).2 hdyadic
    simp [hexponent] at heval
  · intro hnondyadic
    split
    · rfl
    · rename_i exponent hexponent
      exact False.elim <| hnondyadic <|
        (dyadicExponent?_exists_iff x).1 ⟨exponent, hexponent⟩

/-- The rational bounded evaluator rejects exactly the non-dyadic inputs. -/
theorem evalFabiusDyadic_eq_none_iff (x : ℚ) :
    evalFabiusDyadic x = none ↔ ¬ IsDyadicRational x := by
  exact evalDyadic_eq_none_iff fabiusDyadicValue x

/-- The rational global evaluator rejects exactly the non-dyadic inputs. -/
theorem evalExtendedFabiusDyadic_eq_none_iff (x : ℚ) :
    evalExtendedFabiusDyadic x = none ↔ ¬ IsDyadicRational x := by
  exact evalDyadic_eq_none_iff extendedFabiusDyadicValue x

/-- The rational Rvachev evaluator rejects exactly the non-dyadic inputs. -/
theorem evalRvachevDyadic_eq_none_iff (x : ℚ) :
    evalRvachevDyadic x = none ↔ ¬ IsDyadicRational x := by
  exact evalDyadic_eq_none_iff rvachevDyadic x

/--
The exact single-step recurrence needed by the bit-recursive evaluator.

This is Proposition 10 specialized to positive dyadics in `(0,1]`, expressed
entirely in `ℚ`.
-/
def FabiusDyadicHasBitRecurrence (values : Array ℚ) (n : ℕ) : Prop :=
  ∀ a : ℕ, 0 < a → a ≤ 2 ^ n →
    let leadingExponent := Nat.log2 a
    let order := n - leadingExponent
    let remainder := a - 2 ^ leadingExponent
    let offset := (remainder : ℚ) / (2 : ℚ) ^ n
    fabiusDyadic n a =
      fabiusTaylorHorner values order offset - fabiusDyadic n remainder

/--
Assuming the single-step bit recurrence for `values` at exponent `n`, strong
induction on the numerator shows that the bit recursion agrees with equation
(32) at every numerator `a < 2 ^ n`.

The hypothesis is discharged for the precomputed table by
`fabiusInversePowTwoTable_hasBitRecurrence` in `DyadicClosedForm`.
-/
theorem fabiusDyadicUnitAux_eq_of_bitRecurrence
    (values : Array ℚ) (n : ℕ)
    (hrec : FabiusDyadicHasBitRecurrence values n) :
    ∀ a : ℕ, a < 2 ^ n →
      fabiusDyadicUnitAux values n a = fabiusDyadic n a := by
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
      intro ha
      cases a with
      | zero =>
          rw [fabiusDyadicUnitAux.eq_1]
          exact (fabiusDyadic_arg_zero n).symm
      | succ a =>
          have hpos : 0 < a + 1 := Nat.zero_lt_succ a
          have hnot_ge : ¬ 2 ^ n ≤ a + 1 := Nat.not_le.mpr ha
          rw [fabiusDyadicUnitAux.eq_2, if_neg hnot_ge]
          let leadingExponent := Nat.log2 (a + 1)
          let remainder := a + 1 - 2 ^ leadingExponent
          have hpow_pos : 0 < 2 ^ leadingExponent := by positivity
          have hrem_lt : remainder < a + 1 := by
            dsimp [remainder]
            exact Nat.sub_lt hpos hpow_pos
          have hrem_den : remainder < 2 ^ n := hrem_lt.trans ha
          change
            fabiusTaylorHorner values (n - Nat.log2 (a + 1))
                (((a + 1 - 2 ^ Nat.log2 (a + 1) : ℕ) : ℚ) / (2 : ℚ) ^ n) -
              fabiusDyadicUnitAux values n (a + 1 - 2 ^ Nat.log2 (a + 1)) =
            fabiusDyadic n (a + 1)
          rw [ih remainder hrem_lt hrem_den]
          exact (hrec (a + 1) hpos ha.le).symm

/--
The same recurrence hypothesis pins the right endpoint of the unit grid:
`fabiusDyadic n (2 ^ n) = 1`.

At `a = 2 ^ n` the leading exponent is `n`, so the recurrence contributes the
constant Horner term `1` minus the value at numerator `0`.
-/
theorem fabiusDyadic_unit_endpoint_of_bitRecurrence
    (values : Array ℚ) (n : ℕ)
    (hrec : FabiusDyadicHasBitRecurrence values n) :
    fabiusDyadic n (2 ^ n) = 1 := by
  have h := hrec (2 ^ n) (by positivity) le_rfl
  simpa [Nat.log2_eq_log_two, Nat.log_pow Nat.one_lt_two,
    fabiusTaylorHorner, fabiusTaylorHorner.go.eq_1, fabiusDyadic_arg_zero] using h

/--
All recursion and endpoint plumbing for correctness of `fabiusDyadicUnit`.
The only mathematical input is the exact single-step recurrence.
-/
theorem fabiusDyadicUnit_eq_fabiusDyadic_of_bitRecurrence
    (n a : ℕ) (ha : a ≤ 2 ^ n)
    (hrec : FabiusDyadicHasBitRecurrence (fabiusInversePowTwoTable n) n) :
    fabiusDyadicUnit n a = fabiusDyadic n a := by
  rcases ha.eq_or_lt with rfl | ha
  · rw [fabiusDyadicUnit_of_ge n (2 ^ n) le_rfl]
    exact (fabiusDyadic_unit_endpoint_of_bitRecurrence
      (fabiusInversePowTwoTable n) n hrec).symm
  · by_cases hzero : a = 0
    · subst a
      simp
    · rw [fabiusDyadicUnit]
      simp only [hzero, if_false, Nat.not_le.mpr ha, if_false]
      exact fabiusDyadicUnitAux_eq_of_bitRecurrence
        (fabiusInversePowTwoTable n) n hrec a ha

end Fabius
```

### `UpstreamDyadicClosedForm.lean`

```lean
import UpstreamDyadicCorrectness
import UpstreamMomentPowerSeries
import UpstreamThueMorseBitSupport
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Tactic.FieldSimp

/-!
# Closed-form dyadic recurrence for the Fabius function

This module proves the exact Taylor-block identity behind the executable
bit recursion.  It combines Thue--Morse cancellation with a polynomial kernel
refinement law, identifies the inverse-power lookup table, and concludes that
`fabiusDyadicUnit` agrees with the closed formula `fabiusDyadic` on `[0, 1]`.

Main results:

* `sum_range_two_mul` -- the even/odd block split
  `∑_{n < 2k} f n = ∑_{j < k} (f (2j) + f (2j+1))` over any additive
  commutative monoid, the halving step used by every Thue--Morse recursion
  downstream, together with its `Fin`-indexed face `sum_fin_two_mul`;
* `sum_range_block_decomposition` -- the general `m`-blocks-of-length-`p`
  split of `range (m * p)`;
* `thueMorse_sum_split` and `thueMorseSign_add_pow_two` -- the Thue--Morse
  cancellation of a complete dyadic block;
* `dyadicKernel_has_refinement` and `dyadicBlock_eq_taylor_sum` -- the
  polynomial kernel refinement law and the Taylor-block expansion;
* `fabiusDyadicUnit_eq_fabiusDyadic` -- the executable bit recursion agrees
  with the closed formula on `[0, 1]`.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

/-- Choosing disjoint blocks of sizes `p` and `j` out of `n` elements gives
the same count in either order.  This symmetry is what lets the binomial
coefficients be re-indexed in `dyadicKernelPolynomial_hasseDeriv`. -/
lemma choose_mul_choose_disjoint (n p j : ℕ) :
    Nat.choose n p * Nat.choose (n - p) j =
      Nat.choose n j * Nat.choose (n - j) p := by
  have hp := Nat.choose_mul (n := n) (k := p + j) (s := p) (by omega : p ≤ p + j)
  have hj := Nat.choose_mul (n := n) (k := p + j) (s := j) (by omega : j ≤ p + j)
  have hsym : Nat.choose (p + j) p = Nat.choose (p + j) j :=
    Nat.choose_symm_of_eq_add rfl
  calc
    _ = Nat.choose n (p + j) * Nat.choose (p + j) p := by
      simpa using hp.symm
    _ = Nat.choose n (p + j) * Nat.choose (p + j) j := by rw [hsym]
    _ = _ := by simpa [add_comm] using hj

/-- Triangular numbers split additively: `Nat.choose (m + j + 1) 2` equals
`Nat.choose (m + 1) 2 + m * j + Nat.choose (j + 1) 2`.  This is the exponent
bookkeeping behind the power of two in `dyadicScale_choose_taylor`. -/
lemma choose_add_succ_two (m j : ℕ) :
    Nat.choose (m + j + 1) 2 =
      Nat.choose (m + 1) 2 + m * j + Nat.choose (j + 1) 2 := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [show m + (j + 1) + 1 = (m + j + 1) + 1 by omega,
        show 2 = 1 + 1 by omega, Nat.choose_succ_succ]
      rw [ih]
      have hjchoose : Nat.choose (j + 2) 2 = Nat.choose (j + 1) 2 + (j + 1) := by
        rw [show j + 2 = (j + 1) + 1 by omega,
          show 2 = 1 + 1 by omega, Nat.choose_succ_succ]
        simp [Nat.add_comm]
      rw [hjchoose]
      simp [Nat.choose_one_right]
      ring

/-- Closed form for a triangular number:
`2 * Nat.choose (j + 1) 2 = j * (j + 1)`. -/
lemma two_mul_choose_succ_two (j : ℕ) :
    2 * Nat.choose (j + 1) 2 = j * (j + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hchoose : Nat.choose (j + 2) 2 = Nat.choose (j + 1) 2 + (j + 1) := by
        rw [show j + 2 = (j + 1) + 1 by omega,
          show 2 = 1 + 1 by omega, Nat.choose_succ_succ]
        simp [Nat.add_comm]
      rw [hchoose]
      rw [Nat.mul_add, ih]
      ring

/-- Splits a `Fin (m + n)` sum into its first `m` terms and the `n` terms
after them, reindexed by `m + i`.  The `Fin`-indexed form of
`Finset.sum_range_add`, used to peel off a leading dyadic block in
`thueMorse_sum_split`. -/
theorem sum_fin_add {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m n : ℕ) :
    (∑ i : Fin (m + n), f i.val) =
      (∑ i : Fin m, f i.val) + ∑ i : Fin n, f (m + i.val) := by
  rw [Fin.sum_univ_eq_sum_range f (m + n), Fin.sum_univ_eq_sum_range f m,
    Fin.sum_univ_eq_sum_range (fun i => f (m + i)) n]
  exact Finset.sum_range_add f m n

/-- **Even/odd block split.**  Splitting a dyadic block sum by the lowest
binary digit: the even and odd halves of `range (2 * k)` are the images of
`range k` under doubling and doubling-plus-one.  Stated over an arbitrary
`AddCommMonoid`, because the corpus applies it over `ℚ`, over `ℝ`, over `ℤ`,
over `ℕ` and over modules.

This is the single halving step behind every Thue--Morse recursion in the
library, so it lives here, at the root of the import DAG.  It is proved by a
direct induction rather than as a specialization of
`sum_range_block_decomposition`, which appears much later in this file. -/
theorem sum_range_two_mul {M : Type*} [AddCommMonoid M]
    (k : ℕ) (f : ℕ → M) :
    ∑ n ∈ Finset.range (2 * k), f n =
      ∑ j ∈ Finset.range k, (f (2 * j) + f (2 * j + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, ih]
      abel

/-- Pairs a `Fin (2 * a)` sum into `a` consecutive two-term blocks
`f (2 j) + f (2 j + 1)`.  This is the index bookkeeping for the halving step
`thueMorse_sum_two_mul`; the `Fin`-indexed face of `sum_range_two_mul`. -/
theorem sum_fin_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (a : ℕ) :
    (∑ i : Fin (2 * a), f i.val) =
      ∑ j : Fin a, (f (2 * j.val) + f (2 * j.val + 1)) := by
  rw [Fin.sum_univ_eq_sum_range f (2 * a),
    Fin.sum_univ_eq_sum_range (fun j => f (2 * j) + f (2 * j + 1)) a]
  exact sum_range_two_mul a f

/-- Appending a zero binary digit leaves the digit sum unchanged. -/
@[simp] theorem binaryWeight_two_mul (h : ℕ) :
    binaryWeight (2 * h) = binaryWeight h := by
  cases h with
  | zero => simp [binaryWeight]
  | succ h =>
      rw [binaryWeight, binaryWeight,
        Nat.digits_base_mul Nat.one_lt_two (by positivity : 0 < h + 1)]
      simp

/-- Appending a one binary digit raises the digit sum by one. -/
@[simp] theorem binaryWeight_two_mul_add_one (h : ℕ) :
    binaryWeight (2 * h + 1) = binaryWeight h + 1 := by
  rw [binaryWeight, binaryWeight]
  have hdigits := Nat.digits_add 2 Nat.one_lt_two 1 h (by decide) (Or.inl (by decide))
  rw [add_comm] at hdigits
  rw [hdigits]
  simp [add_comm]

/-- The Thue--Morse sign is invariant under doubling the index. -/
@[simp] theorem thueMorseSign_two_mul (h : ℕ) :
    thueMorseSign (2 * h) = thueMorseSign h := by
  simp [thueMorseSign]

/-- The Thue--Morse sign flips between an even index and its successor. -/
@[simp] theorem thueMorseSign_two_mul_add_one (h : ℕ) :
    thueMorseSign (2 * h + 1) = -thueMorseSign h := by
  simp [thueMorseSign, pow_succ]

/-- The signed Thue--Morse sequence is a character of bitwise xor. -/
theorem thueMorseSign_xor (a b : ℕ) :
    thueMorseSign (a ^^^ b) = thueMorseSign a * thueMorseSign b := by
  induction a using Nat.binaryRec generalizing b with
  | zero => simp [thueMorseSign, binaryWeight]
  | bit ba a ih =>
      refine Nat.bitCasesOn (motive := fun b =>
        thueMorseSign (Nat.bit ba a ^^^ b) =
          thueMorseSign (Nat.bit ba a) * thueMorseSign b) b ?_
      intro bb b
      rw [Nat.xor_bit]
      cases ba <;> cases bb <;> simp [ih]

/-- Reflecting an index in a dyadic block complements its first `k` binary
digits and multiplies its Thue--Morse sign by `(-1)^k`. -/
theorem thueMorseSign_dyadic_complement
    (k r : ℕ) (hr : r < 2 ^ k) :
    thueMorseSign (2 ^ k - 1 - r) =
      (-1 : ℤ) ^ k * thueMorseSign r := by
  induction k generalizing r with
  | zero =>
      have hr0 : r = 0 := by omega
      subst r
      norm_num [thueMorseSign, binaryWeight]
  | succ k ih =>
      rcases Nat.even_or_odd r with heven | hodd
      · rcases heven with ⟨s, hs⟩
        have hrform : r = 2 * s := by omega
        have hslt : s < 2 ^ k := by
          rw [pow_succ] at hr
          omega
        have hreflect :
            2 ^ (k + 1) - 1 - r =
              2 * (2 ^ k - 1 - s) + 1 := by
          rw [pow_succ]
          omega
        rw [hreflect, thueMorseSign_two_mul_add_one,
          ih s hslt, hrform, thueMorseSign_two_mul, pow_succ]
        ring
      · rcases hodd with ⟨s, hs⟩
        have hrform : r = 2 * s + 1 := by omega
        have hslt : s < 2 ^ k := by
          rw [pow_succ] at hr
          omega
        have hreflect :
            2 ^ (k + 1) - 1 - r =
              2 * (2 ^ k - 1 - s) := by
          rw [pow_succ]
          omega
        rw [hreflect, thueMorseSign_two_mul,
          ih s hslt, hrform, thueMorseSign_two_mul_add_one, pow_succ]
        ring

/-- Halving a signed Thue--Morse sum: a sum of `thueMorseSign i * f i` over
`Fin (2 * a)` collapses to a sum of `thueMorseSign j * (f (2 j) - f (2 j + 1))`
over `Fin a`, because the sign flips within each adjacent pair.  This is the
step that converts the kernel refinement law into
`fabiusDyadic_refine_of_kernel`. -/
theorem thueMorse_sum_two_mul (a : ℕ) (f : ℕ → ℚ) :
    (∑ i : Fin (2 * a), (thueMorseSign i.val : ℚ) * f i.val) =
      ∑ j : Fin a, (thueMorseSign j.val : ℚ) *
        (f (2 * j.val) - f (2 * j.val + 1)) := by
  let g : ℕ → ℚ := fun i => (thueMorseSign i : ℚ) * f i
  change (∑ i : Fin (2 * a), g i.val) =
    ∑ j : Fin a, (thueMorseSign j.val : ℚ) *
      (f (2 * j.val) - f (2 * j.val + 1))
  rw [sum_fin_two_mul g]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [g]
  simp only [thueMorseSign_two_mul, thueMorseSign_two_mul_add_one]
  push_cast
  ring

/-- The signed power sum `∑_{h < 2 ^ b} thueMorseSign h * h ^ d` over one
complete dyadic Thue--Morse block. -/
private def thuePowerSum (b d : ℕ) : ℚ :=
  ∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) * (h.val : ℚ) ^ d

/-- Doubling the block length expresses `thuePowerSum (b + 1) d` through the
half-length block in degrees strictly below `d`: the degree-`d` terms of the
two halves cancel, which is why the range stops at `d` and why the whole sum
picks up a minus sign.  This is the induction step of
`thuePowerSum_eq_zero_of_lt`, and it is re-exported under local names by
`ThueMorsePrefix` and `FabiusUniformSpline`. -/
lemma thuePowerSum_succ (b d : ℕ) :
    thuePowerSum (b + 1) d =
      -(∑ k ∈ Finset.range d,
          (Nat.choose d k : ℚ) * (2 : ℚ) ^ k * thuePowerSum b k) := by
  rw [thuePowerSum, pow_succ', mul_comm]
  rw [show 2 ^ b * 2 = 2 * 2 ^ b by omega]
  change
    (∑ i : Fin (2 * 2 ^ b),
      (thueMorseSign i.val : ℚ) * (i.val : ℚ) ^ d) = _
  let f : ℕ → ℚ := fun i => (i : ℚ) ^ d
  change
    (∑ i : Fin (2 * 2 ^ b),
      (thueMorseSign i.val : ℚ) * f i.val) = _
  rw [thueMorse_sum_two_mul (2 ^ b) f]
  have hpoint (j : ℕ) :
      ((2 * j : ℕ) : ℚ) ^ d - ((2 * j + 1 : ℕ) : ℚ) ^ d =
        -(∑ k ∈ Finset.range d,
          (Nat.choose d k : ℚ) * (2 : ℚ) ^ k * (j : ℚ) ^ k) := by
    push_cast
    rw [add_pow, Finset.sum_range_succ]
    simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one]
    rw [mul_pow]
    ring_nf
  simp only [f]
  simp_rw [hpoint]
  calc
    (∑ j : Fin (2 ^ b), (thueMorseSign j.val : ℚ) *
        -(∑ k ∈ Finset.range d,
          (Nat.choose d k : ℚ) * (2 : ℚ) ^ k * (j.val : ℚ) ^ k)) =
      -(∑ j : Fin (2 ^ b), ∑ k ∈ Finset.range d,
        (thueMorseSign j.val : ℚ) *
          ((Nat.choose d k : ℚ) * (2 : ℚ) ^ k * (j.val : ℚ) ^ k)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        rw [mul_neg, neg_inj, Finset.mul_sum]
    _ = -(∑ k ∈ Finset.range d, ∑ j : Fin (2 ^ b),
        (thueMorseSign j.val : ℚ) *
          ((Nat.choose d k : ℚ) * (2 : ℚ) ^ k * (j.val : ℚ) ^ k)) := by
        rw [Finset.sum_comm]
    _ = _ := by
      apply congrArg Neg.neg
      apply Finset.sum_congr rfl
      intro k hk
      rw [thuePowerSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- Prouhet cancellation: a complete Thue--Morse block of length `2 ^ b`
annihilates every monomial of degree `d < b`.  The hypothesis is exactly
`d < b`; at `d = b` the sum is nonzero, with the explicit value computed in
`ThueMorsePrefix.thueMorsePowerSum_self`. -/
lemma thuePowerSum_eq_zero_of_lt (b d : ℕ) (hd : d < b) :
    thuePowerSum b d = 0 := by
  induction b generalizing d with
  | zero => omega
  | succ b ih =>
      rw [thuePowerSum_succ]
      rw [Finset.sum_eq_zero]
      · simp
      · intro k hk
        have hklt : k < d := Finset.mem_range.mp hk
        rw [ih k (hklt.trans_le (by omega : d ≤ b))]
        ring

/-- Prouhet cancellation for an arbitrary affine argument: for `d < b` the
signed sum of `(x + y * h) ^ d` over a complete block `h < 2 ^ b` vanishes, for
every `x` and `y`.  Expanding the binomial reduces it to
`thuePowerSum_eq_zero_of_lt` in each degree. -/
lemma thueMorse_affine_power_sum_eq_zero (b d : ℕ) (hd : d < b)
    (x y : ℚ) :
    (∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
      (x + y * (h.val : ℚ)) ^ d) = 0 := by
  simp_rw [add_pow, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  have hdegree : d - k < b := (Nat.sub_le d k).trans_lt hd
  have hinner :
      (∑ h : Fin (2 ^ b),
        (thueMorseSign h.val : ℚ) *
          (x ^ k * (y * (h.val : ℚ)) ^ (d - k) * (Nat.choose d k : ℚ))) =
        (x ^ k * y ^ (d - k) * (Nat.choose d k : ℚ)) *
          thuePowerSum b (d - k) := by
    rw [thuePowerSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    rw [mul_pow]
    ring
  rw [hinner, thuePowerSum_eq_zero_of_lt b (d - k) hdegree, mul_zero]

/-- Adding a fresh leading bit flips the Thue--Morse sign:
`thueMorseSign (2 ^ b + h) = -thueMorseSign h` for `h < 2 ^ b`.  The corpus
uses this whenever a dyadic block is reflected onto its translate. -/
theorem thueMorseSign_add_pow_two (b h : ℕ) (hh : h < 2 ^ b) :
    thueMorseSign (2 ^ b + h) = -thueMorseSign h := by
  rw [thueMorseSign, thueMorseSign, binaryWeight_add_pow_two b h hh, pow_succ]
  ring

/-- Splits a signed sum over `2 ^ b + r` indices, with `r ≤ 2 ^ b`, as the
complete leading block minus the signed sum over the `r` translated indices;
the minus sign is `thueMorseSign_add_pow_two`.  This is the identity behind
`fabiusDyadic_add_remainder_eq_block`. -/
theorem thueMorse_sum_split (b r : ℕ) (hr : r ≤ 2 ^ b) (f : ℕ → ℚ) :
    (∑ i : Fin (2 ^ b + r), (thueMorseSign i.val : ℚ) * f i.val) =
      (∑ i : Fin (2 ^ b), (thueMorseSign i.val : ℚ) * f i.val) -
        ∑ j : Fin r, (thueMorseSign j.val : ℚ) * f (2 ^ b + j.val) := by
  let g : ℕ → ℚ := fun i => (thueMorseSign i : ℚ) * f i
  change (∑ i : Fin (2 ^ b + r), g i.val) =
    (∑ i : Fin (2 ^ b), g i.val) -
      ∑ j : Fin r, (thueMorseSign j.val : ℚ) * f (2 ^ b + j.val)
  rw [sum_fin_add g]
  rw [sub_eq_add_neg, add_right_inj, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j.val < 2 ^ b := j.isLt.trans_le hr
  simp only [g]
  rw [thueMorseSign_add_pow_two b j.val hjlt]
  push_cast
  ring

/-- The normalization of equation (32) at grid exponent `n`, namely
`2 ^ (-Nat.choose (n + 1) 2) / n !`.  The negative exponent is an integer
power, so this is the exact rational prefactor, not a truncation. -/
private def dyadicScale (n : ℕ) : ℚ :=
  (2 : ℚ) ^ (-(Nat.choose (n + 1) 2 : ℤ)) / n.factorial

/-- The polynomial kernel of equation (32): `∑_{2 k ≤ n}` of
`Nat.choose n (2 k) * x ^ (n - 2 k) * moment k`.  Only even binomial indices
occur, so the moments enter at index `k` while the power of `x` keeps the
parity of `n`.  Multiplying the signed sum of
`thueMorseSign h * dyadicKernel n (2 a - 2 h - 1)` over `h < a` by
`dyadicScale n` gives `fabiusDyadic n a`. -/
private def dyadicKernel (n : ℕ) (x : ℚ) : ℚ :=
  ∑ k : Fin (n / 2 + 1),
    (Nat.choose n (2 * k.val) : ℚ) * x ^ (n - 2 * k.val) * moment k.val

/-- Rewrites the `Fin`-indexed kernel sum as a sum over
`Finset.range (n / 2 + 1)`, the form the polynomial computations below use. -/
lemma dyadicKernel_eq_sum_range (n : ℕ) (x : ℚ) :
    dyadicKernel n x =
      ∑ k ∈ Finset.range (n / 2 + 1),
        (Nat.choose n (2 * k) : ℚ) * x ^ (n - 2 * k) * moment k := by
  let g : ℕ → ℚ := fun k =>
    (Nat.choose n (2 * k) : ℚ) * x ^ (n - 2 * k) * moment k
  change (∑ k : Fin (n / 2 + 1), g k.val) = _
  rw [Fin.sum_univ_eq_sum_range g (n / 2 + 1)]

/-- The kernel `dyadicKernel n` as a formal polynomial over `ℚ`, built from
monomials of degree `n - 2 k`.  Working with the polynomial rather than
the function is what makes the derivative and Taylor arguments below
available. -/
private noncomputable def dyadicKernelPolynomial (n : ℕ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (n / 2 + 1),
    Polynomial.monomial (n - 2 * k)
      ((Nat.choose n (2 * k) : ℚ) * moment k)

/-- The kernel polynomial evaluates to the kernel function.  This is the
bridge that lets the refinement law be proved as a polynomial identity and
then transported back to values. -/
lemma dyadicKernelPolynomial_eval (n : ℕ) (x : ℚ) :
    (dyadicKernelPolynomial n).eval x = dyadicKernel n x := by
  rw [dyadicKernelPolynomial, dyadicKernel,
    Polynomial.eval_finsetSum (Finset.range (n / 2 + 1))]
  let g : ℕ → ℚ := fun k =>
    (Nat.choose n (2 * k) : ℚ) * x ^ (n - 2 * k) * moment k
  change (∑ k ∈ Finset.range (n / 2 + 1),
      Polynomial.eval x (Polynomial.monomial (n - 2 * k)
        ((Nat.choose n (2 * k) : ℚ) * moment k))) =
    ∑ k : Fin (n / 2 + 1), g k.val
  rw [Fin.sum_univ_eq_sum_range g (n / 2 + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.eval_monomial]
  ring

/-- The `j`-th Hasse derivative of the kernel polynomial, for `j ≤ n`, is
`Nat.choose n j` times the kernel polynomial of index `n - j`.  This closure
of the kernel family under differentiation is what gives the finite Taylor
expansion `dyadicKernel_taylor`. -/
lemma dyadicKernelPolynomial_hasseDeriv (n j : ℕ) (hj : j ≤ n) :
    Polynomial.hasseDeriv j (dyadicKernelPolynomial n) =
      Polynomial.C (Nat.choose n j : ℚ) * dyadicKernelPolynomial (n - j) := by
  rw [dyadicKernelPolynomial, map_sum]
  rw [dyadicKernelPolynomial, Finset.mul_sum]
  simp only [Polynomial.hasseDeriv_monomial, Polynomial.C_mul_monomial]
  have hsmall : (n - j) / 2 + 1 ≤ n / 2 + 1 := by
    exact Nat.add_le_add_right (Nat.div_le_div_right (Nat.sub_le n j)) 1
  symm
  apply Finset.sum_subset_zero_on_sdiff (Finset.range_mono hsmall)
  · intro k hk
    have hkbig : k < n / 2 + 1 := Finset.mem_range.mp (Finset.mem_sdiff.mp hk).1
    have hknsmall : ¬ k < (n - j) / 2 + 1 := by
      simpa only [Finset.mem_range] using (Finset.mem_sdiff.mp hk).2
    have hdivlt : (n - j) / 2 < k := by omega
    have htwok : n - j < k * 2 :=
      (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mp hdivlt
    have hlt : n - 2 * k < j := by omega
    rw [Nat.choose_eq_zero_of_lt hlt]
    simp
  · intro k hk
    have hk_le_div : k ≤ (n - j) / 2 := by
      simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hk
    have htwok : k * 2 ≤ n - j :=
      (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mp hk_le_div
    have htwok' : 2 * k ≤ n - j := by omega
    have hexponent : n - 2 * k - j = n - j - 2 * k := by omega
    have hcoefficient := choose_mul_choose_disjoint n (2 * k) j
    rw [hexponent]
    congr 1
    have hcoefficientQ :
        (Nat.choose n j : ℚ) * Nat.choose (n - j) (2 * k) =
          (Nat.choose (n - 2 * k) j : ℚ) * Nat.choose n (2 * k) := by
      have hnat : Nat.choose n j * Nat.choose (n - j) (2 * k) =
          Nat.choose (n - 2 * k) j * Nat.choose n (2 * k) := by
        simpa [mul_comm] using hcoefficient.symm
      exact_mod_cast hnat
    calc
      _ = ((Nat.choose n j : ℚ) * Nat.choose (n - j) (2 * k)) * moment k := by ring
      _ = ((Nat.choose (n - 2 * k) j : ℚ) * Nat.choose n (2 * k)) * moment k := by
        rw [hcoefficientQ]
      _ = _ := by ring

/-- The kernel polynomial has degree at most `n`, so its Taylor expansion
terminates after `n + 1` terms. -/
lemma dyadicKernelPolynomial_natDegree_le (n : ℕ) :
    (dyadicKernelPolynomial n).natDegree ≤ n := by
  rw [dyadicKernelPolynomial]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (Polynomial.natDegree_monomial_le _).trans (Nat.sub_le n (2 * k))

/-- Finite Taylor expansion of the kernel: `dyadicKernel n (x + y)` equals
`∑_{j ≤ n} Nat.choose n j * dyadicKernel (n - j) x * y ^ j`.  The identity is
exact, not an approximation, because the kernel is a polynomial of degree at
most `n`; `dyadicBlock_expand` sums it over a Thue--Morse block. -/
lemma dyadicKernel_taylor (n : ℕ) (x y : ℚ) :
    dyadicKernel n (x + y) =
      ∑ j ∈ Finset.range (n + 1),
        (Nat.choose n j : ℚ) * dyadicKernel (n - j) x * y ^ j := by
  let p := dyadicKernelPolynomial n
  have hpdeg : p.natDegree < n + 1 := by
    exact (dyadicKernelPolynomial_natDegree_le n).trans_lt (Nat.lt_succ_self n)
  have htdeg : (Polynomial.taylor x p).natDegree < n + 1 := by
    rw [Polynomial.natDegree_taylor]
    exact hpdeg
  calc
    dyadicKernel n (x + y) = p.eval (y + x) := by
      change dyadicKernel n (x + y) =
        (dyadicKernelPolynomial n).eval (y + x)
      rw [add_comm, dyadicKernelPolynomial_eval]
    _ = (Polynomial.taylor x p).eval y := by
      rw [Polynomial.taylor_eval]
    _ = ∑ j ∈ Finset.range (n + 1),
          (Polynomial.taylor x p).coeff j * y ^ j :=
      Polynomial.eval_eq_sum_range' htdeg y
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjle : j ≤ n := by simpa using Finset.mem_range.mp hj
      rw [Polynomial.taylor_coeff,
        show p = dyadicKernelPolynomial n by rfl,
        dyadicKernelPolynomial_hasseDeriv n j hjle,
        Polynomial.eval_mul, Polynomial.eval_C,
        dyadicKernelPolynomial_eval]

/-- Value of an odd-index kernel at `x = 1`:
`dyadicKernel (2 q + 1) 1 = (2 q + 1) * 2 ^ (2 q) * moment q`.  The moment
recurrence `moment_succ` is what collapses the sum to this single term.  Used
to evaluate the refinement defect in `dyadicKernelPolynomial_refinement`. -/
lemma dyadicKernel_odd_one (q : ℕ) :
    dyadicKernel (2 * q + 1) 1 =
      ((2 * q + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (2 * q) * moment q := by
  cases q with
  | zero => norm_num [dyadicKernel_eq_sum_range, moment_zero]
  | succ q =>
      rw [dyadicKernel_eq_sum_range]
      have hdiv : (2 * (q + 1) + 1) / 2 + 1 = (q + 1) + 1 := by omega
      rw [hdiv, Finset.sum_range_succ]
      simp only [one_pow, mul_one]
      have hchoose : Nat.choose (2 * (q + 1) + 1) (2 * (q + 1)) =
          2 * (q + 1) + 1 := by
        rw [show 2 * (q + 1) + 1 = (2 * (q + 1)) + 1 by omega,
          Nat.choose_succ_self_right]
      rw [hchoose]
      let S : ℚ := ∑ k ∈ Finset.range (q + 1),
        (Nat.choose (2 * (q + 1) + 1) (2 * k) : ℚ) * moment k
      have hmoment : moment (q + 1) =
          S / (((2 * (q + 1) + 1 : ℕ) : ℚ) *
            ((2 : ℚ) ^ (2 * (q + 1)) - 1)) := by
        rw [moment_succ]
        let g : ℕ → ℚ := fun k =>
          (Nat.choose (2 * (q + 1) + 1) (2 * k) : ℚ) * moment k
        change (∑ k : Fin (q + 1), g k.val) / _ = S / _
        rw [Fin.sum_univ_eq_sum_range g (q + 1)]
      rw [hmoment]
      have hpow : (1 : ℚ) < (2 : ℚ) ^ (2 * (q + 1)) := by
        exact one_lt_pow₀ (by norm_num) (by omega)
      have hden :
          (((2 * (q + 1) + 1 : ℕ) : ℚ) *
            ((2 : ℚ) ^ (2 * (q + 1)) - 1)) ≠ 0 := by positivity
      have hpowden : (2 : ℚ) ^ (2 * (q + 1)) - 1 ≠ 0 :=
        ne_of_gt (sub_pos.mpr hpow)
      change S + ((2 * (q + 1) + 1 : ℕ) : ℚ) * (S / _) =
        ((2 * (q + 1) + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (2 * (q + 1)) * (S / _)
      field_simp [hden, hpowden]
      ring

/-- The kernel has the parity of its index: `dyadicKernel n (-x)` equals
`(-1) ^ n * dyadicKernel n x`, because every exponent `n - 2 k` occurring in
it has the parity of `n`. -/
lemma dyadicKernel_neg (n : ℕ) (x : ℚ) :
    dyadicKernel n (-x) = (-1 : ℚ) ^ n * dyadicKernel n x := by
  rw [dyadicKernel_eq_sum_range, dyadicKernel_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le_div : k ≤ n / 2 := by
    simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hk
  have htwok : 2 * k ≤ n := by
    have := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mp hk_le_div
    omega
  have hparity : Even (n - 2 * k) ↔ Even n := by
    rw [Nat.even_sub htwok]
    simp
  have hsign : (-1 : ℚ) ^ (n - 2 * k) = (-1 : ℚ) ^ n :=
    neg_one_pow_congr hparity
  rw [show -x = (-1 : ℚ) * x by ring, mul_pow, hsign]
  ring

/-- At the origin only the constant term of an even-index kernel survives,
leaving `dyadicKernel (2 q) 0 = moment q`.  This uses the convention
`0 ^ 0 = 1` for the term `k = q`. -/
lemma dyadicKernel_even_zero (q : ℕ) :
    dyadicKernel (2 * q) 0 = moment q := by
  rw [dyadicKernel_eq_sum_range]
  have hdiv : (2 * q) / 2 + 1 = q + 1 := by omega
  rw [hdiv]
  calc
    _ = (Nat.choose (2 * q) (2 * q) : ℚ) * 0 ^ (2 * q - 2 * q) * moment q := by
      apply Finset.sum_eq_single q
      · intro k hk hne
        have hklt : k < q := by
          have : k < q + 1 := Finset.mem_range.mp hk
          omega
        have hpow : 2 * q - 2 * k ≠ 0 := by omega
        simp [hpow]
      · simp
    _ = _ := by simp

/-- Every exponent occurring in an odd-index kernel is positive, so
`dyadicKernel (2 q + 1) 0 = 0`. -/
lemma dyadicKernel_odd_zero (q : ℕ) :
    dyadicKernel (2 * q + 1) 0 = 0 := by
  rw [dyadicKernel_eq_sum_range]
  apply Finset.sum_eq_zero
  intro k hk
  have hk_le : k ≤ q := by
    have : k < (2 * q + 1) / 2 + 1 := Finset.mem_range.mp hk
    omega
  have hpow : 2 * q + 1 - 2 * k ≠ 0 := by omega
  simp [hpow]

/-- The `j = 1` case of `dyadicKernelPolynomial_hasseDeriv`: differentiating
the kernel polynomial lowers its index by one and multiplies by `n + 1`. -/
lemma dyadicKernelPolynomial_derivative_succ (n : ℕ) :
    (dyadicKernelPolynomial (n + 1)).derivative =
      Polynomial.C ((n + 1 : ℕ) : ℚ) * dyadicKernelPolynomial n := by
  simpa using dyadicKernelPolynomial_hasseDeriv (n + 1) 1 (by omega)

/-- The affine substitution `2 X + 1`, the right branch of the refinement. -/
private noncomputable def dyadicAffinePlus : Polynomial ℚ :=
  Polynomial.C 2 * Polynomial.X + Polynomial.C 1

/-- The affine substitution `2 X - 1`, the left branch of the refinement. -/
private noncomputable def dyadicAffineMinus : Polynomial ℚ :=
  Polynomial.C 2 * Polynomial.X - Polynomial.C 1

/-- **Kernel refinement law, polynomial form.**  Composing the index-`n + 1`
kernel polynomial with `2 X + 1` and with `2 X - 1` and subtracting gives
`(n + 1) * 2 ^ (n + 1)` times the index-`n` kernel polynomial.  The induction
compares derivatives, then pins the remaining constant using the parity and
endpoint evaluations above.  `dyadicKernel_has_refinement` evaluates this
identity at a point. -/
lemma dyadicKernelPolynomial_refinement (n : ℕ) :
    (dyadicKernelPolynomial (n + 1)).comp dyadicAffinePlus -
        (dyadicKernelPolynomial (n + 1)).comp dyadicAffineMinus =
      Polynomial.C (((n + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (n + 1)) *
        dyadicKernelPolynomial n := by
  induction n with
  | zero =>
      norm_num [dyadicKernelPolynomial, dyadicAffinePlus, dyadicAffineMinus]
      exact (Polynomial.C_ofNat 2).symm
  | succ n ih =>
      let defect :=
        (dyadicKernelPolynomial (n + 2)).comp dyadicAffinePlus -
          (dyadicKernelPolynomial (n + 2)).comp dyadicAffineMinus -
            Polynomial.C ((((n + 1) + 1 : ℕ) : ℚ) *
              (2 : ℚ) ^ ((n + 1) + 1)) * dyadicKernelPolynomial (n + 1)
      have hderiv : defect.derivative = 0 := by
        have hplus : dyadicAffinePlus.derivative = Polynomial.C 2 := by
          simp [dyadicAffinePlus]
        have hminus : dyadicAffineMinus.derivative = Polynomial.C 2 := by
          simp [dyadicAffineMinus]
        rw [show defect =
          (dyadicKernelPolynomial (n + 2)).comp dyadicAffinePlus -
            (dyadicKernelPolynomial (n + 2)).comp dyadicAffineMinus -
              Polynomial.C ((((n + 1) + 1 : ℕ) : ℚ) *
                (2 : ℚ) ^ ((n + 1) + 1)) *
                  dyadicKernelPolynomial (n + 1) by rfl]
        rw [Polynomial.derivative_sub, Polynomial.derivative_sub,
          Polynomial.derivative_comp, Polynomial.derivative_comp,
          hplus, hminus,
          dyadicKernelPolynomial_derivative_succ,
          Polynomial.mul_comp, Polynomial.mul_comp,
          Polynomial.C_comp, Polynomial.C_comp,
          Polynomial.derivative_C_mul,
          dyadicKernelPolynomial_derivative_succ]
        have hfactor :
            Polynomial.C (2 : ℚ) *
                (Polynomial.C (((n + 1) + 1 : ℕ) : ℚ) *
                  (dyadicKernelPolynomial (n + 1)).comp dyadicAffinePlus) -
              Polynomial.C (2 : ℚ) *
                (Polynomial.C (((n + 1) + 1 : ℕ) : ℚ) *
                  (dyadicKernelPolynomial (n + 1)).comp dyadicAffineMinus) =
            Polynomial.C (2 : ℚ) * Polynomial.C (((n + 1) + 1 : ℕ) : ℚ) *
              ((dyadicKernelPolynomial (n + 1)).comp dyadicAffinePlus -
                (dyadicKernelPolynomial (n + 1)).comp dyadicAffineMinus) := by ring
        rw [hfactor]
        rw [ih]
        have hcoeff :
            (2 : ℚ) * (((n + 1) + 1 : ℕ) : ℚ) *
                ((((n + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (n + 1))) =
              (((((n + 1) + 1 : ℕ) : ℚ) * (2 : ℚ) ^ ((n + 1) + 1))) *
                ((n + 1 : ℕ) : ℚ) := by
          push_cast
          rw [pow_succ]
          ring
        have hcoeffPoly :
            Polynomial.C (2 : ℚ) *
                Polynomial.C (((n + 1) + 1 : ℕ) : ℚ) *
                Polynomial.C (((n + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (n + 1)) =
              Polynomial.C ((((n + 1) + 1 : ℕ) : ℚ) *
                  (2 : ℚ) ^ ((n + 1) + 1)) *
                Polynomial.C ((n + 1 : ℕ) : ℚ) := by
          calc
            _ = Polynomial.C
                ((2 : ℚ) * (((n + 1) + 1 : ℕ) : ℚ) *
                  (((n + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (n + 1))) := by
                    repeat rw [← Polynomial.C_mul]
            _ = Polynomial.C
                (((((n + 1) + 1 : ℕ) : ℚ) * (2 : ℚ) ^ ((n + 1) + 1)) *
                  ((n + 1 : ℕ) : ℚ)) := by rw [hcoeff]
            _ = _ := by rw [Polynomial.C_mul]
        calc
          _ = (Polynomial.C (2 : ℚ) *
                  Polynomial.C (((n + 1) + 1 : ℕ) : ℚ) *
                  Polynomial.C (((n + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (n + 1))) *
                dyadicKernelPolynomial n -
              (Polynomial.C ((((n + 1) + 1 : ℕ) : ℚ) *
                  (2 : ℚ) ^ ((n + 1) + 1)) *
                Polynomial.C ((n + 1 : ℕ) : ℚ)) *
                dyadicKernelPolynomial n := by ring
          _ = 0 := by rw [hcoeffPoly]; ring
      have hconst := Polynomial.eq_C_of_derivative_eq_zero hderiv
      have heval : defect.eval 0 = 0 := by
        have hplus0 : dyadicAffinePlus.eval 0 = 1 := by
          norm_num [dyadicAffinePlus]
        have hminus0 : dyadicAffineMinus.eval 0 = -1 := by
          norm_num [dyadicAffineMinus]
        simp only [defect, Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_C, Polynomial.eval_comp, hplus0, hminus0,
          dyadicKernelPolynomial_eval]
        obtain ⟨q, hq | hq⟩ := Nat.even_or_odd' n
        · subst n
          rw [dyadicKernel_neg, dyadicKernel_odd_zero]
          have heven : (-1 : ℚ) ^ (2 * q + 2) = 1 := by
            rw [show 2 * q + 2 = 2 * (q + 1) by omega, pow_mul]
            norm_num
          rw [heven]
          ring
        · subst n
          rw [dyadicKernel_neg]
          have hoddIndex : 2 * q + 1 + 2 = 2 * (q + 1) + 1 := by omega
          have hevenIndex : 2 * q + 1 + 1 = 2 * (q + 1) := by omega
          rw [hoddIndex, hevenIndex,
            dyadicKernel_odd_one (q + 1), dyadicKernel_even_zero (q + 1)]
          have hodd : (-1 : ℚ) ^ (2 * (q + 1) + 1) = -1 := by
            rw [pow_succ, pow_mul]
            norm_num
          rw [hodd]
          push_cast
          rw [pow_succ]
          ring
      have hzero : defect = 0 := by
        calc
          defect = Polynomial.C (defect.coeff 0) := hconst
          _ = Polynomial.C (defect.eval 0) := by rw [Polynomial.coeff_zero_eq_eval_zero]
          _ = 0 := by rw [heval, Polynomial.C_0]
      exact sub_eq_zero.mp hzero

/-- The normalization absorbs exactly the constant produced by the kernel
refinement law: `dyadicScale (n + 1) * (n + 1) * 2 ^ (n + 1) = dyadicScale n`.
This cancellation is what makes `fabiusDyadic` invariant under refining the
dyadic grid. -/
lemma dyadicScale_succ_mul (n : ℕ) :
    dyadicScale (n + 1) * ((n + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (n + 1) =
      dyadicScale n := by
  have hchoose : (n + 2).choose 2 = (n + 1).choose 2 + (n + 1) := by
    rw [show n + 2 = (n + 1) + 1 by omega,
      show 2 = 1 + 1 by omega, Nat.choose_succ_succ]
    simp [Nat.add_comm]
  rw [dyadicScale, dyadicScale, show n + 1 + 1 = n + 2 by omega, hchoose,
    Nat.factorial_succ]
  push_cast
  have hexp :
      -((Nat.choose (n + 1) 2 : ℤ) + ((n : ℤ) + 1)) =
        -(Nat.choose (n + 1) 2 : ℤ) - ((n : ℤ) + 1) := by ring
  rw [hexp, zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0)]
  simp only [div_eq_mul_inv]
  rw [mul_inv]
  have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
  have hp : (2 : ℚ) ^ (n + 1) ≠ 0 := by positivity
  have hz : (2 : ℚ) ^ ((n : ℤ) + 1) = (2 : ℚ) ^ (n + 1) := by
    rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by omega, zpow_natCast]
  rw [hz]
  calc
    _ = (2 : ℚ) ^ (-(Nat.choose (n + 1) 2 : ℤ)) *
          (n.factorial : ℚ)⁻¹ *
          (((n : ℚ) + 1)⁻¹ * ((n : ℚ) + 1)) *
          (((2 : ℚ) ^ (n + 1))⁻¹ * (2 : ℚ) ^ (n + 1)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hn, inv_mul_cancel₀ hp]; ring

/-- Regrouping of a single Taylor coefficient, for `j ≤ n`:
`dyadicScale n * Nat.choose n j * (2 r) ^ j` equals
`2 ^ Nat.choose (j + 1) 2 * (r / 2 ^ n) ^ j / j ! * dyadicScale (n - j)`.
This converts the block expansion into the shape evaluated by
`fabiusTaylorHorner`; the exponent bookkeeping is `choose_add_succ_two`. -/
lemma dyadicScale_choose_taylor (n j : ℕ) (hj : j ≤ n) (r : ℚ) :
    dyadicScale n * (Nat.choose n j : ℚ) * ((2 : ℚ) * r) ^ j =
      (2 : ℚ) ^ (j + 1).choose 2 *
        (r / (2 : ℚ) ^ n) ^ j / j.factorial * dyadicScale (n - j) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [Nat.add_sub_cancel_left]
  simp only [dyadicScale]
  rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast, div_pow]
  have hfac := Nat.choose_mul_factorial_mul_factorial (n := j + m) (k := j) hj
  have hchoose := choose_add_succ_two m j
  have hpow0 : (2 : ℚ) ^ (j + m + 1).choose 2 ≠ 0 := by positivity
  have hpowm : (2 : ℚ) ^ (m + 1).choose 2 ≠ 0 := by positivity
  have hpown : (2 : ℚ) ^ (j + m) ≠ 0 := by positivity
  field_simp [hpow0, hpowm, hpown]
  have hfacNat : Nat.choose (j + m) j * j.factorial * m.factorial =
      (j + m).factorial := by simpa using hfac
  have hfacQ : (Nat.choose (j + m) j : ℚ) * j.factorial * m.factorial =
      ((j + m).factorial : ℚ) := by exact_mod_cast hfacNat
  have hchoose' : Nat.choose (j + m + 1) 2 =
      Nat.choose (m + 1) 2 + m * j + Nat.choose (j + 1) 2 := by
    simpa [add_comm] using hchoose
  have hjprod : j * j + j = 2 * Nat.choose (j + 1) 2 := by
    calc
      j * j + j = j * (j + 1) := by ring
      _ = _ := (two_mul_choose_succ_two j).symm
  have hexponent :
      j + (j + m) * j + Nat.choose (m + 1) 2 =
        Nat.choose (j + m + 1) 2 + Nat.choose (j + 1) 2 := by
    rw [show (j + m) * j = j * j + m * j by ring, hchoose']
    omega
  have hpowers :
      (2 : ℚ) ^ j * ((2 : ℚ) ^ (j + m)) ^ j *
          (2 : ℚ) ^ (m + 1).choose 2 =
        (2 : ℚ) ^ (j + m + 1).choose 2 *
          (2 : ℚ) ^ (j + 1).choose 2 := by
    rw [← pow_mul]
    calc
      (2 : ℚ) ^ j * 2 ^ ((j + m) * j) * 2 ^ (m + 1).choose 2 =
          2 ^ (j + (j + m) * j + (m + 1).choose 2) := by
            rw [← pow_add, ← pow_add]
      _ = 2 ^ ((j + m + 1).choose 2 + (j + 1).choose 2) := by rw [hexponent]
      _ = _ := by rw [pow_add]
  rw [mul_pow]
  calc
    _ = ((Nat.choose (j + m) j : ℚ) * j.factorial * m.factorial) *
          ((2 : ℚ) ^ j * ((2 : ℚ) ^ (j + m)) ^ j *
            (2 : ℚ) ^ (m + 1).choose 2) * r ^ j := by ring
    _ = ((j + m).factorial : ℚ) *
          ((2 : ℚ) ^ (j + m + 1).choose 2 *
            (2 : ℚ) ^ (j + 1).choose 2) * r ^ j := by rw [hfacQ, hpowers]
    _ = _ := by ring

/-- A complete Thue--Morse block annihilates a kernel of lower index: for
`n < b` the signed sum of `dyadicKernel n (x - 2 h)` over `h < 2 ^ b` vanishes,
for every `x`.  Each monomial has degree at most `n < b`, so
`thueMorse_affine_power_sum_eq_zero` applies term by term.  This is what
truncates the expansion in `dyadicBlock_expand_truncated`. -/
lemma thueMorse_kernel_block_eq_zero (n b : ℕ) (hn : n < b) (x : ℚ) :
    (∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
      dyadicKernel n (x - 2 * h.val)) = 0 := by
  simp_rw [dyadicKernel, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  have hdegree : n - 2 * k.val < b := (Nat.sub_le n _).trans_lt hn
  have hzero := thueMorse_affine_power_sum_eq_zero b (n - 2 * k.val)
    hdegree x (-2)
  have heq :
      (∑ h : Fin (2 ^ b),
        (thueMorseSign h.val : ℚ) *
          ((Nat.choose n (2 * k.val) : ℚ) *
            (x - 2 * (h.val : ℚ)) ^ (n - 2 * k.val) * moment k.val)) =
        ((Nat.choose n (2 * k.val) : ℚ) * moment k.val) *
          ∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
            (x + (-2) * (h.val : ℚ)) ^ (n - 2 * k.val) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    ring
  rw [heq, hzero, mul_zero]

/-- Taylor-expands the scaled signed block sum in the displacement `2 r`:
adding `2 r` to every kernel argument spreads the sum over the `n + 1` terms
of `dyadicKernel_taylor`, each carrying its own signed block sum at kernel
index `n - j`. -/
lemma dyadicBlock_expand (n b : ℕ) (r : ℚ) :
    dyadicScale n *
        (∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
          dyadicKernel n
            (((2 : ℚ) * 2 ^ b - 2 * h.val - 1) + 2 * r)) =
      ∑ j ∈ Finset.range (n + 1),
        dyadicScale n * (Nat.choose n j : ℚ) * ((2 : ℚ) * r) ^ j *
          (∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
            dyadicKernel (n - j) ((2 : ℚ) * 2 ^ b - 2 * h.val - 1)) := by
  simp_rw [dyadicKernel_taylor]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro h hh
  ring

/-- The expansion of `dyadicBlock_expand`, truncated to `j ≤ n - b` under the
hypothesis `b ≤ n`.  The discarded terms vanish because their kernel index
`n - j` drops below `b`, where `thueMorse_kernel_block_eq_zero` applies. -/
lemma dyadicBlock_expand_truncated (n b : ℕ) (hb : b ≤ n) (r : ℚ) :
    dyadicScale n *
        (∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
          dyadicKernel n
            (((2 : ℚ) * 2 ^ b - 2 * h.val - 1) + 2 * r)) =
      ∑ j ∈ Finset.range (n - b + 1),
        dyadicScale n * (Nat.choose n j : ℚ) * ((2 : ℚ) * r) ^ j *
          (∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
            dyadicKernel (n - j) ((2 : ℚ) * 2 ^ b - 2 * h.val - 1)) := by
  rw [dyadicBlock_expand]
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right (Nat.sub_le n b) 1))
  intro j hj hnot
  have hjle : j ≤ n := by simpa using Finset.mem_range.mp hj
  have hdlt : n - b < j := by
    simpa only [Finset.mem_range, Nat.not_lt, Nat.add_one_le_iff] using hnot
  have hdegree : n - j < b := by omega
  have hzero := thueMorse_kernel_block_eq_zero (n - j) b hdegree
    ((2 : ℚ) * 2 ^ b - 1)
  have hzero' :
      (∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
        dyadicKernel (n - j) ((2 : ℚ) * 2 ^ b - 2 * h.val - 1)) = 0 := by
    convert hzero using 1
    all_goals ring_nf
  rw [hzero', mul_zero]

/-- The kernel refinement law as a `Prop`: for all `n` and all rational `x`,
`dyadicKernel (n + 1) (2 x + 1) - dyadicKernel (n + 1) (2 x - 1)` equals
`(n + 1) * 2 ^ (n + 1) * dyadicKernel n x`.  Packaging it this way lets the
consequences below be stated as hypothetical implications; it is discharged
once, by `dyadicKernel_has_refinement`. -/
def DyadicKernelHasRefinement : Prop :=
  ∀ n : ℕ, ∀ x : ℚ,
    dyadicKernel (n + 1) (2 * x + 1) -
        dyadicKernel (n + 1) (2 * x - 1) =
      ((n + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (n + 1) * dyadicKernel n x

/-- The refinement law holds, by evaluating the polynomial identity
`dyadicKernelPolynomial_refinement` at each rational point. -/
theorem dyadicKernel_has_refinement : DyadicKernelHasRefinement := by
  intro n x
  have h := congrArg (Polynomial.eval x) (dyadicKernelPolynomial_refinement n)
  simpa [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_comp, dyadicAffinePlus, dyadicAffineMinus,
    dyadicKernelPolynomial_eval] using h

/-- Unfolds equation (32) into the normalization `dyadicScale n` times the
signed kernel sum, the shape every proof in this file works with.  It holds by
`rfl`, so rewriting with it in either direction is free. -/
lemma fabiusDyadic_eq_scale_sum (n a : ℕ) :
    fabiusDyadic n a = dyadicScale n *
      ∑ h : Fin a, (thueMorseSign h.val : ℚ) *
        dyadicKernel n ((2 : ℚ) * a - 2 * h.val - 1) := by
  rfl

/-- **Thue--Morse block concatenation.**  Splitting an index as a multiple of
`2 ^ k` plus a residue below `2 ^ k` splits its Thue--Morse sign into the
product of the signs of the two parts, because the binary expansions of
`h * 2 ^ k` and of `r` occupy disjoint digit ranges.

This multiplicativity is what makes every dyadic Fabius numerator
quasi-periodic.  It is public because the uniform-spline and q-binomial layers
need it too; all three had previously proved it privately. -/
theorem thueMorseSign_block_concat
    (k h r : ℕ) (hr : r < 2 ^ k) :
    thueMorseSign (h * 2 ^ k + r) =
      thueMorseSign h * thueMorseSign r := by
  induction k generalizing h r with
  | zero =>
      have : r = 0 := by omega
      subst r
      norm_num [thueMorseSign, binaryWeight]
  | succ k ih =>
      rcases r.even_or_odd with ⟨r, rfl⟩ | ⟨r, rfl⟩
      · have hr' : r < 2 ^ k := by
          rw [pow_succ] at hr
          omega
        rw [show r + r = 2 * r by omega]
        rw [show h * 2 ^ (k + 1) + 2 * r =
            2 * (h * 2 ^ k + r) by rw [pow_succ]; ring,
          thueMorseSign_two_mul, thueMorseSign_two_mul, ih h r hr']
      · have hr' : r < 2 ^ k := by
          rw [pow_succ] at hr
          omega
        rw [show h * 2 ^ (k + 1) + (2 * r + 1) =
            2 * (h * 2 ^ k + r) + 1 by rw [pow_succ]; ring,
          thueMorseSign_two_mul_add_one,
          thueMorseSign_two_mul_add_one, ih h r hr']
        ring

/-- **Block decomposition of a range sum.**  A sum over `Finset.range (m * p)`
is the sum of `m` consecutive blocks of length `p`.  Stated over an arbitrary
`AddCommMonoid`, since the corpus applies it over the rationals, over the
reals, and over formal power series.

Mathlib has no equivalent: it has `Finset.sum_range_add` for a two-part split
and `Finset.sum_range_add_sum_Ico` for a range/interval split, but nothing
that splits `range (m * p)` into `m` blocks for symbolic `m` and `p`.  A
tree-wide search of Mathlib for `range (a * b)` with two symbolic variables
finds no occurrence at all, and `Combinatorics.SimpleGraph.Extremal.Turan`
does this decomposition by hand.  So do not replace this by an import. -/
theorem sum_range_block_decomposition
    {A : Type*} [AddCommMonoid A] (f : ℕ → A) (m p : ℕ) :
    (∑ j ∈ Finset.range (m * p), f j) =
      ∑ h ∈ Finset.range m, ∑ r ∈ Finset.range p, f (h * p + r) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih,
        Finset.sum_range_succ]

/-- **Block decomposition with a partial final block.**  The variant of
`sum_range_block_decomposition` for a range whose length `m * p + r` need not
be a multiple of the block length `p`. -/
theorem sum_range_block_decomposition_with_remainder
    {A : Type*} [AddCommMonoid A] (f : ℕ → A) (m p r : ℕ) :
    (∑ j ∈ Finset.range (m * p + r), f j) =
      (∑ h ∈ Finset.range m,
        ∑ j ∈ Finset.range p, f (h * p + j)) +
      ∑ j ∈ Finset.range r, f (m * p + j) := by
  rw [Finset.sum_range_add, sum_range_block_decomposition]

/-- Equation (32) transforms by the Thue--Morse sign when its numerator is
translated by a complete length-`2^(n+1)` block. -/
theorem fabiusDyadic_block_translate (n block residue : ℕ)
    (hresidue : residue < 2 ^ (n + 1)) :
    fabiusDyadic n (block * 2 ^ (n + 1) + residue) =
      (thueMorseSign block : ℚ) * fabiusDyadic n residue := by
  rw [fabiusDyadic_eq_scale_sum, fabiusDyadic_eq_scale_sum]
  let scale : ℚ := dyadicScale n
  let period : ℕ := 2 ^ (n + 1)
  let a : ℕ := block * period + residue
  let f : ℕ → ℚ := fun h =>
    (thueMorseSign h : ℚ) *
      dyadicKernel n ((2 : ℚ) * a - 2 * h - 1)
  change scale * (∑ h : Fin a, f h.val) =
    (thueMorseSign block : ℚ) *
      (scale * ∑ h : Fin residue,
        (thueMorseSign h.val : ℚ) *
          dyadicKernel n ((2 : ℚ) * residue - 2 * h.val - 1))
  rw [Fin.sum_univ_eq_sum_range f a,
    sum_range_block_decomposition_with_remainder f block period residue]
  have hfull :
      (∑ q ∈ Finset.range block,
        ∑ j ∈ Finset.range period, f (q * period + j)) = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    have hblockzero := thueMorse_kernel_block_eq_zero n (n + 1)
      (Nat.lt_succ_self n)
      ((2 : ℚ) * a - 2 * (q * period : ℕ) - 1)
    calc
      (∑ j ∈ Finset.range period, f (q * period + j)) =
          (thueMorseSign q : ℚ) *
            ∑ j ∈ Finset.range period,
              (thueMorseSign j : ℚ) *
                dyadicKernel n
                  ((2 : ℚ) * a - 2 * (q * period : ℕ) - 1 - 2 * j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hjlt : j < period := Finset.mem_range.mp hj
        dsimp only [f]
        rw [thueMorseSign_block_concat (n + 1) q j
          (by simpa [period] using hjlt)]
        push_cast
        ring_nf
      _ = 0 := by
        rw [← Fin.sum_univ_eq_sum_range
          (fun j => (thueMorseSign j : ℚ) *
            dyadicKernel n
              ((2 : ℚ) * a - 2 * (q * period : ℕ) - 1 - 2 * j)) period,
          hblockzero, mul_zero]
  rw [hfull, zero_add]
  rw [Fin.sum_univ_eq_sum_range
    (fun h => (thueMorseSign h : ℚ) *
      dyadicKernel n ((2 : ℚ) * residue - 2 * h - 1)) residue]
  calc
    scale * ∑ j ∈ Finset.range residue, f (block * period + j) =
        scale * ((thueMorseSign block : ℚ) *
          ∑ j ∈ Finset.range residue,
            (thueMorseSign j : ℚ) *
              dyadicKernel n ((2 : ℚ) * residue - 2 * j - 1)) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjlt : j < period := (Finset.mem_range.mp hj).trans hresidue
      dsimp only [f, a]
      rw [thueMorseSign_block_concat (n + 1) block j
        (by simpa [period] using hjlt)]
      push_cast
      dsimp only [period]
      ring_nf
    _ = _ := by ring

/-- The closed dyadic formula vanishes at the right endpoint `2`. -/
@[simp]
theorem fabiusDyadic_two_pow_succ (n : ℕ) :
    fabiusDyadic n (2 ^ (n + 1)) = 0 := by
  simpa [fabiusDyadic_arg_zero] using
    fabiusDyadic_block_translate n 1 0 (by positivity)

/-- The block-translation law also holds at the right endpoint of a block.
Both sides then vanish, so callers may use the natural closed-block bound. -/
theorem fabiusDyadic_block_translate_le (n block residue : ℕ)
    (hresidue : residue ≤ 2 ^ (n + 1)) :
    fabiusDyadic n (block * 2 ^ (n + 1) + residue) =
      (thueMorseSign block : ℚ) * fabiusDyadic n residue := by
  rcases hresidue.eq_or_lt with rfl | hresidue
  · calc
      fabiusDyadic n (block * 2 ^ (n + 1) + 2 ^ (n + 1)) =
          fabiusDyadic n ((block + 1) * 2 ^ (n + 1) + 0) := by
        congr 1
        ring
      _ = (thueMorseSign (block + 1) : ℚ) * fabiusDyadic n 0 :=
        fabiusDyadic_block_translate n (block + 1) 0 (by positivity)
      _ = 0 := by rw [fabiusDyadic_arg_zero, mul_zero]
      _ = (thueMorseSign block : ℚ) * fabiusDyadic n (2 ^ (n + 1)) := by
        rw [fabiusDyadic_two_pow_succ, mul_zero]
  · exact fabiusDyadic_block_translate n block residue hresidue

/-- **Canonical block normal form.**  Dividing an arbitrary numerator `a`
by the natural period `2 ^ (n + 1)` separates its closed-form dyadic value
into the Thue--Morse sign of the block quotient and the value at the canonical
remainder:

`fabiusDyadic n a = thueMorseSign (a / 2 ^ (n + 1)) *
  fabiusDyadic n (a % 2 ^ (n + 1))`.

This includes level `n = 0`, the numerator `a = 0`, and exact block multiples;
in the latter case the remainder is zero and both sides vanish. -/
theorem fabiusDyadic_eq_block_sign_mul_mod (n a : ℕ) :
    fabiusDyadic n a =
      (thueMorseSign (a / 2 ^ (n + 1)) : ℚ) *
        fabiusDyadic n (a % 2 ^ (n + 1)) := by
  have hperiod : 0 < 2 ^ (n + 1) := by positivity
  have hdecomp :
      a / 2 ^ (n + 1) * 2 ^ (n + 1) + a % 2 ^ (n + 1) = a := by
    calc
      a / 2 ^ (n + 1) * 2 ^ (n + 1) + a % 2 ^ (n + 1) =
          2 ^ (n + 1) * (a / 2 ^ (n + 1)) + a % 2 ^ (n + 1) := by
        rw [Nat.mul_comm]
      _ = a := Nat.div_add_mod a (2 ^ (n + 1))
  simpa only [hdecomp] using
    fabiusDyadic_block_translate n (a / 2 ^ (n + 1))
      (a % 2 ^ (n + 1)) (Nat.mod_lt a hperiod)

/-- Assuming the kernel refinement law, equation (32) is consistent under
refining the dyadic grid: `fabiusDyadic (n + 1) (2 a) = fabiusDyadic n a`, so
the value depends only on the rational `a / 2 ^ n`.  Callers supply
`dyadicKernel_has_refinement` for `hk`. -/
lemma fabiusDyadic_refine_of_kernel (hk : DyadicKernelHasRefinement)
    (n a : ℕ) :
    fabiusDyadic (n + 1) (2 * a) = fabiusDyadic n a := by
  rw [fabiusDyadic_eq_scale_sum, fabiusDyadic_eq_scale_sum]
  push_cast
  let f : ℕ → ℚ := fun h =>
    dyadicKernel (n + 1) ((2 : ℚ) * (2 * a) - 2 * h - 1)
  change dyadicScale (n + 1) *
      (∑ h : Fin (2 * a), (thueMorseSign h.val : ℚ) * f h.val) =
    dyadicScale n *
      ∑ h : Fin a, (thueMorseSign h.val : ℚ) *
        dyadicKernel n ((2 : ℚ) * a - 2 * h.val - 1)
  rw [thueMorse_sum_two_mul a f]
  have hterms :
      (∑ j : Fin a, (thueMorseSign j.val : ℚ) *
          (f (2 * j.val) - f (2 * j.val + 1))) =
        ((n + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (n + 1) *
          ∑ j : Fin a, (thueMorseSign j.val : ℚ) *
            dyadicKernel n ((2 : ℚ) * a - 2 * j.val - 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hrefine := hk n ((2 : ℚ) * a - 2 * j.val - 1)
    simp only [f]
    push_cast
    have hdiff :
        dyadicKernel (n + 1)
            (2 * (2 * (a : ℚ)) - 2 * (2 * (j.val : ℚ)) - 1) -
          dyadicKernel (n + 1)
            (2 * (2 * (a : ℚ)) - 2 * (2 * (j.val : ℚ) + 1) - 1) =
          ((n + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (n + 1) *
            dyadicKernel n (2 * (a : ℚ) - 2 * (j.val : ℚ) - 1) := by
      convert hrefine using 1; ring_nf
    rw [hdiff]
    push_cast
    ring
  rw [hterms]
  rw [← mul_assoc, ← mul_assoc, dyadicScale_succ_mul]

/-- Iterating `fabiusDyadic_refine_of_kernel` `b` times: refining the grid by
a factor `2 ^ b` leaves the closed-form value unchanged. -/
lemma fabiusDyadic_refine_pow_of_kernel (hk : DyadicKernelHasRefinement)
    (m b a : ℕ) :
    fabiusDyadic (m + b) (2 ^ b * a) = fabiusDyadic m a := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [show m + (b + 1) = (m + b) + 1 by omega,
        pow_succ', mul_assoc, fabiusDyadic_refine_of_kernel hk, ih]

/-- The case `a = 1` of `fabiusDyadic_refine_pow_of_kernel`: every grid
representation of `2 ^ (-m)` gives the tabulated value
`fabiusAtInverseTwoPow m`. -/
lemma fabiusDyadic_pow_two_eq_inverse_of_kernel (hk : DyadicKernelHasRefinement)
    (m b : ℕ) :
    fabiusDyadic (m + b) (2 ^ b) = fabiusAtInverseTwoPow m := by
  simpa [fabiusAtInverseTwoPow] using
    fabiusDyadic_refine_pow_of_kernel hk m b 1

/-- Identifies the constant term of the block expansion: the scaled signed
kernel sum over a complete block `h < 2 ^ b`, with kernel arguments
`2 * 2 ^ b - 2 h - 1`, is `fabiusAtInverseTwoPow m`.  Same content as
`fabiusDyadic_pow_two_eq_inverse_of_kernel`, written in the summed form that
`dyadicBlock_eq_taylor_sum` consumes. -/
lemma dyadic_block_base_eq_inverse_of_kernel (hk : DyadicKernelHasRefinement)
    (m b : ℕ) :
    dyadicScale (m + b) *
        (∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
          dyadicKernel (m + b) ((2 : ℚ) * 2 ^ b - 2 * h.val - 1)) =
      fabiusAtInverseTwoPow m := by
  calc
    _ = fabiusDyadic (m + b) (2 ^ b) := by
      rw [fabiusDyadic_eq_scale_sum]
      push_cast
      rfl
    _ = _ := fabiusDyadic_pow_two_eq_inverse_of_kernel hk m b

/-- **The block Taylor identity.**  For `b ≤ n` and any rational `r`, the
scaled signed kernel sum over the block `h < 2 ^ b`, with its argument
displaced by `2 r`, equals the finite sum over `j ≤ n - b` of
`2 ^ Nat.choose (j + 1) 2 * fabiusAtInverseTwoPow (n - b - j) *
(r / 2 ^ n) ^ j / j !`.  Every coefficient is a tabulated inverse-power value,
which is what makes the Horner evaluator exact.  `GlobalDyadic` and
`DyadicAnalytic` use it as well as the correctness proof below. -/
lemma dyadicBlock_eq_taylor_sum (n b : ℕ) (hb : b ≤ n) (r : ℚ) :
    dyadicScale n *
        (∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
          dyadicKernel n
            (((2 : ℚ) * 2 ^ b - 2 * h.val - 1) + 2 * r)) =
      ∑ j ∈ Finset.range (n - b + 1),
        (2 : ℚ) ^ (j + 1).choose 2 * fabiusAtInverseTwoPow (n - b - j) *
          (r / (2 : ℚ) ^ n) ^ j / j.factorial := by
  rw [dyadicBlock_expand_truncated n b hb r]
  apply Finset.sum_congr rfl
  intro j hj
  have hjleD : j ≤ n - b := by simpa using Finset.mem_range.mp hj
  have hjle : j ≤ n := hjleD.trans (Nat.sub_le n b)
  have hindex : n - j = (n - b - j) + b := by omega
  have hbase := dyadic_block_base_eq_inverse_of_kernel
    dyadicKernel_has_refinement (n - b - j) b
  have hbase' :
      dyadicScale (n - j) *
          (∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
            dyadicKernel (n - j) ((2 : ℚ) * 2 ^ b - 2 * h.val - 1)) =
        fabiusAtInverseTwoPow (n - b - j) := by
    simpa [hindex] using hbase
  have hscale := dyadicScale_choose_taylor n j hjle r
  calc
    dyadicScale n * (Nat.choose n j : ℚ) * ((2 : ℚ) * r) ^ j *
          (∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
            dyadicKernel (n - j) ((2 : ℚ) * 2 ^ b - 2 * h.val - 1)) =
        (dyadicScale n * (Nat.choose n j : ℚ) * ((2 : ℚ) * r) ^ j) *
          (∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
            dyadicKernel (n - j) ((2 : ℚ) * 2 ^ b - 2 * h.val - 1)) := by ring
    _ = ((2 : ℚ) ^ (j + 1).choose 2 *
          (r / (2 : ℚ) ^ n) ^ j / j.factorial * dyadicScale (n - j)) *
          (∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
            dyadicKernel (n - j) ((2 : ℚ) * 2 ^ b - 2 * h.val - 1)) := by
      rw [hscale]
    _ = ((2 : ℚ) ^ (j + 1).choose 2 *
          (r / (2 : ℚ) ^ n) ^ j / j.factorial) *
        (dyadicScale (n - j) *
          (∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
            dyadicKernel (n - j) ((2 : ℚ) * 2 ^ b - 2 * h.val - 1))) := by ring
    _ = _ := by rw [hbase']; ring

/-- The precomputed table contains the exact values `F(2⁻ᵏ)`. -/
theorem fabiusInversePowTwoTable_get (maxExponent k : ℕ) (hk : k ≤ maxExponent) :
    (fabiusInversePowTwoTable maxExponent)[k]? = some (fabiusAtInverseTwoPow k) := by
  induction maxExponent generalizing k with
  | zero =>
      have hk0 : k = 0 := by omega
      subst k
      simp [fabiusInversePowTwoTable,
        fabiusAtInverseTwoPow_eq_halfMoment, halfMomentFabiusValue]
  | succ n ih =>
      rw [fabiusInversePowTwoTable, Array.getElem?_push,
        fabiusInversePowTwoTable_size]
      by_cases hlast : k = n + 1
      · subst k
        simp only [ite_true]
        congr 1
        rw [fabiusAtInverseTwoPow_eq_halfMoment,
          halfMomentFabiusValue_succ]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        rw [ih j.val (by omega)]
        simp [fabiusAtInverseTwoPow_eq_halfMoment]
      · rw [if_neg hlast]
        exact ih k (by omega)

/-- The Horner routine evaluates the Taylor polynomial in Proposition 10. -/
theorem fabiusTaylorHorner_eq_sum (maxExponent order : ℕ)
    (horder : order ≤ maxExponent) (offset : ℚ) :
    fabiusTaylorHorner (fabiusInversePowTwoTable maxExponent) order offset =
      ∑ k ∈ range (order + 1),
        (2 : ℚ) ^ (k + 1).choose 2 * fabiusAtInverseTwoPow (order - k) *
          offset ^ k / k.factorial := by
  have hzero : fabiusInversePowTwoTableValue
      (fabiusInversePowTwoTable maxExponent) 0 = 1 := by
    rw [fabiusInversePowTwoTableValue,
      fabiusInversePowTwoTable_get maxExponent 0 (Nat.zero_le _)]
    simp [fabiusAtInverseTwoPow_eq_halfMoment, halfMomentFabiusValue]
  change fabiusTaylorHorner.go (fabiusInversePowTwoTable maxExponent)
      order offset order = _
  have hgo := fabiusTaylorHorner_go_eq_sum
    (fabiusInversePowTwoTable maxExponent) hzero offset order 0
  simp only [Nat.zero_add] at hgo
  rw [hgo]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k ≤ order := by simpa using hk
  have hlookup := fabiusInversePowTwoTable_get maxExponent (order - k)
    (le_trans (Nat.sub_le order k) horder)
  rw [fabiusInversePowTwoTableValue, hlookup]
  norm_num

/-- Splitting at a binary leading digit cancels the entire remainder block
against the value at that remainder. -/
lemma fabiusDyadic_add_remainder_eq_block (n b r : ℕ) (hr : r ≤ 2 ^ b) :
    fabiusDyadic n (2 ^ b + r) + fabiusDyadic n r =
      dyadicScale n *
        ∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
          dyadicKernel n ((2 : ℚ) * (2 ^ b + r) - 2 * h.val - 1) := by
  rw [fabiusDyadic_eq_scale_sum, fabiusDyadic_eq_scale_sum]
  push_cast
  rw [thueMorse_sum_split b r hr
    (fun h => dyadicKernel n ((2 : ℚ) * (2 ^ b + r) - 2 * h - 1))]
  have hshift :
      (∑ j : Fin r, (thueMorseSign j.val : ℚ) *
          dyadicKernel n
            ((2 : ℚ) * (2 ^ b + r) - 2 * (2 ^ b + j.val) - 1)) =
        ∑ j : Fin r, (thueMorseSign j.val : ℚ) *
          dyadicKernel n ((2 : ℚ) * r - 2 * j.val - 1) := by
    apply Finset.sum_congr rfl
    intro j hj
    congr 2
    ring
  push_cast
  rw [hshift]
  ring

/-- Data attached to the leading binary bit of `a`: with `b = Nat.log2 a` and
`r = a - 2 ^ b` one has `b ≤ n`, `r < 2 ^ b`, and `a = 2 ^ b + r`.  These are
exactly the side conditions each step of the bit recursion needs; both `0 < a`
and `a ≤ 2 ^ n` are used. -/
lemma leading_bit_data (n a : ℕ) (ha0 : 0 < a) (ha : a ≤ 2 ^ n) :
    let b := Nat.log2 a
    let r := a - 2 ^ b
    b ≤ n ∧ r < 2 ^ b ∧ a = 2 ^ b + r := by
  dsimp
  have hane : a ≠ 0 := Nat.ne_of_gt ha0
  have hpow_le : 2 ^ Nat.log2 a ≤ a := Nat.log2_self_le hane
  have ha_lt_next : a < 2 ^ (Nat.log2 a + 1) := Nat.lt_log2_self
  have htwo_pow_lt : 2 ^ n < 2 ^ (n + 1) := by
    exact Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self n)
  have hlog_lt : Nat.log2 a < n + 1 :=
    (Nat.log2_lt hane).2 (ha.trans_lt htwo_pow_lt)
  have hb_le : Nat.log2 a ≤ n := by omega
  have hr_lt : a - 2 ^ Nat.log2 a < 2 ^ Nat.log2 a := by
    rw [pow_succ] at ha_lt_next
    omega
  exact ⟨hb_le, hr_lt, (Nat.add_sub_of_le hpow_le).symm⟩

/-- The one remaining polynomial identity after all bit-manipulation and
recursive cancellation have been discharged. -/
def FabiusDyadicHasBlockTaylor (values : Array ℚ) (n : ℕ) : Prop :=
  ∀ b r : ℕ, b ≤ n → r < 2 ^ b →
    dyadicScale n *
        (∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
          dyadicKernel n ((2 : ℚ) * (2 ^ b + r) - 2 * h.val - 1)) =
      fabiusTaylorHorner values (n - b) ((r : ℚ) / (2 : ℚ) ^ n)

/-- The block Taylor identity for a table of values implies the single-step
bit recurrence for that table: splitting `a` at its leading bit, cancelling the
remainder block by `fabiusDyadic_add_remainder_eq_block`, and rewriting the
block by `hblock` gives exactly the recurrence. -/
theorem blockTaylor_implies_bitRecurrence (values : Array ℚ) (n : ℕ)
    (hblock : FabiusDyadicHasBlockTaylor values n) :
    FabiusDyadicHasBitRecurrence values n := by
  intro a ha0 ha
  dsimp only
  obtain ⟨hb_le, hr_lt, ha_split⟩ := leading_bit_data n a ha0 ha
  let b := Nat.log2 a
  let r := a - 2 ^ b
  have hcancel := fabiusDyadic_add_remainder_eq_block n b r hr_lt.le
  have htaylor := hblock b r hb_le hr_lt
  change fabiusDyadic n a =
    fabiusTaylorHorner values (n - b) ((r : ℚ) / (2 : ℚ) ^ n) -
      fabiusDyadic n r
  rw [eq_sub_iff_add_eq, ha_split]
  exact hcancel.trans htaylor

/-- The precomputed inverse-power table satisfies the block Taylor identity at
grid exponent `n`; this instantiates `dyadicBlock_eq_taylor_sum` through
`fabiusTaylorHorner_eq_sum`. -/
theorem fabiusInversePowTwoTable_hasBlockTaylor (n : ℕ) :
    FabiusDyadicHasBlockTaylor (fabiusInversePowTwoTable n) n := by
  intro b r hb _hr
  rw [fabiusTaylorHorner_eq_sum n (n - b) (Nat.sub_le n b)]
  have hblock := dyadicBlock_eq_taylor_sum n b hb (r : ℚ)
  convert hblock using 1
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  congr 2
  ring

/-- The precomputed inverse-power table satisfies the bit recurrence.  This is
the hypothesis consumed by `fabiusDyadicUnit_eq_fabiusDyadic`. -/
theorem fabiusInversePowTwoTable_hasBitRecurrence (n : ℕ) :
    FabiusDyadicHasBitRecurrence (fabiusInversePowTwoTable n) n :=
  blockTaylor_implies_bitRecurrence (fabiusInversePowTwoTable n) n
    (fabiusInversePowTwoTable_hasBlockTaylor n)

/-- On the unit dyadic grid, the executable recursion agrees with equation (32). -/
theorem fabiusDyadicUnit_eq_fabiusDyadic (n a : ℕ) (ha : a ≤ 2 ^ n) :
    fabiusDyadicUnit n a = fabiusDyadic n a :=
  fabiusDyadicUnit_eq_fabiusDyadic_of_bitRecurrence n a ha
    (fabiusInversePowTwoTable_hasBitRecurrence n)

end Fabius
```

### `UpstreamDyadicAnalytic.lean`

```lean
import UpstreamDifferential
import UpstreamDyadicClosedForm
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Analytic correctness of exact dyadic Fabius evaluation

The bounded Fabius differential equation yields a finite Taylor recurrence on
each dyadic scale. Endpoint compatibility determines its inverse-power values,
and comparison with the exact closed-form recurrence proves that the rational
dyadic evaluator computes the analytic function.  The final API includes the
exact right endpoint of every unit dyadic grid, a direct real-cast identity for
the inverse-power table, and total analytic correctness for the clamped
natural-numerator evaluator.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset Set

namespace Fabius

noncomputable section

/-- The real dyadic scale `2^{-n}`, the base point of the register's
Taylor identities. -/
def inverseTwoPowReal (n : ℕ) : ℝ := ((2 : ℝ) ^ n)⁻¹

/-- The bounded Fabius value at the dyadic scale `2^{-n}` — the Taylor
coefficients' data. -/
noncomputable def analyticInverseValue (F : BoundedFabius) (n : ℕ) : ℝ :=
  fabiusReal F (inverseTwoPowReal n)

/-- **The dyadic Taylor sum** of the register's *Independent analytic
derivations*: the degree-`m` Taylor polynomial whose coefficients are the
normalized Fabius values at the dyadic scales,
`∑_k 2^{C(k+1,2)}·F(2^{-(m-k)})·y^k/k!`.  Its two public laws are the
derivative recursion `analyticTaylorSum_derivative_identity` and the
exact-remainder identity `analytic_scale_recurrence`. -/
noncomputable def analyticTaylorSum (F : BoundedFabius) (m : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ range (m + 1),
    (2 : ℝ) ^ (k + 1).choose 2 * analyticInverseValue F (m - k) *
      y ^ k / k.factorial

@[simp] private lemma inverseTwoPowReal_zero : inverseTwoPowReal 0 = 1 := by
  simp [inverseTwoPowReal]

private lemma two_mul_inverseTwoPowReal_succ (n : ℕ) :
    2 * inverseTwoPowReal (n + 1) = inverseTwoPowReal n := by
  simp only [inverseTwoPowReal, pow_succ]
  field_simp

private lemma inverseTwoPowReal_pos (n : ℕ) : 0 < inverseTwoPowReal n := by
  simp only [inverseTwoPowReal]
  positivity

private lemma inverseTwoPowReal_le_half (n : ℕ) (hn : 1 ≤ n) :
    inverseTwoPowReal n ≤ 1 / 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  simp only [inverseTwoPowReal, pow_add, pow_one]
  have hp : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  have hden : (2 : ℝ) ≤ 2 * 2 ^ m := by nlinarith
  simpa [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hden

@[simp] private lemma analyticTaylorSum_zero (F : BoundedFabius) (m : ℕ) :
    analyticTaylorSum F m 0 = analyticInverseValue F m := by
  rw [analyticTaylorSum]
  rw [Finset.sum_range_succ']
  simp

/-- **The Taylor-level Fabius differential equation**: differentiating
the order-`(m+1)` dyadic Taylor sum reproduces the order-`m` sum at the
doubled argument — the image of `F'(x) = 2F(2x)` in the register's
Taylor-integral derivation. -/
theorem analyticTaylorSum_derivative_identity
    (F : BoundedFabius) (m : ℕ) (y : ℝ) :
    HasDerivAt (analyticTaylorSum F (m + 1))
      (2 * analyticTaylorSum F m (2 * y)) y := by
  have hderiv : HasDerivAt (analyticTaylorSum F (m + 1))
      (∑ k ∈ range (m + 1 + 1),
        ((2 : ℝ) ^ (k + 1).choose 2 * analyticInverseValue F (m + 1 - k) /
          k.factorial) * ((k : ℝ) * y ^ (k - 1))) y := by
    let c : ℕ → ℝ := fun k =>
      (2 : ℝ) ^ (k + 1).choose 2 * analyticInverseValue F (m + 1 - k) /
        k.factorial
    have h := HasDerivAt.sum (u := range (m + 1 + 1))
      (fun k _hk => (hasDerivAt_pow k y).const_mul (c k))
    refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with z
      unfold analyticTaylorSum
      simp only [Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro k hk
      dsimp only [c]
      ring
    · apply Finset.sum_congr rfl
      intro k hk
      dsimp only [c]
  convert hderiv using 1
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
  rw [analyticTaylorSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hfac : ((j + 1).factorial : ℝ) = (j + 1) * j.factorial := by
    rw [Nat.factorial_succ]
    norm_num
  have hchoose := choose_add_two_two j
  rw [show m + 1 - (j + 1) = m - j by omega, hchoose, pow_add,
    pow_succ, mul_pow, hfac]
  have hjfac : (j.factorial : ℝ) ≠ 0 := by positivity
  have hjsucc : ((j : ℝ) + 1) ≠ 0 := by positivity
  rw [show j + 1 - 1 = j by omega]
  push_cast
  field_simp

private lemma analyticTaylorSum_continuous (F : BoundedFabius) (m : ℕ) :
    Continuous (analyticTaylorSum F m) := by
  unfold analyticTaylorSum
  fun_prop

private lemma analytic_scale_recurrence_one
    (F : BoundedFabius) (hF : IsFabius F) (y : ℝ)
    (hy0 : 0 ≤ y) (hy : y ≤ inverseTwoPowReal 1) :
    fabiusReal F (inverseTwoPowReal 1 + y) + fabiusReal F y =
      analyticTaylorSum F 1 y := by
  let lhs : ℝ → ℝ := fun z =>
    fabiusReal F (inverseTwoPowReal 1 + z) + fabiusReal F z
  let rhs : ℝ → ℝ := analyticTaylorSum F 1
  have hlhsCont : Continuous lhs := by
    dsimp only [lhs]
    exact ((hF.contDiff.continuous.comp
      (continuous_const.add continuous_id))).add hF.contDiff.continuous
  have hrhsCont : Continuous rhs := analyticTaylorSum_continuous F 1
  have hderivLhs : ∀ z ∈ Ico (0 : ℝ) (inverseTwoPowReal 1),
      HasDerivWithinAt lhs 2 (Ici z) z := by
    intro z hz
    have hzhalf : z ∈ Icc (0 : ℝ) (1 / 2) := by
      constructor
      · exact hz.1
      · simpa [inverseTwoPowReal] using hz.2.le
    have htlow : 1 / 2 ≤ inverseTwoPowReal 1 + z := by
      norm_num [inverseTwoPowReal]
      exact hz.1
    have hhigh := fabius_hasDerivAt_reflected_of_half_le F hF htlow
    have hlow := hF.hasDerivAt z hzhalf
    have hsym := hF.symmetry (2 * z)
      ⟨mul_nonneg (by norm_num) hz.1, by linarith [hzhalf.2]⟩
    have hhighComp := hhigh.comp z ((hasDerivAt_const z (inverseTwoPowReal 1)).add
      (hasDerivAt_id z))
    have hsum := hhighComp.fun_add hlow
    have hsum' : HasDerivAt lhs 2 z := by
      have hargEq : 2 - 2 * (inverseTwoPowReal 1 + z) = 1 - 2 * z := by
        norm_num [inverseTwoPowReal]
        ring
      have hcoef :
          2 * fabiusReal F (2 - 2 * (inverseTwoPowReal 1 + z)) * (0 + 1) +
              2 * fabiusReal F (2 * z) = 2 := by
        rw [hargEq, hsym]
        ring
      have hsum' := hsum.congr_deriv hcoef
      simpa only [lhs, Function.comp_apply, Pi.add_apply] using hsum'
    exact hsum'.hasDerivWithinAt.mono (by intro x hx; exact hx)
  have hderivRhs : ∀ z ∈ Ico (0 : ℝ) (inverseTwoPowReal 1),
      HasDerivWithinAt rhs 2 (Ici z) z := by
    intro z hz
    have h := analyticTaylorSum_derivative_identity F 0 z
    have h' : HasDerivAt rhs 2 z := by
      convert h using 1
      simp [analyticTaylorSum, analyticInverseValue, hF.one_of_one_le]
    exact h'.hasDerivWithinAt.mono (by intro x hx; exact hx)
  have hhalf : fabiusReal F (1 / 2) = 1 / 2 := by
    have hs := hF.symmetry (1 / 2) (by constructor <;> norm_num)
    norm_num at hs ⊢
    linarith
  have hzero : lhs 0 = rhs 0 := by
    dsimp only [lhs, rhs]
    rw [analyticTaylorSum_zero]
    simp only [analyticInverseValue]
    rw [hF.zero_of_nonpos 0 le_rfl]
    norm_num [inverseTwoPowReal] at hhalf ⊢
  exact eq_of_has_deriv_right_eq hderivLhs hderivRhs
    hlhsCont.continuousOn hrhsCont.continuousOn hzero y ⟨hy0, hy⟩

private lemma analytic_scale_recurrence_succ
    (F : BoundedFabius) (hF : IsFabius F) (m : ℕ) (hm : 1 ≤ m)
    (ih : ∀ y : ℝ, 0 ≤ y → y ≤ inverseTwoPowReal m →
      fabiusReal F (inverseTwoPowReal m + y) + fabiusReal F y =
        analyticTaylorSum F m y)
    (y : ℝ) (hy0 : 0 ≤ y) (hy : y ≤ inverseTwoPowReal (m + 1)) :
    fabiusReal F (inverseTwoPowReal (m + 1) + y) + fabiusReal F y =
      analyticTaylorSum F (m + 1) y := by
  let lhs : ℝ → ℝ := fun z =>
    fabiusReal F (inverseTwoPowReal (m + 1) + z) + fabiusReal F z
  let rhs : ℝ → ℝ := analyticTaylorSum F (m + 1)
  have hlhsCont : Continuous lhs := by
    dsimp only [lhs]
    exact ((hF.contDiff.continuous.comp
      (continuous_const.add continuous_id))).add hF.contDiff.continuous
  have hrhsCont : Continuous rhs := analyticTaylorSum_continuous F (m + 1)
  have hderivLhs : ∀ z ∈ Ico (0 : ℝ) (inverseTwoPowReal (m + 1)),
      HasDerivWithinAt lhs (2 * analyticTaylorSum F m (2 * z)) (Ici z) z := by
    intro z hz
    have hzscaled : 2 * z ≤ inverseTwoPowReal m := by
      rw [← two_mul_inverseTwoPowReal_succ m]
      nlinarith [hz.2.le]
    have hinvhalf := inverseTwoPowReal_le_half m hm
    have hzhalf : z ∈ Icc (0 : ℝ) (1 / 2) := by
      constructor
      · exact hz.1
      · have hzle : z ≤ inverseTwoPowReal (m + 1) := hz.2.le
        exact hzle.trans (inverseTwoPowReal_le_half (m + 1) (by omega))
    have hsumhalf : inverseTwoPowReal (m + 1) + z ≤ 1 / 2 := by
      have hdouble : inverseTwoPowReal (m + 1) + z ≤
          2 * inverseTwoPowReal (m + 1) := by linarith [hz.2.le]
      rw [two_mul_inverseTwoPowReal_succ] at hdouble
      exact hdouble.trans hinvhalf
    have hpoint : inverseTwoPowReal (m + 1) + z ∈ Icc (0 : ℝ) (1 / 2) :=
      ⟨add_nonneg (inverseTwoPowReal_pos (m + 1)).le hz.1, hsumhalf⟩
    have hfirst := hF.hasDerivAt (inverseTwoPowReal (m + 1) + z) hpoint
    have hfirstComp := hfirst.comp z
      ((hasDerivAt_const z (inverseTwoPowReal (m + 1))).add (hasDerivAt_id z))
    have hsecond := hF.hasDerivAt z hzhalf
    have hsum := hfirstComp.fun_add hsecond
    have hargEq : 2 * (inverseTwoPowReal (m + 1) + z) =
        inverseTwoPowReal m + 2 * z := by
      rw [mul_add, two_mul_inverseTwoPowReal_succ]
    have hih := ih (2 * z) (mul_nonneg (by norm_num) hz.1) hzscaled
    have hcoef :
        2 * fabiusReal F (2 * (inverseTwoPowReal (m + 1) + z)) * (0 + 1) +
            2 * fabiusReal F (2 * z) = 2 * analyticTaylorSum F m (2 * z) := by
      rw [hargEq]
      rw [← hih]
      ring
    have hsum' := hsum.congr_deriv hcoef
    have hsum'' : HasDerivAt lhs (2 * analyticTaylorSum F m (2 * z)) z := by
      simpa only [lhs, Function.comp_apply, Pi.add_apply] using hsum'
    exact hsum''.hasDerivWithinAt.mono (by intro x hx; exact hx)
  have hderivRhs : ∀ z ∈ Ico (0 : ℝ) (inverseTwoPowReal (m + 1)),
      HasDerivWithinAt rhs (2 * analyticTaylorSum F m (2 * z)) (Ici z) z := by
    intro z hz
    exact (analyticTaylorSum_derivative_identity F m z).hasDerivWithinAt.mono
      (by intro x hx; exact hx)
  have hzero : lhs 0 = rhs 0 := by
    dsimp only [lhs, rhs]
    rw [analyticTaylorSum_zero]
    simp only [analyticInverseValue]
    rw [hF.zero_of_nonpos 0 le_rfl, add_zero]
    simp
  exact eq_of_has_deriv_right_eq hderivLhs hderivRhs
    hlhsCont.continuousOn hrhsCont.continuousOn hzero y ⟨hy0, hy⟩

/-- **The Taylor identity with exact remainder** (the register's
*Independent analytic derivations*, bounded function): for `1 ≤ m` and
`0 ≤ y ≤ 2^{-m}`,
`F(2^{-m} + y) = analyticTaylorSum F m y - F(y)` — the remainder of the
dyadic Taylor expansion is exactly `-F(y)`, with no error term. -/
theorem analytic_scale_recurrence
    (F : BoundedFabius) (hF : IsFabius F) (m : ℕ) (hm : 1 ≤ m)
    (y : ℝ) (hy0 : 0 ≤ y) (hy : y ≤ inverseTwoPowReal m) :
    fabiusReal F (inverseTwoPowReal m + y) + fabiusReal F y =
      analyticTaylorSum F m y := by
  induction m generalizing y with
  | zero => omega
  | succ m ih =>
      cases m with
      | zero => exact analytic_scale_recurrence_one F hF y hy0 hy
      | succ m =>
          exact analytic_scale_recurrence_succ F hF (m + 1) (by omega)
            (fun z hz0 hz => ih (by omega) z hz0 hz) y hy0 hy

private lemma fabiusAtInverseTwoPow_endpoint (n : ℕ) :
    fabiusAtInverseTwoPow n + fabiusAtInverseTwoPow (n + 1) =
      ∑ k ∈ range (n + 1 + 1),
        (2 : ℚ) ^ (k + 1).choose 2 * fabiusAtInverseTwoPow (n + 1 - k) *
          ((1 : ℚ) / (2 : ℚ) ^ (n + 1)) ^ k / k.factorial := by
  have hcancel := fabiusDyadic_add_remainder_eq_block (n + 1) 0 1 (by norm_num)
  have hblock := dyadicBlock_eq_taylor_sum (n + 1) 0 (by omega) (1 : ℚ)
  have hclosed :
      fabiusDyadic (n + 1) 2 + fabiusDyadic (n + 1) 1 =
        ∑ k ∈ range (n + 1 + 1),
          (2 : ℚ) ^ (k + 1).choose 2 * fabiusAtInverseTwoPow (n + 1 - k) *
            ((1 : ℚ) / (2 : ℚ) ^ (n + 1)) ^ k / k.factorial := by
    calc
      _ = _ := hcancel
      _ = _ := by
        convert hblock using 1
        · congr 1
          apply Finset.sum_congr rfl
          intro h hh
          congr 2
          norm_num
  have hrefine := fabiusDyadic_refine_of_kernel dyadicKernel_has_refinement n 1
  rw [show 2 = 2 * 1 by omega, hrefine] at hclosed
  exact hclosed

private theorem analyticInverseValue_eq_fabiusAtInverseTwoPow
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    analyticInverseValue F n = (fabiusAtInverseTwoPow n : ℝ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn0 : n = 0
      · subst n
        simp [analyticInverseValue, inverseTwoPowReal,
          hF.one_of_one_le, fabiusAtInverseTwoPow_eq_halfMoment,
          halfMomentFabiusValue]
      · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        let base := inverseTwoPowReal (n + 1)
        let termA : ℕ → ℝ := fun k =>
          (2 : ℝ) ^ (k + 1).choose 2 * analyticInverseValue F (n + 1 - k) *
            base ^ k / k.factorial
        let termR : ℕ → ℝ := fun k =>
          (2 : ℝ) ^ (k + 1).choose 2 * (fabiusAtInverseTwoPow (n + 1 - k) : ℝ) *
            base ^ k / k.factorial
        have hsplitA :
            (∑ k ∈ range (n + 1 + 1), termA k) =
              termA 0 + termA 1 + ∑ j ∈ range n, termA (2 + j) := by
          rw [show n + 1 + 1 = 2 + n by omega, Finset.sum_range_add]
          simp [Finset.sum_range_succ]
        have hsplitR :
            (∑ k ∈ range (n + 1 + 1), termR k) =
              termR 0 + termR 1 + ∑ j ∈ range n, termR (2 + j) := by
          rw [show n + 1 + 1 = 2 + n by omega, Finset.sum_range_add]
          simp [Finset.sum_range_succ]
        have ha0 := analytic_scale_recurrence F hF (n + 1) (by omega)
          base (inverseTwoPowReal_pos (n + 1)).le le_rfl
        have hdouble : inverseTwoPowReal (n + 1) + base = inverseTwoPowReal n := by
          dsimp only [base]
          linarith [two_mul_inverseTwoPowReal_succ n]
        have ha :
            analyticInverseValue F n + analyticInverseValue F (n + 1) =
              ∑ k ∈ range (n + 1 + 1), termA k := by
          change fabiusReal F (inverseTwoPowReal n) +
              fabiusReal F (inverseTwoPowReal (n + 1)) = _
          rw [← hdouble]
          simpa only [analyticInverseValue, analyticTaylorSum, base, termA] using ha0
        rw [hsplitA] at ha
        norm_num [termA] at ha
        have hrQ := fabiusAtInverseTwoPow_endpoint n
        have hrCast := congrArg (fun q : ℚ => (q : ℝ)) hrQ
        push_cast at hrCast
        have hbaseReal : (1 : ℝ) / (2 : ℝ) ^ (n + 1) = base := by
          simp only [base, inverseTwoPowReal, one_div]
        rw [hbaseReal] at hrCast
        have hr :
            (fabiusAtInverseTwoPow n : ℝ) + (fabiusAtInverseTwoPow (n + 1) : ℝ) =
              ∑ k ∈ range (n + 1 + 1), termR k := by
          simpa only [termR] using hrCast
        rw [hsplitR] at hr
        norm_num [termR] at hr
        have htail :
            (∑ j ∈ range n, termA (2 + j)) =
              ∑ j ∈ range n, termR (2 + j) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjlt : j < n := Finset.mem_range.mp hj
          have hindex : n + 1 - (2 + j) < n := by omega
          dsimp only [termA, termR]
          rw [ih (n + 1 - (2 + j)) hindex]
        rw [htail] at ha
        have hcoeflt : 2 * base < 1 := by
          dsimp only [base]
          rw [two_mul_inverseTwoPowReal_succ]
          exact (inverseTwoPowReal_le_half n hnpos).trans_lt (by norm_num)
        have hfactor :
            (1 - 2 * base) *
                (analyticInverseValue F n - (fabiusAtInverseTwoPow n : ℝ)) = 0 := by
          linear_combination ha - hr
        exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left
          (ne_of_gt (sub_pos.mpr hcoeflt)))

private lemma analyticTaylorSum_eq_cast_horner
    (F : BoundedFabius) (hF : IsFabius F)
    (maxExponent order : ℕ) (horder : order ≤ maxExponent) (offset : ℚ) :
    analyticTaylorSum F order (offset : ℝ) =
      (fabiusTaylorHorner (fabiusInversePowTwoTable maxExponent)
        order offset : ℝ) := by
  have hq := fabiusTaylorHorner_eq_sum maxExponent order horder offset
  have hr := congrArg (fun q : ℚ => (q : ℝ)) hq
  push_cast at hr
  rw [hr, analyticTaylorSum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [analyticInverseValue_eq_fabiusAtInverseTwoPow F hF]

/-- **The blockwise change of variables** (the register's *Independent
analytic derivations*): stripping the leading binary digit of the
numerator turns the bounded value at `a/2^n` into the Horner form of the
dyadic Taylor sum minus the exact remainder at the stripped
remainder — the analytic identity that drives every interior step of
the exact evaluator. -/
theorem fabiusReal_dyadic_bit_recurrence
    (F : BoundedFabius) (hF : IsFabius F)
    (n a : ℕ) (ha0 : 0 < a) (ha : a ≤ 2 ^ n) :
    let leadingExponent := Nat.log2 a
    let order := n - leadingExponent
    let remainder := a - 2 ^ leadingExponent
    let offset := (remainder : ℚ) / (2 : ℚ) ^ n
    fabiusReal F ((a : ℝ) / (2 : ℝ) ^ n) =
      (fabiusTaylorHorner (fabiusInversePowTwoTable n) order offset : ℝ) -
        fabiusReal F ((remainder : ℝ) / (2 : ℝ) ^ n) := by
  dsimp only
  obtain ⟨hb, hrlt, haSplit⟩ := leading_bit_data n a ha0 ha
  let b := Nat.log2 a
  let r := a - 2 ^ b
  let order := n - b
  let offset : ℚ := (r : ℚ) / (2 : ℚ) ^ n
  change b ≤ n at hb
  change r < 2 ^ b at hrlt
  change a = 2 ^ b + r at haSplit
  change fabiusReal F ((a : ℝ) / (2 : ℝ) ^ n) =
    (fabiusTaylorHorner (fabiusInversePowTwoTable n) order offset : ℝ) -
      fabiusReal F ((r : ℝ) / (2 : ℝ) ^ n)
  by_cases horder0 : order = 0
  · have hbn : b = n := by omega
    have haSplit' : a = 2 ^ n + r := by simpa [hbn] using haSplit
    have hrzero : r = 0 := by omega
    have haPow : a = 2 ^ n := by omega
    rw [haPow, hrzero]
    rw [hF.one_of_one_le _ (by norm_num), hF.zero_of_nonpos _ (by norm_num)]
    have hoffzero : offset = 0 := by simp [offset, hrzero]
    rw [horder0, hoffzero]
    rw [fabiusTaylorHorner, fabiusTaylorHorner.go.eq_1]
    norm_num
  · have horderPos : 1 ≤ order := Nat.one_le_iff_ne_zero.mpr horder0
    have hnadd : n = b + order := by
      dsimp only [order]
      omega
    have hbase : (2 : ℝ) ^ b / (2 : ℝ) ^ n =
        inverseTwoPowReal order := by
      rw [hnadd, pow_add]
      simp only [inverseTwoPowReal]
      field_simp
    have hoffsetCast : (offset : ℝ) = (r : ℝ) / (2 : ℝ) ^ n := by
      simp only [offset]
      push_cast
      rfl
    have hoffsetNonneg : 0 ≤ (offset : ℝ) := by
      rw [hoffsetCast]
      positivity
    have hoffsetLe : (offset : ℝ) ≤ inverseTwoPowReal order := by
      rw [hoffsetCast, ← hbase]
      apply div_le_div_of_nonneg_right
      · exact_mod_cast hrlt.le
      · positivity
    have hxSplit : (a : ℝ) / (2 : ℝ) ^ n =
        inverseTwoPowReal order + (offset : ℝ) := by
      rw [haSplit]
      push_cast
      rw [add_div, hbase, hoffsetCast]
    have hscale := analytic_scale_recurrence F hF order horderPos
      (offset : ℝ) hoffsetNonneg hoffsetLe
    rw [analyticTaylorSum_eq_cast_horner F hF n order (Nat.sub_le n b) offset]
      at hscale
    rw [eq_sub_iff_add_eq, hxSplit, ← hoffsetCast]
    exact hscale

/-- The exact closed-form evaluator takes the value `1` at the right endpoint
of every unit dyadic grid, including the scale `n = 0`. -/
theorem fabiusDyadic_unit_endpoint (n : ℕ) :
    fabiusDyadic n (2 ^ n) = 1 := by
  rw [← fabiusDyadicUnit_eq_fabiusDyadic n (2 ^ n) le_rfl,
    fabiusDyadicUnit_of_ge n (2 ^ n) le_rfl]

/-- Equation (32) evaluates the bounded Fabius function on its dyadic grid. -/
theorem fabiusDyadic_cast (F : BoundedFabius) (hF : IsFabius F)
    (n a : ℕ) (ha : a ≤ 2 ^ n) :
    (fabiusDyadic n a : ℝ) = fabiusReal F ((a : ℝ) / (2 : ℝ) ^ n) := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
      by_cases ha0 : a = 0
      · subst a
        rw [fabiusDyadic_arg_zero]
        norm_num
        exact (hF.zero_of_nonpos 0 le_rfl).symm
      · have hapos : 0 < a := Nat.pos_of_ne_zero ha0
        let b := Nat.log2 a
        let r := a - 2 ^ b
        have hrlt : r < a := by
          dsimp only [r]
          exact Nat.sub_lt hapos (by positivity)
        have hrbound : r ≤ 2 ^ n := hrlt.le.trans ha
        have hihr := ih r hrlt hrbound
        have hrat := fabiusInversePowTwoTable_hasBitRecurrence n a hapos ha
        have hana := fabiusReal_dyadic_bit_recurrence F hF n a hapos ha
        dsimp only at hrat hana
        have hratCast := congrArg (fun q : ℚ => (q : ℝ)) hrat
        push_cast at hratCast
        rw [hratCast, hihr]
        exact hana.symm

/-- After coercion to `ℝ`, the exact rational inverse-power value agrees with
every bounded Fabius solution at `2⁻ⁿ`.  This is the `a = 1` specialization of
`fabiusDyadic_cast` and includes the endpoint `n = 0`. -/
theorem fabiusAtInverseTwoPow_cast
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    (fabiusAtInverseTwoPow n : ℝ) =
      fabiusReal F (((2 : ℝ) ^ n)⁻¹) := by
  simpa only [fabiusAtInverseTwoPow, Nat.cast_one, one_div] using
    fabiusDyadic_cast F hF n 1 Nat.one_le_two_pow

/-- The executable bounded evaluator agrees with the analytic Fabius function
for every natural dyadic numerator. Numerators beyond the unit grid are
handled by the common constant value `1`. -/
theorem fabiusDyadicUnit_cast (F : BoundedFabius) (hF : IsFabius F)
    (n a : ℕ) :
    (fabiusDyadicUnit n a : ℝ) =
      fabiusReal F ((a : ℝ) / (2 : ℝ) ^ n) := by
  by_cases ha : a ≤ 2 ^ n
  · rw [fabiusDyadicUnit_eq_fabiusDyadic n a ha,
      fabiusDyadic_cast F hF n a ha]
  · rw [fabiusDyadicUnit_of_ge n a (by omega)]
    norm_num
    apply (hF.one_of_one_le _ ?_).symm
    rw [le_div_iff₀' (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)]
    norm_num
    exact_mod_cast (show 2 ^ n ≤ a by omega)

end

end Fabius
```

### `AnalyticDenominatorEndpoint.lean`

```lean
import LiteralConjectureSixteen
import UpstreamDyadicAnalytic
import Mathlib.Data.Rat.Cast.Order

namespace FabiusProofLane
open Finset

/-- A genuine integer common denominator of the analytic Fabius odd grid. -/
def ClearsAnalyticFabius (F : Fabius.BoundedFabius) (n d : ℕ) : Prop :=
  ∀ a ∈ Fabius.oddDyadicNumerators n,
    ∃ z : ℤ, (d : ℝ)*Fabius.fabiusReal F ((a : ℝ)/(2 : ℝ)^n)=(z : ℝ)

lemma rational_integer_multiple_iff (q : ℚ) (d : ℕ) :
    (∃ z : ℤ, (d : ℝ)*(q : ℝ)=(z : ℝ)) ↔ q.den ∣ d := by
  constructor
  · rintro ⟨z,hz⟩
    have hq : (d : ℚ)*q=(z : ℚ) := by exact_mod_cast hz
    by_cases hd0 : d=0
    · simp [hd0]
    have heq : q=(z : ℚ)/(d : ℚ) := by
      apply (eq_div_iff (by exact_mod_cast hd0)).mpr
      simpa only [mul_comm] using hq
    have hh : (q.den : ℤ) ∣ (d : ℤ) := by
      rw [heq]
      simpa only [Rat.divInt_eq_div,Int.cast_natCast] using Rat.den_dvd z (d : ℤ)
    exact_mod_cast hh
  · intro hd
    obtain ⟨z,hz⟩ := hd
    refine ⟨(z : ℤ)*q.num,?_⟩
    rw [hz,Nat.cast_mul]
    have hden := Rat.mul_den_eq_num q
    have hr : (q.den : ℚ)*q=(q.num : ℚ) := by simpa only [mul_comm] using hden
    have hreal : (q.den : ℝ)*(q : ℝ)=(q.num : ℝ) := by exact_mod_cast hr
    push_cast
    calc
      (q.den : ℝ)*(z : ℝ)*(q : ℝ)=(z : ℝ)*((q.den : ℝ)*(q : ℝ)) := by ring
      _ = _ := by rw [hreal]

lemma analytic_fabius_common_denominator_iff (F : Fabius.BoundedFabius)
    (hF : Fabius.IsFabius F) (n d : ℕ) :
    ClearsAnalyticFabius F n d ↔ Fabius.dyadicDenominator n ∣ d := by
  have hgrid (a : ℕ) (ha : a ∈ Fabius.oddDyadicNumerators n) : a ≤ 2^n :=
    le_trans (mem_Icc.mp (mem_filter.mp ha).1).2 (Nat.sub_le _ _)
  have hfabius : ClearsAnalyticFabius F n d ↔ Fabius.fabiusDyadicDenominator n ∣ d := by
    rw [ClearsAnalyticFabius,Fabius.fabiusDyadicDenominator,Finset.lcm_dvd_iff]
    apply forall_congr'
    intro a
    apply imp_congr_right
    intro ha
    rw [← Fabius.fabiusDyadic_cast F hF n a (hgrid a ha),rational_integer_multiple_iff]
  by_cases hn : 1 ≤ n
  · rwa [sourceDenominator_eq_fabius n hn]
  · have hzero : n=0 := by omega
    subst n
    simpa [Fabius.dyadicDenominator,Fabius.fabiusDyadicDenominator,
      Fabius.oddDyadicNumerators] using hfabius

#print axioms analytic_fabius_common_denominator_iff
end FabiusProofLane

namespace FabiusProofLane
open Finset

/-- The source's analytic up-function odd grid, with ordinary integer denominators. -/
def ClearsAnalyticRvachev (F : Fabius.BoundedFabius) (n d : ℕ) : Prop :=
  ∀ a ∈ Fabius.oddDyadicNumerators n,
    ∃ z : ℤ, (d : ℝ)*Fabius.rvachevUp F ((a : ℝ)/(2 : ℝ)^n)=(z : ℝ)

lemma rvachevDyadic_cast_odd (F : Fabius.BoundedFabius) (hF : Fabius.IsFabius F)
    (n a : ℕ) (ha : a ∈ Fabius.oddDyadicNumerators n) :
    (Fabius.rvachevDyadic n (a : ℤ) : ℝ)=
      Fabius.rvachevUp F ((a : ℝ)/(2 : ℝ)^n) := by
  have hbounds := mem_Icc.mp (mem_filter.mp ha).1
  have hale : a ≤ 2^n := le_trans hbounds.2 (Nat.sub_le _ _)
  have hapos : (0 : ℝ) < a := by exact_mod_cast (lt_of_lt_of_le (by decide : 0<1) hbounds.1)
  have hargpos : (0 : ℝ) < (a : ℝ)/(2 : ℝ)^n := div_pos hapos (by positivity)
  simp only [Fabius.rvachevDyadic,Int.natAbs_natCast,if_pos hale]
  rw [Rat.cast_abs,Fabius.fabiusDyadic_cast F hF n (2^n-a) (Nat.sub_le _ _),
    abs_of_nonneg (Fabius.fabiusReal_nonneg F _),Fabius.rvachevUp_of_pos F hargpos]
  congr 1
  rw [Nat.cast_sub hale,Nat.cast_pow,Nat.cast_ofNat]
  field_simp

/-- Exact rational D_n is characterized by divisibility among all genuine
integer denominators of the analytic up-function values. -/
theorem analytic_rvachev_common_denominator_iff (F : Fabius.BoundedFabius)
    (hF : Fabius.IsFabius F) (n d : ℕ) :
    ClearsAnalyticRvachev F n d ↔ Fabius.dyadicDenominator n ∣ d := by
  rw [ClearsAnalyticRvachev,Fabius.dyadicDenominator,Finset.lcm_dvd_iff]
  apply forall_congr'
  intro a
  apply imp_congr_right
  intro ha
  rw [← rvachevDyadic_cast_odd F hF n a ha,rational_integer_multiple_iff]

lemma source_D_ne_zero (n : ℕ) : Fabius.dyadicDenominator n ≠ 0 := by
  simp [Fabius.dyadicDenominator,Finset.lcm_eq_zero_iff,Rat.den_nz]

/-- Literal least-common-denominator semantics for the source D_n, at every level. -/
theorem source_D_isLeast_analytic (F : Fabius.BoundedFabius) (hF : Fabius.IsFabius F)
    (n : ℕ) :
    IsLeast {d : ℕ | 0<d ∧ ClearsAnalyticRvachev F n d} (Fabius.dyadicDenominator n) := by
  refine ⟨⟨Nat.pos_of_ne_zero (source_D_ne_zero n),?_⟩,?_⟩
  · exact (analytic_rvachev_common_denominator_iff F hF n _).mpr dvd_rfl
  · intro d hd
    exact Nat.le_of_dvd hd.1 ((analytic_rvachev_common_denominator_iff F hF n d).mp hd.2)

/-- The full source conjecture together with its analytic denominator interpretation. -/
theorem full_fabius_conjecture_with_analytic_meaning
    (F : Fabius.BoundedFabius) (hF : Fabius.IsFabius F) :
    Fabius.conjecture_sixteen ∧
      ∀ n : ℕ, IsLeast {d : ℕ | 0<d ∧ ClearsAnalyticRvachev F n d}
        (Fabius.dyadicDenominator n) :=
  ⟨conjecture_sixteen_proved,source_D_isLeast_analytic F hF⟩

#print axioms full_fabius_conjecture_with_analytic_meaning
end FabiusProofLane
```

### `FabiusFunctionBasic.lean`

```lean
import UpstreamBasic
```

### `FabiusFunctionDyadicAnalytic.lean`

```lean
import UpstreamDyadicAnalytic
```

### `ProveItExistence.lean`

```lean
/-
Third-party source: ProveIt, https://github.com/VladimirReshetnikov/ProveIt
Author: Vladimir Reshetnikov and ProveIt Contributors
Licence: MIT No Attribution License (sources/proveit-LICENSE-pinned)
Commit: 39d36e129589eed9edc5f2d40acfa683d783501d
Path: Analysis/FabiusFunction/Lean/FabiusFunction/Existence.lean
The complete upstream file follows byte-for-byte, including its original imports.
-/
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import FabiusFunction.Basic
import FabiusFunction.DyadicAnalytic

/-!
# Existence and uniqueness of the Fabius function

This module constructs the bounded Fabius function as the fixed point of a
strict contraction on the complete space of continuous, symmetric,
`[0, 1]`-valued functions on the unit interval. Its integral fixed-point
equation supplies a global first-derivative identity. The corresponding
Rvachev equation bootstraps the fixed point to smoothness.

The construction layer also exposes reusable facts about reflection on the
unit interval, the constant-tail extension, and differentiation of its
interval-integral primitive; candidate-specific lemmas are thin
specializations of those general APIs.

Uniqueness follows because every `IsFabius` function has the same values on
dyadic rationals and those rationals approximate every point of `[0, 1]`.
-/

open Filter Set MeasureTheory Topology
open scoped Interval ContDiff

namespace Fabius
namespace Existence

set_option autoImplicit false
noncomputable section

/-- The closed unit interval `[0, 1]`, coerced to a type to serve as the
domain of the candidate functions in the fixed-point construction. -/
abbrev I := Set.Icc (0 : ℝ) 1
/-- Real-valued continuous functions on `I` with the sup metric, the complete
ambient space in which the contraction argument takes place. -/
abbrev C := C(I, ℝ)

/-- The reflection `x ↦ 1 - x` of the unit interval about `1 / 2`, used to
state the symmetry half of `admissible`. -/
def reflect (x : I) : I :=
  ⟨1 - x.1, by constructor <;> linarith [x.2.1, x.2.2]⟩

/-- Reflection of `I` about `1 / 2` is continuous. -/
lemma continuous_reflect : Continuous reflect := by
  exact (continuous_const.sub continuous_subtype_val).subtype_mk _

/-- Reflection about `1 / 2` is an involution on the unit interval. -/
lemma reflect_reflect (x : I) : reflect (reflect x) = x := by
  apply Subtype.ext
  simp [reflect]

/-- A continuous `f : C` is admissible when it takes values in `[0, 1]` and
satisfies the reflection identity `f (1 - x) = 1 - f x` at every point of `I`.
These are exactly the two constraints preserved by `transform`. -/
def admissible (f : C) : Prop :=
  (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
    ∀ x, f (reflect x) = 1 - f x

/-- The set of admissible members of `C`.  The contraction `transformSelf`
maps this set into itself and its fixed point is `fixedCandidate`. -/
def admissibleSet : Set C := {f | admissible f}

/-- `admissibleSet` is closed in `C`, being an intersection over the points of
`I` of pointwise inequality and equality conditions. -/
lemma admissibleSet_closed : IsClosed admissibleSet := by
  have heval (x : I) : Continuous (fun f : C => f x) :=
    (ContinuousMap.evalCLM ℝ x).continuous
  have hbounds : IsClosed {f : C | ∀ x, 0 ≤ f x ∧ f x ≤ 1} := by
    rw [show {f : C | ∀ x, 0 ≤ f x ∧ f x ≤ 1} =
        ⋂ x : I, {f : C | 0 ≤ f x ∧ f x ≤ 1} by ext f; simp]
    apply isClosed_iInter
    intro x
    exact (isClosed_le continuous_const (heval x)).inter
      (isClosed_le (heval x) continuous_const)
  have hsymm : IsClosed {f : C | ∀ x, f (reflect x) = 1 - f x} := by
    rw [show {f : C | ∀ x, f (reflect x) = 1 - f x} =
        ⋂ x : I, {f : C | f (reflect x) = 1 - f x} by ext f; simp]
    apply isClosed_iInter
    intro x
    exact isClosed_eq (heval (reflect x)) (continuous_const.sub (heval x))
  exact hbounds.inter hsymm

/-- `admissibleSet` inherits completeness from `C` because it is closed; this
is one of the two hypotheses of the Banach fixed-point theorem used below. -/
instance : CompleteSpace admissibleSet :=
  admissibleSet_closed.completeSpace_coe

/-- The identity function `x ↦ x` on `I`, the explicit admissible function
that witnesses `Nonempty admissibleSet`. -/
def linearCandidate : C :=
  ⟨fun x => x.1, continuous_subtype_val⟩

/-- The identity function on `I` is admissible. -/
lemma linearCandidate_admissible : admissible linearCandidate := by
  constructor
  · intro x
    exact x.2
  · intro x
    rfl

/-- `admissibleSet` is nonempty, witnessed by `linearCandidate`; this is the
second hypothesis of the Banach fixed-point theorem used below. -/
instance : Nonempty admissibleSet :=
  ⟨⟨linearCandidate, linearCandidate_admissible⟩⟩

/-- Extend `f : C` to all of `ℝ` by precomposing with the projection onto
`[0, 1]`, so the extension is constant on `(-∞, 0]` and on `[1, ∞)`.  This is
the form in which candidates are integrated. -/
def extend (f : C) (x : ℝ) : ℝ :=
  f (Set.projIcc 0 1 (by norm_num) x)

/-- The extension of a continuous function on `I` to `ℝ` is continuous. -/
lemma continuous_extend (f : C) : Continuous (extend f) :=
  f.continuous.comp continuous_projIcc

/-- On `[0, 1]` the extension agrees with the original function on `I`. -/
lemma extend_eq (f : C) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    extend f x = f ⟨x, hx⟩ := by
  simp [extend, Set.projIcc_of_mem (by norm_num) hx]

/-- On the closed left tail, the projected extension is the left endpoint
value of the original continuous map. -/
lemma extend_eq_zero_of_nonpos (f : C) {x : ℝ} (hx : x ≤ 0) :
    extend f x = f ⟨0, by constructor <;> norm_num⟩ := by
  rw [extend, (Set.projIcc_eq_left (by norm_num : (0 : ℝ) < 1)).2 hx]

/-- On the closed right tail, the projected extension is the right endpoint
value of the original continuous map. -/
lemma extend_eq_one_of_one_le (f : C) {x : ℝ} (hx : 1 ≤ x) :
    extend f x = f ⟨1, by constructor <;> norm_num⟩ := by
  rw [extend, (Set.projIcc_eq_right (by norm_num : (0 : ℝ) < 1)).2 hx]

/-- The primitive `y ↦ ∫ t in 0..y, extend f t` of the extension of `f`,
normalized to vanish at `0` and defined for every real `y`. -/
def cumulative (f : C) (y : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..y, extend f t

/-- The primitive `cumulative f` is continuous on `ℝ`. -/
lemma continuous_cumulative (f : C) : Continuous (cumulative f) := by
  apply intervalIntegral.continuous_primitive
  intro a b
  exact (continuous_extend f).intervalIntegrable a b

/-- The primitive of any `f : C` vanishes at `0`. -/
lemma cumulative_zero (f : C) : cumulative f 0 = 0 := by
  simp [cumulative]

/-- Fundamental theorem of calculus for the projected extension: the
primitive `cumulative f` has derivative `extend f y` at every real `y`. -/
lemma cumulative_hasDerivAt (f : C) (y : ℝ) :
    HasDerivAt (cumulative f) (extend f y) y := by
  apply intervalIntegral.integral_hasDerivAt_right
  · exact (continuous_extend f).intervalIntegrable 0 y
  · exact (continuous_extend f).aestronglyMeasurable.stronglyMeasurableAtFilter
  · exact (continuous_extend f).continuousAt

/-- For admissible `f` the primitive reaches `1 / 2` at `1`; this is the
reflection identity integrated over `[0, 1]`.  It is what makes the two
branches of `transformValue` agree at `x = 1 / 2`. -/
lemma cumulative_one_of_admissible {f : C} (hf : admissible f) :
    cumulative f 1 = 1 / 2 := by
  have hreflect : (∫ t in (0 : ℝ)..1, extend f (1 - t)) =
      ∫ t in (0 : ℝ)..1, extend f t := by
    simpa only [sub_self, sub_zero] using
      intervalIntegral.integral_comp_sub_left
        (f := extend f) (a := 0) (b := 1) 1
  have heq : ∀ t ∈ uIcc (0 : ℝ) 1, extend f (1 - t) = 1 - extend f t := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    rw [extend_eq f ⟨by linarith [ht.2], by linarith [ht.1]⟩,
      extend_eq f ht]
    exact hf.2 ⟨t, ht⟩
  have hintegral : (∫ t in (0 : ℝ)..1, extend f (1 - t)) =
      ∫ t in (0 : ℝ)..1, (1 - extend f t) :=
    intervalIntegral.integral_congr heq
  rw [hreflect] at hintegral
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_const] at hintegral
  · norm_num at hintegral
    simpa [cumulative] using (show (∫ t in (0 : ℝ)..1, extend f t) = 1 / 2 by linarith)
  · exact intervalIntegrable_const
  · exact (continuous_extend f).intervalIntegrable 0 1

/-- The value at `x ∈ I` of the transform of `f`: `cumulative f (2 * x)` for
`x ≤ 1 / 2` and `1 - cumulative f (2 - 2 * x)` otherwise.  The tie at
`x = 1 / 2` is resolved by the left branch. -/
def transformValue (f : C) (x : I) : ℝ :=
  if x.1 ≤ 1 / 2 then cumulative f (2 * x.1)
  else 1 - cumulative f (2 - 2 * x.1)

/-- For admissible `f` the two branches of `transformValue f` take the same
value at `x = 1 / 2`, so the glued function is continuous. -/
lemma continuous_transformValue {f : C} (hf : admissible f) :
    Continuous (transformValue f) := by
  apply Continuous.if_le
  · exact (continuous_cumulative f).comp
      (continuous_const.mul continuous_subtype_val)
  · exact continuous_const.sub ((continuous_cumulative f).comp
      (continuous_const.sub (continuous_const.mul continuous_subtype_val)))
  · exact continuous_subtype_val
  · exact continuous_const
  · intro x hx
    have hxval : x.1 = 1 / 2 := hx
    simp only [hxval]
    norm_num
    rw [cumulative_one_of_admissible hf]
    norm_num

/-- `transformValue` of an admissible `f`, bundled as an element of `C`. -/
def transform (f : admissibleSet) : C :=
  ⟨transformValue f.1, continuous_transformValue f.2⟩

private lemma cumulative_bounds {f : C} (hf : admissible f)
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    0 ≤ cumulative f y ∧ cumulative f y ≤ y := by
  have hcont := continuous_extend f
  have hnonneg : 0 ≤ ∫ t in (0 : ℝ)..y, extend f t := by
    apply intervalIntegral.integral_nonneg hy.1
    intro t ht
    rw [extend_eq f ⟨ht.1, ht.2.trans hy.2⟩]
    exact (hf.1 ⟨t, ⟨ht.1, ht.2.trans hy.2⟩⟩).1
  have hle : (∫ t in (0 : ℝ)..y, extend f t) ≤
      ∫ _t in (0 : ℝ)..y, (1 : ℝ) := by
    apply intervalIntegral.integral_mono_on hy.1
      (hcont.intervalIntegrable 0 y) (continuous_const.intervalIntegrable 0 y)
    intro t ht
    rw [extend_eq f ⟨ht.1, ht.2.trans hy.2⟩]
    exact (hf.1 ⟨t, ⟨ht.1, ht.2.trans hy.2⟩⟩).2
  rw [intervalIntegral.integral_const] at hle
  norm_num at hle
  exact ⟨by simpa [cumulative] using hnonneg, by simpa [cumulative] using hle⟩

/-- The transform of an admissible function is again admissible, so
`transform` restricts to a self-map of `admissibleSet`. -/
lemma transform_admissible (f : admissibleSet) : admissible (transform f) := by
  constructor
  · intro x
    simp only [transform, transformValue, ContinuousMap.coe_mk]
    split_ifs with hx
    · have hy : 2 * x.1 ∈ Icc (0 : ℝ) 1 := by
        constructor
        · nlinarith [x.2.1]
        · linarith
      have hb := cumulative_bounds f.2 hy
      exact ⟨hb.1, hb.2.trans hy.2⟩
    · have hy : 2 - 2 * x.1 ∈ Icc (0 : ℝ) 1 := by
        constructor <;> linarith [x.2.1, x.2.2]
      have hb := cumulative_bounds f.2 hy
      constructor <;> linarith
  · intro x
    simp only [transform, transformValue, ContinuousMap.coe_mk, reflect]
    by_cases hx : x.1 ≤ 1 / 2
    · rcases hx.eq_or_lt with hxeq | hxlt
      · have hr : 1 - x.1 ≤ 1 / 2 := by linarith
        rw [if_pos hr, if_pos hx]
        have hxval : x.1 = 1 / 2 := hxeq
        simp only [hxval]
        norm_num
        rw [cumulative_one_of_admissible f.2]
        norm_num
      · have hr : ¬(1 - x.1 ≤ 1 / 2) := by linarith
        rw [if_neg hr, if_pos hx]
        congr 2
        ring
    · have hxlt : 1 / 2 < x.1 := lt_of_not_ge hx
      have hr : 1 - x.1 ≤ 1 / 2 := by linarith
      rw [if_pos hr, if_neg hx]
      ring_nf

/-- The transform viewed as a self-map of `admissibleSet`.  Its fixed point
is `fixedCandidate`. -/
def transformSelf (f : admissibleSet) : admissibleSet :=
  ⟨transform f, transform_admissible f⟩

private lemma norm_extend_sub_le_dist (f g : C) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖extend f t - extend g t‖ ≤ dist f g := by
  have h := ContinuousMap.dist_apply_le_dist (f := f) (g := g) ⟨t, ht⟩
  simpa [Real.dist_eq, extend_eq f ht, extend_eq g ht] using h

private lemma cumulative_sub_eq_integral (f g : C) (y : ℝ) :
    cumulative f y - cumulative g y =
      ∫ t in (0 : ℝ)..y, (extend f t - extend g t) := by
  rw [cumulative, cumulative, intervalIntegral.integral_sub]
  · exact (continuous_extend f).intervalIntegrable 0 y
  · exact (continuous_extend g).intervalIntegrable 0 y

/-- For admissible `f` and `g` and `y ∈ [0, 1]`, the two primitives differ at
`y` by at most `dist f g / 2`.  The factor `1 / 2` comes from splitting at
`y ≤ 1 / 2` and using that both primitives equal `1 / 2` at `1`; this estimate
is what makes `transformSelf` a contraction. -/
lemma norm_cumulative_sub_le_half_dist (f g : admissibleSet)
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    ‖cumulative f.1 y - cumulative g.1 y‖ ≤ (1 / 2 : ℝ) * dist f.1 g.1 := by
  let h : ℝ → ℝ := fun t => extend f.1 t - extend g.1 t
  have hcont : Continuous h := (continuous_extend f.1).sub (continuous_extend g.1)
  have htotal : (∫ t in (0 : ℝ)..1, h t) = 0 := by
    dsimp only [h]
    rw [← cumulative_sub_eq_integral, cumulative_one_of_admissible f.2,
      cumulative_one_of_admissible g.2]
    ring
  rw [cumulative_sub_eq_integral]
  change ‖∫ t in (0 : ℝ)..y, h t‖ ≤ _
  by_cases hyhalf : y ≤ 1 / 2
  · have hnorm : ‖∫ t in (0 : ℝ)..y, h t‖ ≤ dist f.1 g.1 * |y - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [uIoc_of_le hy.1] at ht
      exact norm_extend_sub_le_dist f.1 g.1
        ⟨ht.1.le, ht.2.trans hy.2⟩
    rw [sub_zero, abs_of_nonneg hy.1] at hnorm
    calc
      _ ≤ dist f.1 g.1 * y := hnorm
      _ ≤ (1 / 2 : ℝ) * dist f.1 g.1 := by
        rw [mul_comm (dist f.1 g.1)]
        exact mul_le_mul_of_nonneg_right hyhalf dist_nonneg
  · have hyhalf' : 1 / 2 ≤ y := le_of_not_ge hyhalf
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hcont.intervalIntegrable 0 y) (hcont.intervalIntegrable y 1)
    have heq : (∫ t in (0 : ℝ)..y, h t) = -∫ t in y..1, h t := by
      rw [htotal] at hadd
      linarith
    rw [heq, norm_neg]
    have hnorm : ‖∫ t in y..1, h t‖ ≤ dist f.1 g.1 * |1 - y| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [uIoc_of_le hy.2] at ht
      exact norm_extend_sub_le_dist f.1 g.1
        ⟨hy.1.trans ht.1.le, ht.2⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hy.2)] at hnorm
    calc
      _ ≤ dist f.1 g.1 * (1 - y) := hnorm
      _ ≤ (1 / 2 : ℝ) * dist f.1 g.1 := by
        rw [mul_comm (dist f.1 g.1)]
        apply mul_le_mul_of_nonneg_right _ dist_nonneg
        linarith

/-- `transformSelf` at least halves distances, uniformly over
`admissibleSet`. -/
lemma dist_transformSelf_le (f g : admissibleSet) :
    dist (transformSelf f) (transformSelf g) ≤
      (1 / 2 : ℝ) * dist f g := by
  change dist (transform f) (transform g) ≤
    (1 / 2 : ℝ) * dist f.1 g.1
  apply (ContinuousMap.dist_le (mul_nonneg (by norm_num) dist_nonneg)).2
  intro x
  rw [Real.dist_eq]
  simp only [transform, transformValue, ContinuousMap.coe_mk]
  split_ifs with hx
  · have hy : 2 * x.1 ∈ Icc (0 : ℝ) 1 := by
      constructor <;> nlinarith [x.2.1]
    exact norm_cumulative_sub_le_half_dist f g hy
  · have hy : 2 - 2 * x.1 ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [x.2.1, x.2.2]
    have h := norm_cumulative_sub_le_half_dist f g hy
    calc
      |(1 - cumulative f.1 (2 - 2 * x.1)) -
          (1 - cumulative g.1 (2 - 2 * x.1))| =
          ‖-(cumulative f.1 (2 - 2 * x.1) -
            cumulative g.1 (2 - 2 * x.1))‖ := by
        congr 1
        ring
      _ = ‖cumulative f.1 (2 - 2 * x.1) -
          cumulative g.1 (2 - 2 * x.1)‖ := norm_neg _
      _ ≤ _ := h

/-- `transformSelf` is Lipschitz with constant `1 / 2`. -/
lemma transformSelf_lipschitz :
    LipschitzWith (1 / 2 : NNReal) transformSelf := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simpa using dist_transformSelf_le f g

/-- `transformSelf` is a contraction with ratio `1 / 2`, the input to
Mathlib's Banach fixed-point theorem. -/
lemma transformSelf_contracting :
    ContractingWith (1 / 2 : NNReal) transformSelf :=
  ⟨by norm_num, transformSelf_lipschitz⟩

/-- The fixed point of `transformSelf` in `admissibleSet` supplied by the
Banach fixed-point theorem.  Its extension to `ℝ` is `boundedCandidate`. -/
noncomputable def fixedCandidate : admissibleSet :=
  transformSelf_contracting.fixedPoint transformSelf

/-- `fixedCandidate` is fixed by `transformSelf`. -/
lemma fixedCandidate_fixed : transformSelf fixedCandidate = fixedCandidate :=
  transformSelf_contracting.fixedPoint_isFixedPt

/-- Pointwise form of the fixed-point equation: at every `x ∈ I` the value of
`fixedCandidate` is its own transform value.  Every value computation below
unfolds this identity. -/
lemma fixedCandidate_eq_transformValue (x : I) :
    fixedCandidate.1 x = transformValue fixedCandidate.1 x := by
  have h := congrArg (fun f : admissibleSet => f.1 x) fixedCandidate_fixed
  exact h.symm

/-- `fixedCandidate` vanishes at the left endpoint `0`. -/
lemma fixedCandidate_zero : fixedCandidate.1 ⟨0, by constructor <;> norm_num⟩ = 0 := by
  rw [fixedCandidate_eq_transformValue]
  simp [transformValue, cumulative_zero]

/-- `fixedCandidate` takes the value `1` at the right endpoint `1`, obtained
from `fixedCandidate_zero` by the admissibility symmetry. -/
lemma fixedCandidate_one : fixedCandidate.1 ⟨1, by constructor <;> norm_num⟩ = 1 := by
  have hs := fixedCandidate.2.2 ⟨0, by constructor <;> norm_num⟩
  have hreflect : reflect ⟨0, by constructor <;> norm_num⟩ =
      ⟨1, by constructor <;> norm_num⟩ := by apply Subtype.ext; norm_num [reflect]
  rw [hreflect, fixedCandidate_zero] at hs
  simpa using hs

/-- The extension of `fixedCandidate` to `ℝ` vanishes at `0`; the `simp`
form of `fixedCandidate_zero`. -/
@[simp] lemma extend_fixedCandidate_zero : extend fixedCandidate.1 0 = 0 := by
  rw [extend_eq fixedCandidate.1 (by constructor <;> norm_num)]
  exact fixedCandidate_zero

/-- The extension of `fixedCandidate` to `ℝ` equals `1` at `1`; the `simp`
form of `fixedCandidate_one`, used to evaluate the right branch formula at
`x = 1 / 2`. -/
@[simp] lemma extend_fixedCandidate_one : extend fixedCandidate.1 1 = 1 := by
  rw [extend_eq fixedCandidate.1 (by constructor <;> norm_num)]
  exact fixedCandidate_one

/-- The candidate bounded Fabius function: `fixedCandidate` extended to all
of `ℝ` through the projection onto `[0, 1]`, repackaged with its unit-interval
codomain.  This is the `F` shown to satisfy `IsFabius` below. -/
noncomputable def boundedCandidate : Fabius.BoundedFabius := fun x =>
  ⟨extend fixedCandidate.1 x, fixedCandidate.2.1 _⟩

/-- `boundedCandidate` read as a real-valued function is the extension of
`fixedCandidate`; the definitional `simp` bridge between the two names. -/
@[simp] lemma boundedCandidate_real (x : ℝ) :
    Fabius.fabiusReal boundedCandidate x = extend fixedCandidate.1 x :=
  rfl

/-- `boundedCandidate` vanishes on `(-∞, 0]`; the `zero_of_nonpos` field of
`IsFabius`. -/
lemma boundedCandidate_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    Fabius.fabiusReal boundedCandidate x = 0 := by
  change extend fixedCandidate.1 x = 0
  rw [extend_eq_zero_of_nonpos fixedCandidate.1 hx]
  exact fixedCandidate_zero

/-- `boundedCandidate` equals `1` on `[1, ∞)`; the `one_of_one_le` field of
`IsFabius`. -/
lemma boundedCandidate_one_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    Fabius.fabiusReal boundedCandidate x = 1 := by
  change extend fixedCandidate.1 x = 1
  rw [extend_eq_one_of_one_le fixedCandidate.1 hx]
  exact fixedCandidate_one

/-- Reflection symmetry of `boundedCandidate` on `[0, 1]`, inherited from
admissibility of `fixedCandidate`; the `symmetry` field of `IsFabius`. -/
lemma boundedCandidate_symmetry (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    Fabius.fabiusReal boundedCandidate (1 - x) =
      1 - Fabius.fabiusReal boundedCandidate x := by
  change extend fixedCandidate.1 (1 - x) = 1 - extend fixedCandidate.1 x
  rw [extend_eq fixedCandidate.1 ⟨by linarith [hx.2], by linarith [hx.1]⟩,
    extend_eq fixedCandidate.1 hx]
  exact fixedCandidate.2.2 ⟨x, hx⟩

/-- On `[0, 1/2]` the candidate is given by the left branch of the fixed-point
equation, `x ↦ cumulative fixedCandidate.1 (2 * x)`. -/
lemma fixedCandidate_left_formula {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (1 / 2)) :
    Fabius.fabiusReal boundedCandidate x = cumulative fixedCandidate.1 (2 * x) := by
  change extend fixedCandidate.1 x = _
  rw [extend_eq fixedCandidate.1 ⟨hx.1, hx.2.trans (by norm_num)⟩]
  rw [fixedCandidate_eq_transformValue]
  rw [transformValue, if_pos hx.2]

/-- On `[1/2, 1]` the candidate is given by the right branch of the
fixed-point equation, `x ↦ 1 - cumulative fixedCandidate.1 (2 - 2 * x)`; at
`x = 1 / 2` this uses `cumulative_one_of_admissible` to reconcile the two
branches. -/
lemma fixedCandidate_right_formula {x : ℝ}
    (hx : x ∈ Icc (1 / 2 : ℝ) 1) :
    Fabius.fabiusReal boundedCandidate x =
      1 - cumulative fixedCandidate.1 (2 - 2 * x) := by
  change extend fixedCandidate.1 x = _
  rw [extend_eq fixedCandidate.1 ⟨(by linarith [hx.1] : 0 ≤ x), hx.2⟩]
  rw [fixedCandidate_eq_transformValue]
  by_cases heq : x = 1 / 2
  · subst x
    rw [transformValue, if_pos le_rfl]
    norm_num
    rw [cumulative_one_of_admissible fixedCandidate.2]
    norm_num
  · rw [transformValue, if_neg (not_le.mpr (lt_of_le_of_ne hx.1 (Ne.symm heq)))]

/-- Fundamental theorem of calculus for the fixed point: at every real `y`
the primitive `cumulative fixedCandidate.1` has derivative
`extend fixedCandidate.1 y`. -/
lemma cumulative_fixed_hasDerivAt (y : ℝ) :
    HasDerivAt (cumulative fixedCandidate.1) (extend fixedCandidate.1 y) y :=
  cumulative_hasDerivAt fixedCandidate.1 y

/-- Chain rule for the left branch: `z ↦ cumulative fixedCandidate.1 (2 * z)`
has derivative `2 * extend fixedCandidate.1 (2 * x)` at every real `x`. -/
lemma leftFormula_hasDerivAt (x : ℝ) :
    HasDerivAt (fun z : ℝ => cumulative fixedCandidate.1 (2 * z))
      (2 * extend fixedCandidate.1 (2 * x)) x := by
  have hinner : HasDerivAt (fun z : ℝ => 2 * z) 2 x :=
    by simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul 2
  have h := (cumulative_fixed_hasDerivAt (2 * x)).comp x hinner
  simpa [Function.comp_def, mul_comm] using h

/-- Chain rule for the right branch:
`z ↦ 1 - cumulative fixedCandidate.1 (2 - 2 * z)` has derivative
`2 * extend fixedCandidate.1 (2 - 2 * x)` at every real `x`. -/
lemma rightFormula_hasDerivAt (x : ℝ) :
    HasDerivAt (fun z : ℝ => 1 - cumulative fixedCandidate.1 (2 - 2 * z))
      (2 * extend fixedCandidate.1 (2 - 2 * x)) x := by
  have hinner : HasDerivAt (fun z : ℝ => 2 - 2 * z) (-2) x :=
    by simpa only [id_eq, neg_mul, mul_one] using
      ((hasDerivAt_id x).const_mul 2).const_sub 2
  have hcomp := (cumulative_fixed_hasDerivAt (2 - 2 * x)).comp x hinner
  have h := hcomp.const_sub 1
  simpa only [Function.comp_def, Pi.sub_apply, id_eq, zero_sub, mul_neg,
    mul_one, neg_neg] using h.congr_deriv (by ring)

private lemma boundedCandidate_hasDerivAt_zero :
    HasDerivAt (Fabius.fabiusReal boundedCandidate) 0 0 := by
  have hleft : HasDerivWithinAt (Fabius.fabiusReal boundedCandidate) 0 (Iic 0) 0 := by
    apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).hasDerivWithinAt.congr
    · intro y hy
      exact boundedCandidate_zero_of_nonpos hy
    · exact boundedCandidate_zero_of_nonpos le_rfl
  have hright : HasDerivWithinAt (Fabius.fabiusReal boundedCandidate) 0
      (Icc (0 : ℝ) (1 / 2)) 0 := by
    have hglobal : HasDerivAt
        (fun z : ℝ => cumulative fixedCandidate.1 (2 * z)) 0 0 := by
      simpa using leftFormula_hasDerivAt 0
    have h := hglobal.hasDerivWithinAt (s := Icc (0 : ℝ) (1 / 2))
    apply h.congr
    · intro y hy
      exact fixedCandidate_left_formula hy
    · exact fixedCandidate_left_formula (by constructor <;> norm_num)
  apply (hleft.union hright).hasDerivAt
  apply mem_of_superset (Icc_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
    (show (0 : ℝ) < 1 / 4 by norm_num))
  intro y hy
  by_cases hy0 : y ≤ 0
  · exact Or.inl hy0
  · exact Or.inr ⟨le_of_not_ge hy0, by linarith [hy.2]⟩

private lemma boundedCandidate_hasDerivAt_half :
    HasDerivAt (Fabius.fabiusReal boundedCandidate) 2 (1 / 2) := by
  have hleft : HasDerivWithinAt (Fabius.fabiusReal boundedCandidate) 2
      (Icc (0 : ℝ) (1 / 2)) (1 / 2) := by
    have hglobal : HasDerivAt
        (fun z : ℝ => cumulative fixedCandidate.1 (2 * z)) 2 (1 / 2) := by
      simpa using leftFormula_hasDerivAt (1 / 2)
    have h := hglobal.hasDerivWithinAt (s := Icc (0 : ℝ) (1 / 2))
    apply h.congr
    · intro y hy
      exact fixedCandidate_left_formula hy
    · exact fixedCandidate_left_formula (by constructor <;> norm_num)
  have hright : HasDerivWithinAt (Fabius.fabiusReal boundedCandidate) 2
      (Icc (1 / 2 : ℝ) 1) (1 / 2) := by
    have hglobal : HasDerivAt
        (fun z : ℝ => 1 - cumulative fixedCandidate.1 (2 - 2 * z)) 2 (1 / 2) := by
      have h := rightFormula_hasDerivAt (1 / 2)
      have harg : (2 : ℝ) - 2 * (1 / 2) = 1 := by norm_num
      rw [harg, extend_fixedCandidate_one] at h
      norm_num at h ⊢
      exact h
    have h := hglobal.hasDerivWithinAt (s := Icc (1 / 2 : ℝ) 1)
    apply h.congr
    · intro y hy
      exact fixedCandidate_right_formula hy
    · exact fixedCandidate_right_formula (by constructor <;> norm_num)
  apply (hleft.union hright).hasDerivAt
  apply mem_of_superset (Icc_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) < 1 by norm_num))
  intro y hy
  by_cases h : y ≤ 1 / 2
  · exact Or.inl ⟨hy.1, h⟩
  · exact Or.inr ⟨le_of_not_ge h, hy.2⟩

private lemma boundedCandidate_hasDerivAt_one :
    HasDerivAt (Fabius.fabiusReal boundedCandidate) 0 1 := by
  have hleft : HasDerivWithinAt (Fabius.fabiusReal boundedCandidate) 0
      (Icc (1 / 2 : ℝ) 1) 1 := by
    have hglobal : HasDerivAt
        (fun z : ℝ => 1 - cumulative fixedCandidate.1 (2 - 2 * z)) 0 1 := by
      simpa using rightFormula_hasDerivAt 1
    have h := hglobal.hasDerivWithinAt (s := Icc (1 / 2 : ℝ) 1)
    apply h.congr
    · intro y hy
      exact fixedCandidate_right_formula hy
    · exact fixedCandidate_right_formula (by constructor <;> norm_num)
  have hright : HasDerivWithinAt (Fabius.fabiusReal boundedCandidate) 0 (Ici 1) 1 := by
    apply (hasDerivAt_const (1 : ℝ) (1 : ℝ)).hasDerivWithinAt.congr
    · intro y hy
      exact boundedCandidate_one_of_one_le hy
    · exact boundedCandidate_one_of_one_le le_rfl
  apply (hleft.union hright).hasDerivAt
  apply mem_of_superset (Icc_mem_nhds (show (3 / 4 : ℝ) < 1 by norm_num)
    (show (1 : ℝ) < 2 by norm_num))
  intro y hy
  by_cases hy1 : 1 ≤ y
  · exact Or.inr hy1
  · exact Or.inl ⟨by linarith [hy.1], le_of_not_ge hy1⟩

/-- Global first-derivative identity: at every real `x` the candidate is
differentiable with derivative `2 * rvachevUp boundedCandidate (2 * x - 1)`.
The two branch formulas cover the open pieces and the three private endpoint
lemmas above supply the gluing points `0`, `1 / 2` and `1`. -/
lemma boundedCandidate_hasDerivAt (x : ℝ) :
    HasDerivAt (Fabius.fabiusReal boundedCandidate)
      (2 * Fabius.rvachevUp boundedCandidate (2 * x - 1)) x := by
  rcases lt_trichotomy x 0 with hxneg | rfl | hxpos
  · have hcoeff : 2 * Fabius.rvachevUp boundedCandidate (2 * x - 1) = 0 := by
      rw [Fabius.rvachevUp, if_pos (by linarith),
        boundedCandidate_zero_of_nonpos (by linarith)]
      ring
    rw [hcoeff]
    apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hxneg] with y hy
    exact boundedCandidate_zero_of_nonpos hy.le
  · have hcoeff : 2 * Fabius.rvachevUp boundedCandidate (2 * 0 - 1) = 0 := by
      rw [Fabius.rvachevUp, if_pos (by norm_num),
        boundedCandidate_zero_of_nonpos (by norm_num)]
      ring
    rw [hcoeff]
    exact boundedCandidate_hasDerivAt_zero
  · rcases lt_trichotomy x (1 / 2) with hxhalf | hxeq | hxhalf
    · have hcoeff : 2 * Fabius.rvachevUp boundedCandidate (2 * x - 1) =
          2 * extend fixedCandidate.1 (2 * x) := by
        rw [Fabius.rvachevUp, if_pos (by linarith)]
        change 2 * extend fixedCandidate.1 (2 * x - 1 + 1) = _
        congr 2
        ring
      rw [hcoeff]
      apply (leftFormula_hasDerivAt x).congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds hxpos hxhalf] with y hy
      exact fixedCandidate_left_formula ⟨hy.1.le, hy.2.le⟩
    · subst x
      have hcoeff : 2 * Fabius.rvachevUp boundedCandidate (2 * (1 / 2) - 1) = 2 := by
        rw [Fabius.rvachevUp, if_pos (by norm_num)]
        norm_num
      rw [hcoeff]
      exact boundedCandidate_hasDerivAt_half
    · rcases lt_trichotomy x 1 with hxone | rfl | hxone
      · have hcoeff : 2 * Fabius.rvachevUp boundedCandidate (2 * x - 1) =
            2 * extend fixedCandidate.1 (2 - 2 * x) := by
          rw [Fabius.rvachevUp, if_neg (by linarith)]
          change 2 * extend fixedCandidate.1 (1 - (2 * x - 1)) = _
          congr 2
          ring
        rw [hcoeff]
        apply (rightFormula_hasDerivAt x).congr_of_eventuallyEq
        filter_upwards [Ioo_mem_nhds hxhalf hxone] with y hy
        exact fixedCandidate_right_formula ⟨hy.1.le, hy.2.le⟩
      · have hcoeff : 2 * Fabius.rvachevUp boundedCandidate (2 * 1 - 1) = 0 := by
          rw [Fabius.rvachevUp, if_neg (by norm_num),
            boundedCandidate_zero_of_nonpos (by norm_num)]
          ring
        rw [hcoeff]
        exact boundedCandidate_hasDerivAt_one
      · have hcoeff : 2 * Fabius.rvachevUp boundedCandidate (2 * x - 1) = 0 := by
          rw [Fabius.rvachevUp, if_neg (by linarith),
            boundedCandidate_zero_of_nonpos (by linarith)]
          ring
        rw [hcoeff]
        apply (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq
        filter_upwards [Ioi_mem_nhds hxone] with y hy
        exact boundedCandidate_one_of_one_le hy.le

/-- The folded candidate `rvachevUp boundedCandidate` is even, a special case
of `rvachevUp_even`. -/
lemma rvachevCandidate_even :
    Function.Even (Fabius.rvachevUp boundedCandidate) := by
  exact Fabius.rvachevUp_even boundedCandidate

/-- Rvachev's dyadic differential refinement equation for the candidate: at
every real `x`, writing `u` for `rvachevUp boundedCandidate`, the derivative of
`u` at `x` is `2 * (u (2 * x + 1) - u (2 * x - 1))`.  This is the hypothesis
fed to `contDiff_of_hasDerivAt_dyadic_refinement`. -/
lemma rvachevCandidate_hasDerivAt (x : ℝ) :
    HasDerivAt (Fabius.rvachevUp boundedCandidate)
      (2 * (Fabius.rvachevUp boundedCandidate (2 * x + 1) -
        Fabius.rvachevUp boundedCandidate (2 * x - 1))) x := by
  exact Fabius.rvachevUp_hasDerivAt_of_fabiusReal_hasDerivAt
    boundedCandidate (fun _x hx => boundedCandidate_zero_of_nonpos hx)
    boundedCandidate_hasDerivAt x

/-- The folded candidate is `C^∞` on `ℝ`, obtained by feeding its refinement
equation to `contDiff_of_hasDerivAt_dyadic_refinement`. -/
lemma rvachevCandidate_contDiff :
    ContDiff ℝ ∞ (Fabius.rvachevUp boundedCandidate) := by
  exact Fabius.contDiff_of_hasDerivAt_dyadic_refinement _ rvachevCandidate_hasDerivAt

/-- `boundedCandidate` is `C^∞` on `ℝ`: it is differentiable everywhere and
its derivative is a constant multiple of an affine rescaling of the `C^∞`
function `rvachevUp boundedCandidate`.  This is the `contDiff` field of
`IsFabius`. -/
lemma boundedCandidate_contDiff :
    ContDiff ℝ ∞ (Fabius.fabiusReal boundedCandidate) := by
  have hdifferentiable : Differentiable ℝ
      (Fabius.fabiusReal boundedCandidate) :=
    fun x => (boundedCandidate_hasDerivAt x).differentiableAt
  rw [contDiff_infty_iff_deriv]
  refine ⟨hdifferentiable, ?_⟩
  have hderiv : deriv (Fabius.fabiusReal boundedCandidate) = fun x : ℝ =>
      2 * Fabius.rvachevUp boundedCandidate (2 * x - 1) := by
    funext x
    exact (boundedCandidate_hasDerivAt x).deriv
  rw [hderiv]
  exact contDiff_const.mul
    (rvachevCandidate_contDiff.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const))

/-- `boundedCandidate` satisfies the `IsFabius` characterization, assembling
the two constant tails, `C^∞` regularity, the reflection symmetry, and the
derivative equation on `[0, 1/2]`.  This is the existence half of
`existsUnique`. -/
lemma boundedCandidate_isFabius :
    Fabius.IsFabius boundedCandidate where
  zero_of_nonpos := fun _x hx => boundedCandidate_zero_of_nonpos hx
  one_of_one_le := fun _x hx => boundedCandidate_one_of_one_le hx
  contDiff := boundedCandidate_contDiff
  symmetry := boundedCandidate_symmetry
  hasDerivAt := by
    intro x hx
    have h := boundedCandidate_hasDerivAt x
    have hnonpos : 2 * x - 1 ≤ 0 := by linarith [hx.2]
    rw [Fabius.rvachevUp, if_pos hnonpos] at h
    convert h using 1
    congr 2
    ring

/-- Uniqueness: two bounded functions satisfying `IsFabius` are equal.  They
agree at every dyadic rational by `fabiusDyadic_cast`, and the continuity
contained in the `contDiff` field propagates that along the approximations
`⌊x * 2 ^ n⌋₊ / 2 ^ n` of an arbitrary point of `[0, 1]`. -/
lemma isFabius_eq (F G : Fabius.BoundedFabius)
    (hF : Fabius.IsFabius F) (hG : Fabius.IsFabius G) :
    F = G := by
  funext x
  apply Subtype.ext
  change Fabius.fabiusReal F x = Fabius.fabiusReal G x
  by_cases hx0 : x ≤ 0
  · rw [hF.zero_of_nonpos x hx0, hG.zero_of_nonpos x hx0]
  by_cases hx1 : 1 ≤ x
  · rw [hF.one_of_one_le x hx1, hG.one_of_one_le x hx1]
  have hxpos : 0 ≤ x := (lt_of_not_ge hx0).le
  have hxle : x ≤ 1 := (lt_of_not_ge hx1).le
  let u : ℕ → ℝ := fun n =>
    (⌊x * (2 : ℝ) ^ n⌋₊ : ℝ) / (2 : ℝ) ^ n
  have hpow : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hu : Tendsto u atTop (𝓝 x) := by
    exact (tendsto_nat_floor_mul_div_atTop hxpos).comp hpow
  have heq (n : ℕ) : Fabius.fabiusReal F (u n) =
      Fabius.fabiusReal G (u n) := by
    let a := ⌊x * (2 : ℝ) ^ n⌋₊
    have ha : a ≤ 2 ^ n := by
      have haReal : (a : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by
        rw [Nat.cast_pow, Nat.cast_ofNat]
        exact (Nat.floor_le (mul_nonneg hxpos (by positivity))).trans
          (mul_le_of_le_one_left (by positivity) hxle)
      exact (Nat.cast_le (α := ℝ)).mp haReal
    change Fabius.fabiusReal F ((a : ℝ) / (2 : ℝ) ^ n) =
      Fabius.fabiusReal G ((a : ℝ) / (2 : ℝ) ^ n)
    rw [← Fabius.fabiusDyadic_cast F hF n a ha,
      ← Fabius.fabiusDyadic_cast G hG n a ha]
  have hlimF : Tendsto (fun n => Fabius.fabiusReal F (u n)) atTop
      (𝓝 (Fabius.fabiusReal F x)) :=
    hF.contDiff.continuous.continuousAt.tendsto.comp hu
  have hlimG : Tendsto (fun n => Fabius.fabiusReal G (u n)) atTop
      (𝓝 (Fabius.fabiusReal G x)) :=
    hG.contDiff.continuous.continuousAt.tendsto.comp hu
  have hevent : (fun n => Fabius.fabiusReal F (u n)) =ᶠ[atTop]
      (fun n => Fabius.fabiusReal G (u n)) :=
    Filter.Eventually.of_forall heq
  exact tendsto_nhds_unique hlimF (hlimG.congr' hevent.symm)

/-- There is exactly one bounded Fabius function: `boundedCandidate` supplies
existence and `isFabius_eq` supplies uniqueness.  Re-exported outside the
`Existence` namespace as `Fabius.existsUnique_fabius`. -/
theorem existsUnique :
    ∃! F : Fabius.BoundedFabius, Fabius.IsFabius F := by
  refine ⟨boundedCandidate, boundedCandidate_isFabius, ?_⟩
  intro F hF
  exact isFabius_eq F boundedCandidate hF boundedCandidate_isFabius

end
end Existence

/-- There exists a unique bounded Fabius function satisfying IsFabius. -/
theorem existsUnique_fabius :
    ∃! F : BoundedFabius, IsFabius F :=
  Existence.existsUnique

/-- Any two bounded functions satisfying the Fabius characterization agree. -/
theorem IsFabius.eq {F G : BoundedFabius} (hF : IsFabius F) (hG : IsFabius G) :
    F = G :=
  Existence.isFabius_eq F G hF hG

/-- Bundled bounded Fabius functions form a subsingleton. -/
instance fabiusFunctionSubsingleton : Subsingleton FabiusFunction where
  allEq F G := Subtype.ext (F.property.eq G.property)

end Fabius
```

### `UnconditionalEndpoint.lean`

```lean
import ProveItExistence
import AnalyticDenominatorEndpoint
import ArithmeticEndpoint

namespace FabiusProofLane

/-- Explicit non-vacuity of the analytic characterization. The construction is
third-party ProveIt mathematics, not a new existence result of this packet. -/
theorem certified_fabius_exists :
    ∃ F : Fabius.BoundedFabius, Fabius.IsFabius F :=
  Fabius.existsUnique_fabius.exists

/-- Arias de Reyna's full Conjecture 16 for the unique bounded Fabius function,
with the exact least-positive-common-denominator meaning certified in Lean. -/
theorem arias_de_reyna_conjecture_16 :
    ∃! F : Fabius.BoundedFabius, Fabius.IsFabius F ∧
      Fabius.conjecture_sixteen ∧
      ∀ n : ℕ, IsLeast
        {d : ℕ | 0 < d ∧ ClearsAnalyticRvachev F n d}
        (Fabius.dyadicDenominator n) := by
  obtain ⟨F, hF, huniq⟩ := Fabius.existsUnique_fabius
  refine ⟨F, ⟨hF, full_fabius_conjecture_with_analytic_meaning F hF⟩, ?_⟩
  intro G hG
  exact huniq G hG.1

#print certified_fabius_exists
#print arias_de_reyna_conjecture_16
#print Fabius.IsFabius
#print Fabius.conjecture_sixteen
#print ClearsAnalyticRvachev
#check Fabius.fabiusDyadic_cast
#print axioms certified_fabius_exists
#print axioms Fabius.existsUnique_fabius
#print axioms Fabius.fabiusDyadic_cast
#print axioms source_D_isLeast_analytic
#print axioms arias_de_reyna_conjecture_16
end FabiusProofLane
```

