# Lean source appendix — MathDB 351157

Complete source packet. Exact endpoint: `labbe_lapointe_conj_1_3`.

### `MarkoffStatement.lean`

```lean
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Range
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

open Polynomial
noncomputable section

def mu0 : Matrix (Fin 2) (Fin 2) (Polynomial ℤ) := !![X + X^2, 1; X, 1]
def mu1 : Matrix (Fin 2) (Fin 2) (Polynomial ℤ) :=
  !![X + 2*X^2 + X^3 + X^4, 1 + X; X + X^2, 1]
def muq (w : List Bool) : Matrix (Fin 2) (Fin 2) (Polynomial ℤ) :=
  (w.map fun b => if b then mu1 else mu0).prod

def onesIn (s : ℤ → Bool) (i : ℤ) (l : ℕ) : ℕ :=
  ((List.range l).filter fun t => s (i + t)).length

def BalancedSeq (s : ℤ → Bool) : Prop :=
  ∀ (i j : ℤ) (l : ℕ), (onesIn s i l : ℤ) - onesIn s j l ≤ 1

def IsFactor (w : List Bool) (s : ℤ → Bool) : Prop :=
  ∃ i : ℤ, w = List.ofFn fun t : Fin w.length => s (i + t)

def LB : Set (List Bool) := {w | ∃ s, BalancedSeq s ∧ IsFactor w s}

def ones (w : List Bool) : ℕ := (w.filter id).length

def FiniteBalanced (w : List Bool) : Prop :=
  ∀ i j l : ℕ, i + l ≤ w.length → j + l ≤ w.length →
    (ones ((w.drop i).take l) : ℤ) - ones ((w.drop j).take l) ≤ 1

@[simp] theorem muq_nil : muq [] = 1 := rfl
@[simp] theorem muq_cons (b : Bool) (w : List Bool) :
    muq (b :: w) = (if b then mu1 else mu0) * muq w := by
  simp [muq]
theorem muq_append (u v : List Bool) : muq (u ++ v) = muq u * muq v := by
  simp [muq, List.prod_append]

@[simp] theorem onesIn_zero (s : ℤ → Bool) (i : ℤ) : onesIn s i 0 = 0 := rfl

theorem onesIn_succ (s : ℤ → Bool) (i : ℤ) (l : ℕ) :
    onesIn s i (l+1) = onesIn s i l + if s (i + l) then 1 else 0 := by
  cases h : s (i+l) <;> simp [onesIn, List.range_succ, List.filter_append, h]

theorem onesIn_add (s : ℤ → Bool) (i : ℤ) (l m : ℕ) :
    onesIn s i (l+m) = onesIn s i l + onesIn s (i+l) m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show l + (m+1) = (l+m)+1 by omega, onesIn_succ, ih, onesIn_succ]
    simp [Nat.cast_add, add_assoc]

theorem factor_get {w : List Bool} {s : ℤ → Bool} {i : ℤ}
    (h : w = List.ofFn fun t : Fin w.length => s (i+t))
    (t : ℕ) (ht : t < w.length) : w[t] = s (i+t) := by
  have e := congrArg (fun l : List Bool => l[t]?) h
  simpa [List.getElem?_eq_getElem ht, List.getElem?_ofFn, ht] using e

#print axioms muq_append
#print axioms onesIn_add
#print axioms factor_get
```

### `MarkoffChecks.lean`

```lean
import MarkoffStatement
import Mathlib.Tactic.IntervalCases

open Polynomial

/-- The source's example pins both product direction and the selected entry. -/
theorem source_example_00101 :
    muq [false,false,true,false,true] 0 1 =
      1 + 4*X + 10*X^2 + 18*X^3 + 27*X^4 + 33*X^5 +
      33*X^6 + 29*X^7 + 21*X^8 + 12*X^9 + 5*X^10 + X^11 := by
  simp [muq, mu0, mu1, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem noninjective_pair :
    muq [false,false,false,true,true] 0 1 = muq [false,true,false,false,true] 0 1 := by
  simp [muq, mu0, mu1, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Reduction to a finite window test for a periodic sequence. -/
theorem balanced_of_period (s : ℤ → Bool) (p k : ℕ) (hp : 0 < p)
    (full : ∀ i, onesIn s i p = k)
    (short : ∀ i j l, l < p → (onesIn s i l : ℤ) - onesIn s j l ≤ 1) :
    BalancedSeq s := by
  intro i j l
  induction l using Nat.strong_induction_on generalizing i j with
  | h l ih =>
    by_cases hl : l < p
    · exact short i j l hl
    · have hpl : p ≤ l := by omega
      have hlt : l - p < l := by omega
      have hrec := ih (l-p) hlt
      rw [show l = p + (l-p) by omega, onesIn_add, onesIn_add, full, full]
      push_cast
      have hh := hrec (i+p) (j+p)
      omega

def periodic5 (i : ℤ) : Bool := decide (i % 5 = 2 ∨ i % 5 = 4)
def periodic4 (i : ℤ) : Bool := decide (i % 4 = 1)

theorem onesIn_congr {s t : ℤ → Bool} {i j : ℤ} (l : ℕ)
    (h : ∀ r : ℕ, r < l → s (i+r) = t (j+r)) :
    onesIn s i l = onesIn t j l := by
  induction l with
  | zero => rfl
  | succ l ih =>
    rw [onesIn_succ, onesIn_succ, ih (fun r hr => h r (by omega)), h l (by omega)]

theorem periodic5_reduce (i : ℤ) (l : ℕ) :
    onesIn periodic5 i l = onesIn periodic5 (i%5) l := by
  apply onesIn_congr
  intro r _
  simp [periodic5, Int.add_emod]

theorem periodic4_reduce (i : ℤ) (l : ℕ) :
    onesIn periodic4 i l = onesIn periodic4 (i%4) l := by
  apply onesIn_congr
  intro r _
  simp [periodic4, Int.add_emod]

theorem periodic5_balanced : BalancedSeq periodic5 := by
  apply balanced_of_period periodic5 5 2 (by decide)
  · intro i
    rw [periodic5_reduce]
    have h0 := Int.emod_nonneg i (by decide : (5 : ℤ) ≠ 0)
    have h1 := Int.emod_lt_of_pos i (by decide : (0 : ℤ) < 5)
    interval_cases hi : i%5 <;> decide
  · intro i j l hl
    rw [periodic5_reduce i l, periodic5_reduce j l]
    have hi0 := Int.emod_nonneg i (by decide : (5 : ℤ) ≠ 0)
    have hi1 := Int.emod_lt_of_pos i (by decide : (0 : ℤ) < 5)
    have hj0 := Int.emod_nonneg j (by decide : (5 : ℤ) ≠ 0)
    have hj1 := Int.emod_lt_of_pos j (by decide : (0 : ℤ) < 5)
    interval_cases hi : i%5 <;> interval_cases hj : j%5 <;> interval_cases l <;> decide

theorem periodic4_balanced : BalancedSeq periodic4 := by
  apply balanced_of_period periodic4 4 1 (by decide)
  · intro i
    rw [periodic4_reduce]
    have h0 := Int.emod_nonneg i (by decide : (4 : ℤ) ≠ 0)
    have h1 := Int.emod_lt_of_pos i (by decide : (0 : ℤ) < 4)
    interval_cases hi : i%4 <;> decide
  · intro i j l hl
    rw [periodic4_reduce i l, periodic4_reduce j l]
    have hi0 := Int.emod_nonneg i (by decide : (4 : ℤ) ≠ 0)
    have hi1 := Int.emod_lt_of_pos i (by decide : (0 : ℤ) < 4)
    have hj0 := Int.emod_nonneg j (by decide : (4 : ℤ) ≠ 0)
    have hj1 := Int.emod_lt_of_pos j (by decide : (0 : ℤ) < 4)
    interval_cases hi : i%4 <;> interval_cases hj : j%4 <;> interval_cases l <;> decide

theorem witness_u_mem : [false,false,true,false,true,false,false] ∈ LB := by
  refine ⟨periodic5, periodic5_balanced, 0, ?_⟩
  decide

theorem witness_v_mem : [false,true,false,false,false,true,false] ∈ LB := by
  refine ⟨periodic4, periodic4_balanced, 0, ?_⟩
  decide

theorem witnesses_equal_counts :
    ones [false,false,true,false,true,false,false] =
    ones [false,true,false,false,false,true,false] := by decide

theorem witnesses_distinct :
    ([false,false,true,false,true,false,false] : List Bool) ≠
    [false,true,false,false,false,true,false] := by decide

#print axioms source_example_00101
#print axioms noninjective_pair
#print axioms witness_u_mem
#print axioms witness_v_mem
```

### `MarkoffFactors.lean`

```lean
import MarkoffStatement

noncomputable section

@[simp] theorem ones_append (u v : List Bool) : ones (u ++ v) = ones u + ones v := by
  simp [ones, List.filter_append]

theorem ones_take_succ (w : List Bool) (t : ℕ) (ht : t < w.length) :
    ones (w.take (t+1)) = ones (w.take t) + if w[t] then 1 else 0 := by
  rw [List.take_add_one, List.getElem?_eq_getElem ht]
  cases w[t] <;> simp [ones]

theorem factor_window_count {w : List Bool} {s : ℤ → Bool} {a : ℤ}
    (h : w = List.ofFn fun t : Fin w.length => s (a+t))
    (i l : ℕ) (hi : i+l ≤ w.length) :
    ones ((w.drop i).take l) = onesIn s (a+i) l := by
  induction l with
  | zero => simp [ones]
  | succ l ih =>
    rw [ones_take_succ (w.drop i) l (by simp only [List.length_drop]; omega), onesIn_succ]
    rw [ih (by omega)]
    have hget := factor_get h (i+l) (by omega)
    have hget' : (w.drop i)[l]'(by simp only [List.length_drop]; omega) = s ((a+i)+l) := by
      simpa [List.getElem_drop, Nat.cast_add, add_assoc] using hget
    rw [hget']

theorem LB_finiteBalanced {w : List Bool} (h : w ∈ LB) : FiniteBalanced w := by
  obtain ⟨s,hs,a,ha⟩ := h
  intro i j l hi hj
  rw [factor_window_count ha i l hi, factor_window_count ha j l hj]
  exact hs (a+i) (a+j) l

/-- The two witnesses cannot be compared by injectivity on one fixed language. -/
theorem witnesses_no_common_sequence :
    ¬ ∃ s : ℤ → Bool, BalancedSeq s ∧
      IsFactor [false,false,true,false,true,false,false] s ∧
      IsFactor [false,true,false,false,false,true,false] s := by
  rintro ⟨s,hs,⟨a,ha⟩,⟨b,hb⟩⟩
  have hc := hs (a+2) (b+2) 3
  have hca := factor_window_count ha 2 3 (by decide)
  have hcb := factor_window_count hb 2 3 (by decide)
  norm_num [ones] at hca hcb
  rw [← hca, ← hcb] at hc
  norm_num [ones] at hc

theorem unbalanced_00011_not_mem : [false,false,false,true,true] ∉ LB := by
  intro h
  have hb := LB_finiteBalanced h
  have hh := hb 3 0 2 (by decide) (by decide)
  norm_num [ones] at hh

#print axioms factor_window_count
#print axioms LB_finiteBalanced
#print axioms witnesses_no_common_sequence
#print axioms unbalanced_00011_not_mem
```

### `BalancedFloor.lean`

```lean
import MarkoffStatement
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section

/-- Number of ones in a contiguous finite window, with truncation outside the word. -/
def windowCount (w : List Bool) (i l : ℕ) : ℤ := ones ((w.drop i).take l)

def prefixCount (w : List Bool) (t : ℕ) : ℤ := ones (w.take t)

@[simp] theorem prefixCount_zero (w : List Bool) : prefixCount w 0 = 0 := rfl
@[simp] theorem prefixCount_length (w : List Bool) :
    prefixCount w w.length = ones w := by simp [prefixCount]

theorem windowCount_add (w : List Bool) (i l m : ℕ) :
    windowCount w i (l+m) = windowCount w i l + windowCount w (i+l) m := by
  simp [windowCount, List.take_add, List.drop_drop, ones, List.filter_append]

theorem prefixCount_add (w : List Bool) (i l : ℕ) :
    prefixCount w (i+l) = prefixCount w i + windowCount w i l := by
  simpa [prefixCount, windowCount] using windowCount_add w 0 i l

/-- Euclidean subtraction of window lengths gives the strict cross-window bound. -/
theorem balanced_cross_window (w : List Bool) (hb : FiniteBalanced w)
    (i j l m : ℕ) (hl : 0 < l) (hm : 0 < m)
    (hi : i+l ≤ w.length) (hj : j+m ≤ w.length) :
    windowCount w i l * m - windowCount w j m * l < (l : ℤ) + m := by
  have main : ∀ N : ℕ, ∀ i j l m : ℕ, l+m = N → 0 < l → 0 < m →
      i+l ≤ w.length → j+m ≤ w.length →
      windowCount w i l * m - windowCount w j m * l < (l : ℤ) + m := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro i j l m hN hl hm hi hj
      by_cases he : l = m
      · subst m
        have hbal : windowCount w i l - windowCount w j l ≤ 1 := hb i j l hi hj
        have hp : (0 : ℤ) < l := by omega
        nlinarith
      · by_cases hlt : l < m
        · have hbal : windowCount w i l - windowCount w j l ≤ 1 :=
            hb i j l hi (by omega)
          have hr := ih (l+(m-l)) (by omega) i (j+l) l (m-l) rfl hl
            (by omega) hi (by omega)
          have heq := windowCount_add w j l (m-l)
          have hcast : (m : ℤ) = (l : ℤ) + (m-l : ℕ) := by omega
          rw [show l+(m-l) = m by omega] at heq
          have hp : (0 : ℤ) < l := by omega
          rw [heq, hcast]
          nlinarith [mul_le_mul_of_nonneg_right hbal (le_of_lt hp)]
        · have hbal : windowCount w i m - windowCount w j m ≤ 1 :=
            hb i j m (by omega) hj
          have hr := ih ((l-m)+m) (by omega) (i+m) j (l-m) m rfl
            (by omega) hm (by omega) hj
          have heq := windowCount_add w i m (l-m)
          have hcast : (l : ℤ) = (m : ℤ) + (l-m : ℕ) := by omega
          rw [show m+(l-m) = l by omega] at heq
          have hp : (0 : ℤ) < m := by omega
          rw [heq, hcast]
          nlinarith [mul_le_mul_of_nonneg_right hbal (le_of_lt hp)]
  exact main (l+m) i j l m rfl hl hm hi hj

/-- Elementary one-dimensional strict finite Helly lemma. -/
theorem finite_strict_separation {ι : Type*} (s : Finset ι) (lo hi : ι → ℝ)
    (h : ∀ i ∈ s, ∀ j ∈ s, lo i < hi j) :
    ∃ x : ℝ, ∀ i ∈ s, lo i < x ∧ x < hi i := by
  classical
  by_cases hs : s.Nonempty
  · obtain ⟨a, ha, hmax⟩ := s.exists_max_image lo hs
    obtain ⟨b, hb, hmin⟩ := s.exists_min_image hi hs
    obtain ⟨x, hx0, hx1⟩ := exists_between (h a ha b hb)
    exact ⟨x, fun i hi => ⟨lt_of_le_of_lt (hmax i hi) hx0,
      lt_of_lt_of_le hx1 (hmin i hi)⟩⟩
  · exact ⟨0, fun i hi => False.elim (hs ⟨i, hi⟩)⟩

/-- The finite family of all positive-length windows. -/
def windows (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (n+1)).product (Finset.range (n+1))).filter
    (fun x => 0 < x.2 ∧ x.1+x.2 ≤ n)

@[simp] theorem mem_windows (n i l : ℕ) :
    (i,l) ∈ windows n ↔ 0 < l ∧ i+l ≤ n := by
  simp [windows, Finset.mem_product]
  omega

/-- A common slope strictly approximates the count in every window. -/
theorem balanced_strict_slope (w : List Bool) (hb : FiniteBalanced w) :
    ∃ α : ℝ, ∀ i l : ℕ, 0 < l → i+l ≤ w.length →
      (windowCount w i l : ℝ) - 1 < l*α ∧
      l*α < (windowCount w i l : ℝ) + 1 := by
  let lo : ℕ × ℕ → ℝ := fun x => ((windowCount w x.1 x.2 : ℝ)-1) / x.2
  let hi : ℕ × ℕ → ℝ := fun x => ((windowCount w x.1 x.2 : ℝ)+1) / x.2
  have hpair : ∀ a ∈ windows w.length, ∀ b ∈ windows w.length, lo a < hi b := by
    intro ⟨i,l⟩ ha ⟨j,m⟩ hb'
    obtain ⟨hl,hi'⟩ := (mem_windows _ _ _).mp ha
    obtain ⟨hm,hj⟩ := (mem_windows _ _ _).mp hb'
    have hc := balanced_cross_window w hb i j l m hl hm hi' hj
    have hc' : (windowCount w i l : ℝ)*m - (windowCount w j m : ℝ)*l <
        (l : ℝ) + m := by exact_mod_cast hc
    have hl' : (0 : ℝ) < l := by exact_mod_cast hl
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    dsimp [lo,hi]
    apply (div_lt_div_iff₀ hl' hm').mpr
    nlinarith
  obtain ⟨α,hα⟩ := finite_strict_separation (windows w.length) lo hi hpair
  refine ⟨α, fun i l hl hi' => ?_⟩
  have hh := hα (i,l) ((mem_windows _ _ _).mpr ⟨hl,hi'⟩)
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  simpa [mul_comm] using And.intro ((div_lt_iff₀ hl').mp hh.1) ((lt_div_iff₀ hl').mp hh.2)

/-- Strict mechanical prefix representation, including the two endpoint prefixes. -/
def StrictFloor (w : List Bool) : Prop :=
  ∃ α ρ : ℝ, ∀ t : ℕ, t ≤ w.length →
    (prefixCount w t : ℝ) < t*α+ρ ∧ t*α+ρ < (prefixCount w t : ℝ)+1

/-- The requested finite-balanced to strict-floor bridge; no slope or sequence assumptions. -/
theorem finiteBalanced_strictFloor (w : List Bool) (hb : FiniteBalanced w) :
    StrictFloor w := by
  obtain ⟨α,hα⟩ := balanced_strict_slope w hb
  let lo : ℕ → ℝ := fun t => (prefixCount w t : ℝ) - t*α
  let hi : ℕ → ℝ := fun t => (prefixCount w t : ℝ) + 1 - t*α
  have hpair : ∀ i ∈ Finset.range (w.length+1),
      ∀ j ∈ Finset.range (w.length+1), lo i < hi j := by
    intro i hi' j hj'
    have hi0 : i ≤ w.length := by have hh := Finset.mem_range.mp hi'; omega
    have hj0 : j ≤ w.length := by have hh := Finset.mem_range.mp hj'; omega
    dsimp [lo,hi]
    rcases lt_trichotomy i j with hij | hij | hij
    · have hh := hα i (j-i) (by omega) (by omega)
      have he := prefixCount_add w i (j-i)
      rw [show i+(j-i) = j by omega] at he
      have he' : (prefixCount w j : ℝ) = (prefixCount w i : ℝ) + windowCount w i (j-i) := by
        exact_mod_cast he
      have hc : (j : ℝ) = (i : ℝ) + (j-i : ℕ) := by exact_mod_cast (Nat.add_sub_of_le (le_of_lt hij)).symm
      rw [he',hc]
      nlinarith [hh.2]
    · subst j; linarith
    · have hh := hα j (i-j) (by omega) (by omega)
      have he := prefixCount_add w j (i-j)
      rw [show j+(i-j) = i by omega] at he
      have he' : (prefixCount w i : ℝ) = (prefixCount w j : ℝ) + windowCount w j (i-j) := by
        exact_mod_cast he
      have hc : (i : ℝ) = (j : ℝ) + (i-j : ℕ) := by exact_mod_cast (Nat.add_sub_of_le (le_of_lt hij)).symm
      rw [he',hc]
      nlinarith [hh.1]
  obtain ⟨ρ,hρ⟩ := finite_strict_separation (Finset.range (w.length+1)) lo hi hpair
  refine ⟨α,ρ,fun t ht => ?_⟩
  have hh := hρ t (Finset.mem_range.mpr (by omega))
  dsimp [lo,hi] at hh
  constructor <;> linarith [hh.1, hh.2]

#print axioms balanced_cross_window
#print axioms balanced_strict_slope
#print axioms finiteBalanced_strictFloor
```

### `MarkoffRoot.lean`

```lean
import MarkoffStatement
import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

noncomputable section
open Polynomial
set_option linter.unusedSimpArgs false

def zeta : ℂ := (1 + (Real.sqrt 3 : ℂ) * Complex.I) / 2

@[simp] theorem zeta_re : zeta.re = 1/2 := by norm_num [zeta]
@[simp] theorem zeta_im : zeta.im = Real.sqrt 3 / 2 := by norm_num [zeta]

theorem zeta_sq : zeta^2 = zeta - 1 := by
  apply Complex.ext
  · norm_num [pow_two, Complex.mul_re]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  · norm_num [pow_two, Complex.mul_im]
    ring

theorem zeta_cube : zeta^3 = -1 := by
  calc
    zeta^3 = zeta * zeta^2 := by ring
    _ = -1 := by rw [zeta_sq]; linear_combination zeta_sq

theorem zeta_four : zeta^4 = -zeta := by
  rw [show 4 = 3+1 by decide, pow_succ, zeta_cube]
  ring

theorem zeta_ne_zero : zeta ≠ 0 := by
  intro h
  have hh := zeta_re
  rw [h] at hh
  norm_num at hh

theorem zeta_nonreal : zeta.im ≠ 0 := by
  rw [zeta_im]
  positivity

def ev : Polynomial ℤ →+* ℂ := eval₂RingHom (Int.castRingHom ℂ) zeta

def evM : Matrix (Fin 2) (Fin 2) (Polynomial ℤ) →+* Matrix (Fin 2) (Fin 2) ℂ :=
  ev.mapMatrix

def rootN : Matrix (Fin 2) (Fin 2) ℂ := !![zeta, 1-zeta; 1, -zeta]

theorem rootN_sq : rootN * rootN = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootN, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;> simp only [zeta_sq] <;> ring

theorem ev_mu0 : evM mu0 = zeta • (1 + rootN) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [evM, ev, mu0, rootN, Matrix.add_apply, Matrix.smul_apply] <;>
    ring_nf <;> simp only [zeta_sq] <;> ring

theorem ev_mu1 : evM mu1 = zeta^2 • (1 + (2-zeta) • rootN) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [evM, ev, mu1, rootN, Matrix.add_apply, Matrix.smul_apply] <;>
    ring_nf <;> simp only [zeta_four, zeta_cube, zeta_sq] <;> ring

/-- Product of two nilpotent root forms. -/
theorem root_forms_mul (a b : ℂ) :
    (1 + a • rootN) * (1 + b • rootN) = 1 + (a+b) • rootN := by
  rw [add_mul, mul_add, mul_add]
  simp [Matrix.smul_mul, Matrix.mul_smul, rootN_sq, add_smul, add_assoc, add_comm]

@[simp] theorem ones_cons (b : Bool) (w : List Bool) :
    ones (b :: w) = ones w + if b then 1 else 0 := by
  cases b <;> simp [ones]

/-- Published zeroth-order evaluation, re-derived for the literal source matrices. -/
theorem root_value_matrix (w : List Bool) :
    evM (muq w) = zeta^(w.length + ones w) •
      (1 + ((w.length : ℂ) + (1-zeta)*(ones w : ℂ)) • rootN) := by
  induction w with
  | nil => simp [ones]
  | cons b w ih =>
    rw [muq_cons, map_mul, ih]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, ev_mu0, List.length_cons, ones_cons]
      have hf := root_forms_mul 1 ((w.length : ℂ)+(1-zeta)*(ones w : ℂ))
      simp only [one_smul] at hf
      rw [Matrix.smul_mul, Matrix.mul_smul, hf, smul_smul]
      simp only [Nat.cast_add, Nat.cast_one, Nat.add_zero]
      have hp : zeta * zeta^(w.length + ones w) = zeta^(w.length + 1 + ones w) := by
        rw [show w.length+1+ones w = (w.length+ones w)+1 by omega, pow_succ]
        ring
      rw [hp]
      congr 2
      ring
    · simp only [↓reduceIte, ev_mu1, List.length_cons, ones_cons]
      rw [Matrix.smul_mul, Matrix.mul_smul, root_forms_mul, smul_smul]
      simp only [Nat.cast_add, Nat.cast_one]
      have hp : zeta^2 * zeta^(w.length + ones w) = zeta^(w.length + 1 + (ones w + 1)) := by
        rw [show w.length+1+(ones w+1) = (w.length+ones w)+2 by omega, pow_add]
        ring
      rw [hp]
      congr 2
      ring

theorem root_value (w : List Bool) :
    ev (muq w 0 1) = zeta^(w.length+ones w) *
      ((w.length : ℂ) - (w.length+ones w : ℕ)*zeta) := by
  have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) (root_value_matrix w)
  change ev (muq w 0 1) = zeta^(w.length+ones w) *
    (0 + ((w.length : ℂ)+(1-zeta)*(ones w : ℂ)) * (1-zeta)) at hh
  rw [hh]
  congr 1
  push_cast
  linear_combination (ones w : ℂ) * zeta_sq

#print axioms rootN_sq
#print axioms root_value_matrix
#print axioms root_value
```

### `MarkoffCounts.lean`

```lean
import MarkoffRoot
import Mathlib.Tactic.IntervalCases

noncomputable section
set_option linter.unusedSimpArgs false

theorem zeta_five : zeta^5 = 1-zeta := by
  rw [show 5 = 4+1 by decide, pow_succ, zeta_four]
  linear_combination -zeta_sq

theorem zeta_six : zeta^6 = 1 := by
  rw [show 6 = 3*2 by decide, pow_mul, zeta_cube]
  norm_num

theorem zeta_pow_mod (n : ℕ) : zeta^n = zeta^(n%6) := by
  conv_lhs => rw [← Nat.mod_add_div n 6]
  rw [pow_add, pow_mul, zeta_six]
  simp

theorem root_linear_independence (a b c d : ℤ)
    (h : (a : ℂ) + b*zeta = (c : ℂ) + d*zeta) : a=c ∧ b=d := by
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp only [Complex.add_im, Complex.intCast_im, Complex.mul_im, Complex.intCast_re,
    zero_mul, zero_add, add_zero] at him
  have hb : b=d := by
    have hb' : (b : ℝ) = d := (mul_right_cancel₀ zeta_nonreal him)
    exact_mod_cast hb'
  subst d
  simp only [Complex.add_re, Complex.intCast_re, Complex.mul_re, Complex.intCast_im,
    zero_mul, sub_zero] at hre
  exact ⟨by exact_mod_cast (show (a : ℝ) = c by linarith [hre]), rfl⟩

/-- Integer coordinates of the root value in the basis 1, ζ. -/
def phaseCoords (n k : ℤ) (r : ℕ) : ℤ × ℤ :=
  match r with
  | 0 => (n, -(n+k))
  | 1 => (n+k, -k)
  | 2 => (k, n)
  | 3 => (-n, n+k)
  | 4 => (-(n+k), k)
  | _ => (-k, -n)

theorem phase_formula (n k : ℤ) (r : ℕ) (hr : r < 6) :
    zeta^r * ((n : ℂ) - (n+k)*zeta) =
      ((phaseCoords n k r).1 : ℂ) + (phaseCoords n k r).2*zeta := by
  interval_cases r <;> norm_num [phaseCoords, zeta_five, zeta_four, zeta_cube, zeta_sq] <;>
    ring_nf <;> simp only [zeta_cube, zeta_sq] <;> ring

theorem phaseCoords_injective (n k m l : ℤ) (r s : ℕ)
    (hn : 0 ≤ n) (hk : 0 ≤ k) (hkn : k ≤ n)
    (hm : 0 ≤ m) (hl : 0 ≤ l) (hlm : l ≤ m)
    (hr : r < 6) (hs : s < 6)
    (h : phaseCoords n k r = phaseCoords m l s) : n=m ∧ k=l := by
  have ha := congrArg Prod.fst h
  have hb := congrArg Prod.snd h
  interval_cases r <;> interval_cases s <;> simp [phaseCoords] at ha hb <;> omega

/-- Count recovery directly from the sixth-root value, without a degree hypothesis. -/
theorem root_value_recovers_counts (u v : List Bool)
    (h : ev (muq u 0 1) = ev (muq v 0 1)) :
    u.length = v.length ∧ ones u = ones v := by
  rw [root_value, root_value, zeta_pow_mod (u.length+ones u),
    zeta_pow_mod (v.length+ones v)] at h
  have hu : ((u.length : ℂ) - (u.length+ones u : ℕ)*zeta) =
      ((u.length : ℤ) : ℂ) - ((u.length : ℤ)+(ones u : ℤ))*zeta := by push_cast; rfl
  have hv : ((v.length : ℂ) - (v.length+ones v : ℕ)*zeta) =
      ((v.length : ℤ) : ℂ) - ((v.length : ℤ)+(ones v : ℤ))*zeta := by push_cast; rfl
  rw [hu, hv, phase_formula _ _ _ (Nat.mod_lt _ (by decide)),
    phase_formula _ _ _ (Nat.mod_lt _ (by decide))] at h
  have hcoord := root_linear_independence _ _ _ _ h
  have heq : phaseCoords u.length (ones u) ((u.length+ones u)%6) =
      phaseCoords v.length (ones v) ((v.length+ones v)%6) := Prod.ext hcoord.1 hcoord.2
  have hku : ones u ≤ u.length := List.length_filter_le _ _
  have hkv : ones v ≤ v.length := List.length_filter_le _ _
  have hh := phaseCoords_injective u.length (ones u) v.length (ones v)
    _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) heq
  exact ⟨by omega, by omega⟩

theorem polynomial_recovers_counts (u v : List Bool) (h : muq u 0 1 = muq v 0 1) :
    u.length = v.length ∧ ones u = ones v :=
  root_value_recovers_counts u v (congrArg ev h)

#print axioms polynomial_recovers_counts
```

### `MarkoffEnergy.lean`

```lean
import BalancedFloor
import MarkoffFactors
import Mathlib.Algebra.Order.BigOperators.Group.Finset

noncomputable section
open scoped BigOperators
set_option linter.unusedSimpArgs false

/-- Prefix versions of the two statistics; including t=0,n changes only count constants. -/
def momentA (n : ℕ) (k : ℤ) (P : ℕ → ℤ) : ℤ :=
  ∑ t ∈ Finset.range (n+1), (k + (k-1)*P t - (P t)^2)

def momentB (n : ℕ) (P : ℕ → ℤ) : ℤ :=
  - ∑ t ∈ Finset.range (n+1), (2*(t : ℤ)-n)*P t

def prefixTotal (n : ℕ) (P : ℕ → ℤ) : ℤ := ∑ t ∈ Finset.range (n+1), P t

def energy (α ρ : ℝ) (n : ℕ) (P : ℕ → ℤ) : ℝ :=
  ∑ t ∈ Finset.range (n+1), ((P t : ℝ)^2 - (2*t*α + 2*ρ - 1)*P t)

def wordMomentA (w : List Bool) : ℤ := momentA w.length (ones w) (prefixCount w)
def wordMomentB (w : List Bool) : ℤ := momentB w.length (prefixCount w)

/-- The strict strip makes p the unique integer minimizer of the coordinate energy. -/
theorem quadratic_strict_min (p q : ℤ) (x : ℝ)
    (h0 : (p : ℝ) < x) (h1 : x < (p : ℝ)+1) (hpq : p ≠ q) :
    (p : ℝ)^2 - (2*x-1)*p < (q : ℝ)^2 - (2*x-1)*q := by
  rcases lt_or_gt_of_ne hpq with hlt | hgt
  · have hh : (p : ℝ)+1 ≤ q := by exact_mod_cast (show p+1 ≤ q by omega)
    have ha : (0 : ℝ) < (q : ℝ)-p := by linarith
    have hb : (0 : ℝ) < (q : ℝ)+p-2*x+1 := by linarith
    nlinarith [mul_pos ha hb]
  · have hh : (q : ℝ)+1 ≤ p := by exact_mod_cast (show q+1 ≤ p by omega)
    have ha : (q : ℝ)-p < (0 : ℝ) := by linarith
    have hb : (q : ℝ)+p-2*x+1 < (0 : ℝ) := by linarith
    nlinarith [mul_pos_of_neg_of_neg ha hb]

theorem energy_strict_min (n : ℕ) (P Q : ℕ → ℤ) (α ρ : ℝ)
    (hP : ∀ t ≤ n, (P t : ℝ) < t*α+ρ ∧ t*α+ρ < (P t : ℝ)+1)
    (hne : ∃ t ≤ n, P t ≠ Q t) : energy α ρ n P < energy α ρ n Q := by
  unfold energy
  apply Finset.sum_lt_sum
  · intro t ht
    have ht' : t ≤ n := by have := Finset.mem_range.mp ht; omega
    by_cases heq : P t = Q t
    · rw [heq]
    · have hh := quadratic_strict_min (P t) (Q t) (t*α+ρ)
        (hP t ht').1 (hP t ht').2 heq
      convert le_of_lt hh using 1 <;> ring
  · obtain ⟨t,ht,hne⟩ := hne
    refine ⟨t,Finset.mem_range.mpr (by omega),?_⟩
    have hh := quadratic_strict_min (P t) (Q t) (t*α+ρ)
      (hP t ht).1 (hP t ht).2 hne
    convert hh using 1 <;> ring

/-- Algebraic energy difference. No balance or mechanicality is assumed here. -/
theorem energy_difference (n : ℕ) (k : ℤ) (P Q : ℕ → ℤ) (α ρ : ℝ) :
    energy α ρ n P - energy α ρ n Q =
      -((momentA n k P - momentA n k Q : ℤ) : ℝ) +
      α*((momentB n P - momentB n Q : ℤ) : ℝ) -
      ((n : ℝ)*α+2*ρ-k)*((prefixTotal n P - prefixTotal n Q : ℤ) : ℝ) := by
  unfold energy momentA momentB prefixTotal
  simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
    Int.cast_one, Int.cast_ofNat, Int.cast_neg, Int.cast_sum,
    Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- Two strict mechanical integer paths are determined by n,k and the two moments. -/
theorem strictFloor_moments_unique (n : ℕ) (k : ℤ) (P Q : ℕ → ℤ)
    (hP0 : P 0 = 0) (hQ0 : Q 0 = 0) (hPn : P n = k) (hQn : Q n = k)
    (hP : ∃ α ρ : ℝ, ∀ t ≤ n, (P t : ℝ) < t*α+ρ ∧ t*α+ρ < (P t : ℝ)+1)
    (hQ : ∃ α ρ : ℝ, ∀ t ≤ n, (Q t : ℝ) < t*α+ρ ∧ t*α+ρ < (Q t : ℝ)+1)
    (hA : momentA n k P = momentA n k Q) (hB : momentB n P = momentB n Q) :
    ∀ t ≤ n, P t = Q t := by
  by_contra hne
  push Not at hne
  obtain ⟨α,ρ,hα⟩ := hP
  obtain ⟨β,σ,hβ⟩ := hQ
  have heP := energy_strict_min n P Q α ρ hα hne
  have heQ := energy_strict_min n Q P β σ hβ (by
    obtain ⟨t,ht,hne⟩ := hne
    exact ⟨t,ht,Ne.symm hne⟩)
  have hp : (0 : ℝ) < n*α+2*ρ-k := by
    have h0 := (hα 0 (by omega)).1
    have hn := (hα n (by omega)).1
    rw [hP0] at h0
    rw [hPn] at hn
    norm_num at h0
    linarith
  have hq : (0 : ℝ) < n*β+2*σ-k := by
    have h0 := (hβ 0 (by omega)).1
    have hn := (hβ n (by omega)).1
    rw [hQ0] at h0
    rw [hQn] at hn
    norm_num at h0
    linarith
  have hiP := energy_difference n k P Q α ρ
  have hiQ := energy_difference n k Q P β σ
  rw [hA,hB] at hiP hiQ
  simp only [sub_self, Int.cast_zero, neg_zero, mul_zero, zero_add, zero_sub] at hiP hiQ
  have hsP : (0 : ℝ) < ((prefixTotal n P - prefixTotal n Q : ℤ) : ℝ) := by
    by_contra hh
    have hh' : ((prefixTotal n P - prefixTotal n Q : ℤ) : ℝ) ≤ 0 := by linarith
    have hh'' := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hp) hh'
    linarith
  have hsQ : (0 : ℝ) < ((prefixTotal n Q - prefixTotal n P : ℤ) : ℝ) := by
    by_contra hh
    have hh' : ((prefixTotal n Q - prefixTotal n P : ℤ) : ℝ) ≤ 0 := by linarith
    have hh'' := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hq) hh'
    linarith
  push_cast at hsP hsQ
  linarith

theorem prefixCount_determines_word (u v : List Bool) (hn : u.length = v.length)
    (hP : ∀ t ≤ u.length, prefixCount u t = prefixCount v t) : u=v := by
  apply List.ext_getElem hn
  intro i hi hj
  have ht := hP i (by omega)
  have hs := hP (i+1) (by omega)
  unfold prefixCount at ht hs
  rw [ones_take_succ u i hi, ones_take_succ v i hj] at hs
  cases hu : u[i] <;> cases hv : v[i] <;> simp [hu,hv] at * <;> omega

/-- The combinatorial reconstruction step for the literal finite balance predicate. -/
theorem finiteBalanced_moments_injective (u v : List Bool)
    (hu : FiniteBalanced u) (hv : FiniteBalanced v)
    (hn : u.length = v.length) (hk : ones u = ones v)
    (hA : wordMomentA u = wordMomentA v) (hB : wordMomentB u = wordMomentB v) : u=v := by
  apply prefixCount_determines_word u v hn
  apply strictFloor_moments_unique u.length (ones u) (prefixCount u) (prefixCount v)
  · exact prefixCount_zero u
  · exact prefixCount_zero v
  · exact prefixCount_length u
  · simp [hn,hk]
  · exact finiteBalanced_strictFloor u hu
  · simpa [StrictFloor,hn] using finiteBalanced_strictFloor v hv
  · simpa [wordMomentA,hn,hk] using hA
  · simpa [wordMomentB,hn] using hB

#print axioms energy_difference
#print axioms strictFloor_moments_unique
#print axioms finiteBalanced_moments_injective
```

### `MarkoffJetLocal.lean`

```lean
import MarkoffRoot
import Mathlib.Tactic.NoncommRing

noncomputable section
open Polynomial
set_option linter.unusedSimpArgs false

def evD (M : Matrix (Fin 2) (Fin 2) (Polynomial ℤ)) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => ev ((M i j).derivative)

theorem evD_add (M N : Matrix (Fin 2) (Fin 2) (Polynomial ℤ)) :
    evD (M+N) = evD M + evD N := by
  ext i j
  simp [evD, Polynomial.derivative_add]

theorem evD_sub (M N : Matrix (Fin 2) (Fin 2) (Polynomial ℤ)) :
    evD (M-N) = evD M - evD N := by
  ext i j
  simp [evD, Polynomial.derivative_sub]

theorem evD_mul (M N : Matrix (Fin 2) (Fin 2) (Polynomial ℤ)) :
    evD (M*N) = evD M * evM N + evM M * evD N := by
  ext i j
  simp [evD, evM, Matrix.mul_apply, Fin.sum_univ_two,
    Polynomial.derivative_add, Polynomial.derivative_mul]
  ring

/-- Exact polynomial commutator of the two source generators. -/
theorem generator_commutator :
    mu1*mu0-mu0*mu1 = (X+X^4 : Polynomial ℤ) • (!![0,1;-X,0] : Matrix (Fin 2) (Fin 2) (Polynomial ℤ)) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [mu0,mu1,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

def jetK : Matrix (Fin 2) (Fin 2) ℂ := 3 • !![0,1;-zeta,0]

theorem ev_commutator : evM (mu1*mu0-mu0*mu1) = 0 := by
  rw [generator_commutator]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [evM,ev,zeta_four]

theorem evD_commutator : evD (mu1*mu0-mu0*mu1) = -jetK := by
  rw [generator_commutator]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [evD,ev,jetK,Polynomial.derivative_mul,Polynomial.derivative_add,
      Polynomial.derivative_X_pow] <;>
    ring_nf <;> simp only [zeta_four,zeta_cube,zeta_sq] <;> ring

theorem jet_anticommutes : jetK*rootN = -(rootN*jetK) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jetK,rootN,Matrix.mul_apply,Fin.sum_univ_two] <;>
    ring_nf <;> simp only [zeta_cube,zeta_sq] <;> ring

theorem jet_sandwich_zero : rootN*jetK*rootN = 0 := by
  rw [mul_assoc,jet_anticommutes,mul_neg,← mul_assoc,rootN_sq,zero_mul,neg_zero]

/-- A formal first-order comparison valid for arbitrary prefixes and suffixes. -/
theorem adjacent_swap_jet_matrix (x y : List Bool) :
    evD (muq (x ++ [true,false] ++ y)) - evD (muq (x ++ [false,true] ++ y)) =
      evM (muq x) * (-jetK) * evM (muq y) := by
  have hp : muq (x ++ [true,false] ++ y) - muq (x ++ [false,true] ++ y) =
      muq x * (mu1*mu0-mu0*mu1) * muq y := by
    simp only [muq_append, muq_cons, muq_nil, ↓reduceIte, mul_one]
    noncomm_ring
  have hd := congrArg evD hp
  rw [evD_sub] at hd
  simpa [evD_mul,ev_commutator,evD_commutator,map_mul] using hd

/-- The root sandwich collapses to a linear expression. -/
theorem jet_root_sandwich (a b : ℂ) :
    ((1+a • rootN)*jetK*(1+b • rootN)) 0 1 = 3*(1+zeta*(a-b)) := by
  simp [add_mul,mul_add,Matrix.smul_mul,Matrix.mul_smul,jet_sandwich_zero,
    jet_anticommutes,Matrix.add_apply,Matrix.sub_apply,Matrix.mul_apply,
    Fin.sum_univ_two,rootN,jetK]
  ring_nf
  simp only [zeta_cube,zeta_sq]
  ring

#print axioms generator_commutator
#print axioms evD_commutator
#print axioms adjacent_swap_jet_matrix
#print axioms jet_root_sandwich
```

### `MarkoffSwapMoments.lean`

```lean
import MarkoffEnergy
import MarkoffRoot

noncomputable section
open scoped BigOperators
set_option linter.unusedSimpArgs false

@[simp] theorem ones_append' (u v : List Bool) : ones (u++v) = ones u+ones v := ones_append u v

theorem prefixCount_append (u v : List Bool) (t : ℕ) :
    prefixCount (u++v) t = prefixCount u t + prefixCount v (t-u.length) := by
  simp [prefixCount, List.take_append]

/-- Only one prefix count changes in an adjacent unequal-letter interchange. -/
theorem prefixCount_swap (x y : List Bool) (t : ℕ) :
    prefixCount (x ++ [true,false] ++ y) t =
      prefixCount (x ++ [false,true] ++ y) t + if t=x.length+1 then 1 else 0 := by
  simp only [List.append_assoc, prefixCount_append]
  by_cases ht : t ≤ x.length
  · have hh : t-x.length=0 := by omega
    simp [hh, show t ≠ x.length+1 by omega]
  · by_cases he : t=x.length+1
    · simp [he,prefixCount,ones]
    · have hh : 2 ≤ t-x.length := by omega
      obtain ⟨r,hr⟩ : ∃ r, t-x.length=r+2 := ⟨t-x.length-2,by omega⟩
      simp [prefixCount, hr, List.take_succ_cons, ones, he]

theorem prefixCount_swap_at (x y : List Bool) :
    prefixCount (x ++ [false,true] ++ y) (x.length+1) = ones x := by
  rw [List.append_assoc,prefixCount_append]
  simp [prefixCount,ones,List.take_of_length_le]

theorem wordMomentA_swap (x y : List Bool) :
    wordMomentA (x ++ [true,false] ++ y) - wordMomentA (x ++ [false,true] ++ y) =
      (ones (x ++ [true,false] ++ y) : ℤ) - 2*(ones x : ℤ)-2 := by
  let u := x ++ [true,false] ++ y
  let v := x ++ [false,true] ++ y
  have hn : u.length=v.length := by simp [u,v]
  have hk : ones u=ones v := by simp [u,v,ones_cons]
  change momentA u.length (ones u) (prefixCount u) - momentA v.length (ones v) (prefixCount v) = _
  rw [← hn,← hk]
  unfold momentA
  rw [← Finset.sum_sub_distrib]
  have hpoint : ∀ t : ℕ, ((ones u : ℤ)+((ones u : ℤ)-1)*prefixCount u t-(prefixCount u t)^2) -
      ((ones u : ℤ)+((ones u : ℤ)-1)*prefixCount v t-(prefixCount v t)^2) =
      if t=x.length+1 then (ones u : ℤ)-2*(ones x : ℤ)-2 else 0 := by
    intro t
    have hp := prefixCount_swap x y t
    change prefixCount u t = prefixCount v t + _ at hp
    rw [hp]
    split_ifs with ht
    · subst t
      have hq : prefixCount v (x.length+1) = ones x := prefixCount_swap_at x y
      rw [hq]
      ring
    · ring
  simp_rw [hpoint]
  have hmem : x.length+1 ∈ Finset.range (u.length+1) := by simp [u]
  simp only [Finset.sum_ite_eq', ite_eq_left hmem]
  rfl

theorem wordMomentB_swap (x y : List Bool) :
    wordMomentB (x ++ [true,false] ++ y) - wordMomentB (x ++ [false,true] ++ y) =
      ((x ++ [true,false] ++ y).length : ℤ) - 2*(x.length : ℤ)-2 := by
  let u := x ++ [true,false] ++ y
  let v := x ++ [false,true] ++ y
  have hn : u.length=v.length := by simp [u,v]
  change momentB u.length (prefixCount u) - momentB v.length (prefixCount v) = _
  rw [← hn]
  unfold momentB
  rw [show (-∑ t ∈ Finset.range (u.length+1), (2*(t : ℤ)-u.length)*prefixCount u t) -
      (-∑ t ∈ Finset.range (u.length+1), (2*(t : ℤ)-u.length)*prefixCount v t) =
      ∑ t ∈ Finset.range (u.length+1),
        -((2*(t : ℤ)-u.length)*(prefixCount u t-prefixCount v t)) by
    simp [mul_sub,Finset.sum_sub_distrib]; ring]
  have hpoint : ∀ t : ℕ, -((2*(t : ℤ)-u.length)*(prefixCount u t-prefixCount v t)) =
      if t=x.length+1 then (u.length : ℤ)-2*(x.length : ℤ)-2 else 0 := by
    intro t
    have hp := prefixCount_swap x y t
    change prefixCount u t = prefixCount v t + _ at hp
    rw [hp]
    split_ifs with ht
    · subst t; push_cast; ring
    · ring
  simp_rw [hpoint]
  have hmem : x.length+1 ∈ Finset.range (u.length+1) := by simp [u]
  simp only [Finset.sum_ite_eq', ite_eq_left hmem]
  rfl

#print axioms prefixCount_swap
#print axioms wordMomentA_swap
#print axioms wordMomentB_swap
```

### `MarkoffJetSwap.lean`

```lean
import MarkoffJetLocal
import MarkoffSwapMoments

noncomputable section
open Polynomial
set_option linter.unusedSimpArgs false

/-- Scalar form of the local derivative comparison in the source conventions. -/
theorem adjacent_swap_jet (x y : List Bool) :
    ev ((muq (x ++ [true,false] ++ y) 0 1).derivative) -
      ev ((muq (x ++ [false,true] ++ y) 0 1).derivative) =
    3*zeta^((x ++ [true,false] ++ y).length + ones (x ++ [true,false] ++ y)) *
      ((2*(ones x : ℂ)+2-ones (x ++ [true,false] ++ y)) +
        zeta*(2*(x.length : ℂ)+2-(x ++ [true,false] ++ y).length)) := by
  have hm := adjacent_swap_jet_matrix x y
  rw [root_value_matrix,root_value_matrix] at hm
  have hs := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hm
  simp only [Matrix.sub_apply,evD] at hs
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul,mul_neg,neg_mul,
    Matrix.neg_apply,Matrix.smul_apply,smul_eq_mul,jet_root_sandwich] at hs
  rw [hs]
  have hw : (x ++ [true,false] ++ y).length + ones (x ++ [true,false] ++ y) =
      (x.length+ones x)+(y.length+ones y)+3 := by
    simp [ones_cons]
    omega
  rw [hw]
  simp only [pow_add,zeta_cube]
  simp only [List.length_append,List.length_cons,List.length_nil,ones_append',ones_cons,show ones [] = 0 from rfl]
  push_cast
  ring_nf
  simp only [zeta_sq]
  ring

/-- Unnormalized first-jet invariant; its power factor depends only on counts. -/
def jetInvariant (w : List Bool) : ℂ :=
  ev ((muq w 0 1).derivative) +
    3*zeta^(w.length+ones w)*((wordMomentA w : ℂ)+zeta*(wordMomentB w : ℂ))

theorem jetInvariant_swap (x y : List Bool) :
    jetInvariant (x ++ [true,false] ++ y) = jetInvariant (x ++ [false,true] ++ y) := by
  let u := x ++ [true,false] ++ y
  let v := x ++ [false,true] ++ y
  have hn : u.length=v.length := by simp [u,v]
  have hk : ones u=ones v := by simp [u,v,ones_cons]
  have hD := adjacent_swap_jet x y
  have hA := wordMomentA_swap x y
  have hB := wordMomentB_swap x y
  change ev ((muq u 0 1).derivative)-ev ((muq v 0 1).derivative) = _ at hD
  change wordMomentA u-wordMomentA v = _ at hA
  change wordMomentB u-wordMomentB v = _ at hB
  have hA' : (wordMomentA u : ℂ)-(wordMomentA v : ℂ) =
      (ones u : ℂ)-2*(ones x : ℂ)-2 := by exact_mod_cast hA
  have hB' : (wordMomentB u : ℂ)-(wordMomentB v : ℂ) =
      (u.length : ℂ)-2*(x.length : ℂ)-2 := by exact_mod_cast hB
  change jetInvariant u = jetInvariant v
  unfold jetInvariant
  rw [←hn,←hk]
  linear_combination hD + (3*zeta^(u.length+ones u))*hA' +
    (3*zeta^(u.length+ones u)*zeta)*hB'

#print axioms adjacent_swap_jet
#print axioms jetInvariant_swap
```

### `MarkoffConjecture.lean`

```lean
import MarkoffJetSwap
import MarkoffCounts
import MarkoffChecks
import Mathlib.Data.List.Perm.Basic

noncomputable section
set_option linter.unusedSimpArgs false

/-- Permutations are generated by adjacent interchanges in arbitrary contexts. -/
theorem invariant_of_adjacent {α β : Type*} (F : List α → β)
    (hs : ∀ (x : List α) (a b : α) (y : List α),
      F (x ++ [a,b] ++ y) = F (x ++ [b,a] ++ y))
    {u v : List α} (h : u.Perm v) : F u = F v := by
  have main : ∀ x : List α, F (x++u) = F (x++v) := by
    induction h with
    | nil => intro x; rfl
    | cons a h ih =>
      intro x
      simpa [List.append_assoc] using ih (x++[a])
    | swap a b y =>
      intro x
      simpa [List.append_assoc] using hs x b a y
    | trans h₁ h₂ ih₁ ih₂ =>
      intro x
      exact (ih₁ x).trans (ih₂ x)
  simpa using main []

theorem jetInvariant_perm {u v : List Bool} (h : u.Perm v) :
    jetInvariant u = jetInvariant v := by
  apply invariant_of_adjacent jetInvariant ?_ h
  intro x a b y
  cases a <;> cases b
  · rfl
  · exact (jetInvariant_swap x y).symm
  · exact jetInvariant_swap x y
  · rfl

theorem ones_eq_count_true (w : List Bool) : ones w = w.count true := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [ones_cons,ih]

theorem count_false_add_ones (w : List Bool) : w.count false + ones w = w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [ones_cons] <;> omega

theorem same_counts_perm {u v : List Bool}
    (hn : u.length=v.length) (hk : ones u=ones v) : u.Perm v := by
  apply List.perm_iff_count.mpr
  intro b
  cases b
  · have hu := count_false_add_ones u
    have hv := count_false_add_ones v
    omega
  · simpa [ones_eq_count_true] using hk

/-- Global first-jet recovery of the two moments, over all binary words. -/
theorem polynomial_recovers_moments (u v : List Bool) (h : muq u 0 1 = muq v 0 1) :
    wordMomentA u=wordMomentA v ∧ wordMomentB u=wordMomentB v := by
  obtain ⟨hn,hk⟩ := polynomial_recovers_counts u v h
  have hi := jetInvariant_perm (same_counts_perm hn hk)
  unfold jetInvariant at hi
  rw [hn,hk,h] at hi
  have hsum := mul_left_cancel₀
    (mul_ne_zero (by norm_num : (3 : ℂ) ≠ 0) (pow_ne_zero _ zeta_ne_zero))
    (add_left_cancel hi)
  apply root_linear_independence
  simpa [mul_comm] using hsum

theorem qMarkoff_injective_on_finite_balanced :
    Set.InjOn (fun w => muq w 0 1) {w | FiniteBalanced w} := by
  intro u hu v hv h
  obtain ⟨hn,hk⟩ := polynomial_recovers_counts u v h
  obtain ⟨hA,hB⟩ := polynomial_recovers_moments u v h
  exact finiteBalanced_moments_injective u v hu hv hn hk hA hB

/-- Conjecture 1.3 with precisely the endpoint required by the source review. -/
theorem labbe_lapointe_conj_1_3 : Set.InjOn (fun w => muq w 0 1) LB := by
  intro u hu v hv h
  exact qMarkoff_injective_on_finite_balanced (LB_finiteBalanced hu) (LB_finiteBalanced hv) h

#check labbe_lapointe_conj_1_3
#print labbe_lapointe_conj_1_3
#print axioms polynomial_recovers_moments
#print axioms qMarkoff_injective_on_finite_balanced
#print axioms labbe_lapointe_conj_1_3
#eval Lean.versionString
```

### `MarkoffAudit.lean`

```lean
import MarkoffConjecture

#print mu0
#print mu1
#print muq
#print onesIn
#print BalancedSeq
#print IsFactor
#print LB
#print FiniteBalanced
#print StrictFloor
#print labbe_lapointe_conj_1_3
#print axioms labbe_lapointe_conj_1_3
#print axioms qMarkoff_injective_on_finite_balanced
#print axioms finiteBalanced_strictFloor
#print axioms polynomial_recovers_counts
#print axioms polynomial_recovers_moments
#print axioms finiteBalanced_moments_injective
#print axioms witness_u_mem
#print axioms witness_v_mem
#print axioms witnesses_distinct
#print axioms witnesses_equal_counts
#print axioms witnesses_no_common_sequence
#print axioms source_example_00101
#print axioms noninjective_pair
#print axioms unbalanced_00011_not_mem
```

