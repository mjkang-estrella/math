# Lean source appendix

Modules are listed in import order.

## IKGraph.lean

```lean
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.CardEmbedding

open scoped BigOperators

/-- A row degree in the Boolean incidence matrix of a finite simple bipartite graph. -/
def IKDeg {ell M : ℕ} (a : Fin ell → Fin M → Bool) (x : Fin ell) : ℕ :=
  (Finset.univ.filter fun y => a x y = true).card

def IKNoIsolates {ell M : ℕ} (a : Fin ell → Fin M → Bool) : Prop :=
  (∀ x, ∃ y, a x y = true) ∧ (∀ y, ∃ x, a x y = true)

/-- A matching of size ell saturates the ell rows, hence is an injective choice of neighbours. -/
def IKMatchings {ell M : ℕ} (a : Fin ell → Fin M → Bool) :=
  {f : Fin ell → Fin M // Function.Injective f ∧ ∀ x, a x (f x) = true}

noncomputable def IKCount {ell M : ℕ} (a : Fin ell → Fin M → Bool) : ℕ :=
  Nat.card (IKMatchings a)

noncomputable def IKPsi (d : ℕ) (t : ℝ) : ℝ :=
  (Real.log (d.factorial : ℝ) - Real.log (Real.Gamma ((d : ℝ) - t + 1))) / t

noncomputable def IKRhs {ell M : ℕ} (a : Fin ell → Fin M → Bool) : ℝ :=
  ∑ x, IKPsi (IKDeg a x) ((ell : ℝ) * (IKDeg a x : ℝ) / (M : ℝ))

/-- Base-two logarithm, written explicitly using the natural logarithm. -/
noncomputable def IKLog₂ (z : ℝ) : ℝ := Real.log z / Real.log 2

noncomputable def IKPsi₂ (d : ℕ) (t : ℝ) : ℝ :=
  t⁻¹ * (IKLog₂ (d.factorial : ℝ) - IKLog₂ (Real.Gamma ((d : ℝ) - t + 1)))

/-- Equation (20). The zero-count case is vacuous with extended-real log zero.
The empty graph has an empty sum. -/
def IKConjecture : Prop :=
  ∀ (ell M : ℕ) (a : Fin ell → Fin M → Bool),
    ell ≤ M → IKNoIsolates a → 0 < IKCount a →
    IKLog₂ (IKCount a : ℝ) ≤
      ∑ x, IKPsi₂ (IKDeg a x) ((ell : ℝ) * (IKDeg a x : ℝ) / (M : ℝ))

def IKRefutation : Prop :=
  ∃ (ell M : ℕ) (a : Fin ell → Fin M → Bool),
    0 < ell ∧ ell ≤ M ∧ IKNoIsolates a ∧ 0 < IKCount a ∧
      IKRhs a < Real.log (IKCount a : ℝ)

theorem ik_rhs_base_two {ell M : ℕ} (a : Fin ell → Fin M → Bool) :
    (∑ x, IKPsi₂ (IKDeg a x) ((ell : ℝ) * (IKDeg a x : ℝ) / (M : ℝ))) =
      IKRhs a / Real.log 2 := by
  rw [IKRhs, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  simp only [IKPsi₂, IKLog₂, IKPsi]
  ring

/-- The zero row and zero column form the single-edge component. -/
def IKFamily (m : ℕ) (x : Fin (m + 1)) (y : Fin (m + 2)) : Bool :=
  decide ((x = 0) ↔ (y = 0))

@[simp] theorem ik_family_edge {m : ℕ} {x : Fin (m + 1)} {y : Fin (m + 2)} :
    IKFamily m x y = true ↔ (x = 0 ↔ y = 0) := by simp [IKFamily]

theorem ik_family_no_isolates {m : ℕ} (hm : 0 < m) : IKNoIsolates (IKFamily m) := by
  constructor
  · intro x
    by_cases hx : x = 0
    · exact ⟨0, by simp [hx]⟩
    · exact ⟨(0 : Fin (m + 1)).succ, by simp [hx]⟩
  · intro y
    by_cases hy : y = 0
    · exact ⟨0, by simp [hy]⟩
    · have i : Fin m := ⟨0, hm⟩
      exact ⟨i.succ, by simp [hy]⟩

/-- Restrict to nonzero rows and columns, with inverse adjoining the forced edge. -/
def ik_matching_equiv (m : ℕ) : IKMatchings (IKFamily m) ≃ (Fin m ↪ Fin (m + 1)) := by
  have row (f : IKMatchings (IKFamily m)) (i : Fin m) : f.val i.succ ≠ 0 :=
    fun h => Fin.succ_ne_zero i ((ik_family_edge.mp (f.prop.2 i.succ)).mpr h)
  refine
    { toFun := fun f => ⟨fun i => (f.val i.succ).pred (row f i), ?_⟩
      invFun := fun g => ⟨Fin.cases 0 (fun i => (g i).succ), ?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro i j h
    apply Fin.succ_injective _ (f.prop.1 ?_)
    simpa using congrArg Fin.succ h
  · intro i j
    refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
      simp [g.injective.eq_iff]
    exact fun h => (Fin.succ_ne_zero _ h.symm).elim
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  · intro f
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using (ik_family_edge.mp (f.prop.2 0)).mp rfl |>.symm
    · exact Fin.succ_pred _ (row f j)
  · intro g
    ext i
    simp

theorem ik_family_count (m : ℕ) : IKCount (IKFamily m) = (m + 1).factorial := by
  classical
  unfold IKCount
  rw [Nat.card_congr (ik_matching_equiv m), Nat.card_eq_fintype_card,
    Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin,
    Nat.descFactorial_eq_div (by omega), show m + 1 - m = 1 by omega]
  simp

@[simp] theorem ik_family_deg_zero (m : ℕ) : IKDeg (IKFamily m) 0 = 1 := by
  simp [IKDeg, Finset.filter_eq']

@[simp] theorem ik_family_deg_succ {m : ℕ} (i : Fin m) :
    IKDeg (IKFamily m) i.succ = m + 1 := by
  have h : (Finset.univ.filter fun y : Fin (m + 2) => IKFamily m i.succ y = true) =
      Finset.univ.erase 0 := by
    ext y
    simp
  rw [IKDeg, h, Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp

theorem ik_family_rhs (m : ℕ) :
    IKRhs (IKFamily m) =
      (m : ℝ) * IKPsi (m + 1) ((m + 1 : ℝ)^2 / (m + 2)) +
        IKPsi 1 ((m + 1 : ℝ) / (m + 2)) := by
  rw [IKRhs, Fin.sum_univ_succ]
  simp [pow_two, add_comm]
```

## IKAnalysis.lean

```lean
import IKGraph
import Mathlib.NumberTheory.Harmonic.GammaDeriv

open Real Set

/-- The natural-log gap multiplied by the square of the larger row degree. -/
theorem ik_scaled_gap (m : ℕ) :
    ((m : ℝ) + 1)^2 * (log (IKCount (IKFamily m) : ℝ) - IKRhs (IKFamily m)) =
      log ((m + 1).factorial : ℝ) +
      (m : ℝ) * (m + 2) * log (Gamma (2 - 1 / (m + 2))) +
      (m + 1 : ℝ) * (m + 2) * log (Gamma (1 + 1 / (m + 2))) := by
  have h₁ : (m : ℝ) + 1 ≠ 0 := by positivity
  have h₂ : (m : ℝ) + 2 ≠ 0 := by positivity
  rw [ik_family_count, ik_family_rhs]
  simp only [IKPsi, Nat.cast_add, Nat.cast_one, Nat.factorial_one, log_one, zero_sub]
  rw [show (m : ℝ) + 1 - (m + 1)^2 / (m + 2) + 1 = 2 - 1 / (m + 2) by
    field_simp; ring,
    show (1 : ℝ) - (m + 1) / (m + 2) + 1 = 1 + 1 / (m + 2) by
      field_simp; ring]
  field_simp; ring

local notation "γ" => Real.eulerMascheroniConstant

theorem ik_gamma_tangents {e : ℝ} (he : 0 < e) (he' : e < 1) :
    -(1 - γ) * e ≤ log (Gamma (2 - e)) ∧ -γ * e ≤ log (Gamma (1 + e)) := by
  have h₁ : HasDerivAt (log ∘ Gamma) (-γ) 1 := by
    simpa [Function.comp_def, Gamma_one] using hasDerivAt_Gamma_one.log (by simp [Gamma_one])
  have hg₂ : HasDerivAt Gamma (1 - γ) 2 := by
    have h := hasDerivAt_Gamma_nat 1
    norm_num [harmonic] at h
    simpa [sub_eq_add_neg, add_comm] using h
  have h₂ : HasDerivAt (log ∘ Gamma) (1 - γ) 2 := by
    simpa [Function.comp_def, Gamma_two] using hg₂.log (by simp)
  constructor
  · have h := convexOn_log_Gamma.slope_le_of_hasDerivAt
      (show 2 - e ∈ Ioi (0 : ℝ) from by simp; linarith)
      (show 2 ∈ Ioi (0 : ℝ) from by norm_num)
      (show 2 - e < 2 by linarith) h₂
    rw [slope_def_field, show 2 - (2 - e) = e by ring, div_le_iff₀ he] at h
    simp only [Function.comp_apply, Gamma_two, log_one, zero_sub] at h
    linarith
  · have h := convexOn_log_Gamma.le_slope_of_hasDerivAt
      (show 1 ∈ Ioi (0 : ℝ) from by norm_num)
      (show 1 + e ∈ Ioi (0 : ℝ) from by simp; linarith)
      (show 1 < 1 + e by linarith) h₁
    rw [slope_def_field, add_sub_cancel_left, le_div_iff₀ he] at h
    simpa [Gamma_one] using h

theorem ik_log_factorial_bound {m : ℕ} (hm : 4 ≤ m) :
    (m : ℝ) + 2 / 3 < log ((m + 1).factorial : ℝ) := by
  induction m, hm using Nat.le_induction with
  | base =>
      have he : exp 1 < (11 : ℝ) / 4 := exp_one_lt_d9.trans (by norm_num)
      have hp := pow_lt_pow_left₀ he (exp_pos 1).le (show 14 ≠ 0 by decide)
      have hc : ((11 : ℝ) / 4)^14 < (120 : ℝ)^3 := by norm_num
      have hl := strictMonoOn_log (Set.mem_Ioi.mpr (by positivity))
        (Set.mem_Ioi.mpr (by positivity)) (hp.trans hc)
      simp only [log_pow, log_exp] at hl
      norm_num [Nat.factorial] at *
      linarith
  | succ n hn ih =>
      have h₆ : (6 : ℝ) ≤ (n : ℝ) + 2 := by exact_mod_cast (show 6 ≤ n + 2 by omega)
      have h := strictMonoOn_log (Set.mem_Ioi.mpr (exp_pos 1))
        (Set.mem_Ioi.mpr (show 0 < (n : ℝ) + 2 by positivity))
        (exp_one_lt_three.trans_le (by linarith : (3 : ℝ) ≤ (n : ℝ) + 2))
      rw [log_exp] at h
      rw [Nat.factorial_succ, Nat.cast_mul, log_mul (by positivity) (by positivity)]
      push_cast
      rw [show (n : ℝ) + 1 + 1 = n + 2 by ring]
      linarith

theorem ik_family_violation_ge_four {m : ℕ} (hm : 4 ≤ m) :
    IKRhs (IKFamily m) < log (IKCount (IKFamily m) : ℝ) := by
  let e : ℝ := 1 / ((m : ℝ) + 2)
  have hm₀ : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have he : 0 < e := by dsimp [e]; positivity
  have he' : e < 1 := by dsimp [e]; rw [div_lt_one (by positivity)]; linarith
  obtain ⟨h₂, h₁⟩ := ik_gamma_tangents he he'
  have ha : (m : ℝ) * (m + 2) * (-(1 - γ) * e) = -(m : ℝ) * (1 - γ) := by
    dsimp [e]
    field_simp
  have hb : ((m : ℝ) + 1) * (m + 2) * (-γ * e) = -((m : ℝ) + 1) * γ := by
    dsimp [e]
    field_simp
  have h₂' := mul_le_mul_of_nonneg_left h₂ (show 0 ≤ (m : ℝ) * (m + 2) by positivity)
  have h₁' := mul_le_mul_of_nonneg_left h₁ (show 0 ≤ ((m : ℝ) + 1) * (m + 2) by positivity)
  rw [ha] at h₂'
  rw [hb] at h₁'
  have hgap := ik_scaled_gap m
  change ((m : ℝ) + 1)^2 * (log (IKCount (IKFamily m) : ℝ) - IKRhs (IKFamily m)) =
    log ((m + 1).factorial : ℝ) + (m : ℝ) * (m + 2) * log (Gamma (2 - e)) +
      (m + 1 : ℝ) * (m + 2) * log (Gamma (1 + e)) at hgap
  have hpos : 0 < ((m : ℝ) + 1)^2 * (log (IKCount (IKFamily m) : ℝ) - IKRhs (IKFamily m)) := by
    rw [hgap]
    linarith only [h₂', h₁', ik_log_factorial_bound hm, eulerMascheroniConstant_lt_two_thirds]
  exact sub_pos.mp (pos_of_mul_pos_right hpos (by positivity))
```

## IKCertificate.lean

```lean
import IKAnalysis

open Real
open scoped BigOperators

/-- Integer numerators in the shifted Gamma recurrence at 1 + k/5. -/
def ikChordProduct (n k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, (5 * (i + 1) + k)

private theorem ik_chord_product_pos (n k : ℕ) : 0 < ikChordProduct n k := by
  unfold ikChordProduct
  exact Finset.prod_pos fun _ _ => by positivity

private theorem ik_log_gamma_rec {x : ℝ} (hx : 0 < x) :
    (log ∘ Gamma) (x + 1) = (log ∘ Gamma) x + log x := by
  simp only [Function.comp_apply, Gamma_add_one hx.ne', log_mul hx.ne' (Gamma_pos_of_pos hx).ne']
  ring

/-- Extrapolate the secant from n to n+1, then pull back by n recurrence steps. -/
theorem ik_gamma_chord_fifths {n : ℕ} (hn : 0 < n) {k : ℕ} (hk : 0 < k) :
    log ((n.factorial * 5^n : ℕ) : ℝ) + ((k : ℝ) / 5) * log n -
      log (ikChordProduct n k : ℝ) ≤ log (Gamma (1 + (k : ℝ) / 5)) := by
  let a : ℝ := (k : ℝ) / 5
  have ha : 0 < a := by dsimp [a]; positivity
  have h := BohrMollerup.f_add_nat_ge convexOn_log_Gamma @ik_log_gamma_rec
    (show 2 ≤ n + 1 by omega) ha
  have hf := BohrMollerup.f_add_nat_eq @ik_log_gamma_rec (show 0 < 1 + a by positivity) n
  have hN : (log ∘ Gamma) ((n : ℝ) + 1) = log (n.factorial : ℝ) := by
    rw [Function.comp_apply, Gamma_nat_eq_factorial]
  have hs : ∑ i ∈ Finset.range n, log (1 + a + (i : ℝ)) =
      log (ikChordProduct n k : ℝ) - (n : ℝ) * log 5 := by
    unfold ikChordProduct
    push_cast
    have hc : (∑ _i ∈ Finset.range n, log 5) = (n : ℝ) * log 5 := by
      simp [nsmul_eq_mul]
    rw [log_prod (fun i _ => by positivity), ← hc, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← log_div (by positivity) (by positivity)]
    congr 1
    dsimp [a]
    ring
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at h
  rw [hN, show (n : ℝ) + 1 + a = 1 + a + n by ring, hf, hs] at h
  push_cast
  rw [log_mul (by positivity) (by positivity), log_pow]
  change log (n.factorial : ℝ) + (n : ℝ) * log 5 + a * log n -
    log (ikChordProduct n k : ℝ) ≤ (log ∘ Gamma) (1 + a)
  linarith

/-- Exact integer form of the m = 3 rational certificate. -/
private theorem ik_chord_integer_comparison :
    ikChordProduct 64 4 ^ 15 * ikChordProduct 64 1 ^ 20 <
      24 * (Nat.factorial 64 * 5^64)^35 * 64^16 := by
  decide

theorem ik_family_violation_three :
    IKRhs (IKFamily 3) < log (IKCount (IKFamily 3) : ℝ) := by
  have hi :
      (ikChordProduct 64 4 : ℝ)^15 * (ikChordProduct 64 1 : ℝ)^20 <
        24 * (((Nat.factorial 64 * 5^64 : ℕ) : ℝ)^35) * (64 : ℝ)^16 := by
    exact_mod_cast ik_chord_integer_comparison
  have hp₄ : 0 < (ikChordProduct 64 4 : ℝ) := Nat.cast_pos.mpr (ik_chord_product_pos _ _)
  have hp₁ : 0 < (ikChordProduct 64 1 : ℝ) := Nat.cast_pos.mpr (ik_chord_product_pos _ _)
  have hlog := strictMonoOn_log (Set.mem_Ioi.mpr (by positivity))
    (Set.mem_Ioi.mpr (by positivity)) hi
  rw [log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
    log_mul (by positivity) (by positivity)] at hlog
  simp only [log_pow, Nat.cast_ofNat] at hlog
  have h₄ := ik_gamma_chord_fifths (n := 64) (k := 4) (by decide) (by decide)
  have h₁ := ik_gamma_chord_fifths (n := 64) (k := 1) (by decide) (by decide)
  have hgap := ik_scaled_gap 3
  norm_num only [Nat.cast_ofNat, Nat.cast_one, Nat.factorial] at hgap
  have hgap' :
      16 * (log (IKCount (IKFamily 3) : ℝ) - IKRhs (IKFamily 3)) =
        log 24 + 15 * log (Gamma (1 + 4 / 5)) + 20 * log (Gamma (1 + 1 / 5)) := by
    convert hgap using 2 <;> norm_num
  simp only [Nat.cast_ofNat, Nat.cast_one] at h₄ h₁
  have : 0 < 16 * (log (IKCount (IKFamily 3) : ℝ) - IKRhs (IKFamily 3)) := by
    rw [hgap']
    have hw₄ := mul_le_mul_of_nonneg_left h₄ (show (0 : ℝ) ≤ 15 by norm_num)
    have hw₁ := mul_le_mul_of_nonneg_left h₁ (show (0 : ℝ) ≤ 20 by norm_num)
    let B := log ((Nat.factorial 64 * 5^64 : ℕ) : ℝ)
    let P := log (ikChordProduct 64 4 : ℝ)
    let Q := log (ikChordProduct 64 1 : ℝ)
    calc
      0 < (log 24 + 35 * B + 16 * log 64) - (15 * P + 20 * Q) := sub_pos.mpr hlog
      _ = log 24 + (15 * (B + 4 / 5 * log 64 - P) + 20 * (B + 1 / 5 * log 64 - Q)) := by
        ring
      _ ≤ log 24 + (15 * log (Gamma (1 + 4 / 5)) + 20 * log (Gamma (1 + 1 / 5))) :=
        add_le_add_right (add_le_add hw₄ hw₁) _
      _ = _ := by ring
  linarith
```

## IKRefutation.lean

```lean
import IKCertificate

open Real
open scoped BigOperators

theorem ik_witness_three_count : IKCount (IKFamily 3) = 24 := by
  rw [ik_family_count]
  decide

theorem ik_family_violation {m : ℕ} (hm : 3 ≤ m) :
    IKRhs (IKFamily m) < log (IKCount (IKFamily m) : ℝ) := by
  rcases eq_or_lt_of_le hm with rfl | hm'
  · exact ik_family_violation_three
  · exact ik_family_violation_ge_four hm'

theorem ik_family_violation_base_two {m : ℕ} (hm : 3 ≤ m) :
    (∑ x, IKPsi₂ (IKDeg (IKFamily m) x)
      (((m + 1 : ℕ) : ℝ) * (IKDeg (IKFamily m) x : ℝ) / ((m + 2 : ℕ) : ℝ))) <
      IKLog₂ (IKCount (IKFamily m) : ℝ) := by
  rw [ik_rhs_base_two, IKLog₂]
  exact div_lt_div_of_pos_right (ik_family_violation hm) (log_pos (by norm_num))

theorem ilinca_kahn_conj31_false : IKRefutation :=
  ⟨4, 5, IKFamily 3, by decide, by decide, ik_family_no_isolates (by decide),
    by rw [ik_witness_three_count]; decide, ik_family_violation_three⟩

theorem ilinca_kahn_conj31_not : ¬ IKConjecture := by
  intro h
  obtain ⟨ell, M, a, _, hsize, hisolates, hcount, hgap⟩ := ilinca_kahn_conj31_false
  have hh := h ell M a hsize hisolates hcount
  rw [IKLog₂, ik_rhs_base_two] at hh
  exact (not_lt_of_ge hh) (div_lt_div_of_pos_right hgap (log_pos (by norm_num)))

#check IKConjecture
#check IKRefutation
#check ik_family_no_isolates
#check ik_family_count
#check ik_witness_three_count
#check ik_family_violation_three
#check ik_family_violation_ge_four
#check ik_family_violation
#check ik_family_violation_base_two
#check ilinca_kahn_conj31_false
#check ilinca_kahn_conj31_not
#print axioms IKConjecture
#print axioms IKRefutation
#print axioms ik_family_no_isolates
#print axioms ik_family_count
#print axioms ik_witness_three_count
#print axioms ik_family_violation_three
#print axioms ik_family_violation_ge_four
#print axioms ik_family_violation
#print axioms ik_family_violation_base_two
#print axioms ilinca_kahn_conj31_false
#print axioms ilinca_kahn_conj31_not
```

