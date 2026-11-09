import UlasExactReadout
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
open Polynomial
namespace Ulas.Round4

theorem main_term_coeff (m E F : ℕ) (a : ℤ) :
    (if E = 0 ∨ E%2 = 1 then Round3.reducedTerm m E 0 a else 0).coeff F =
      (if E = 0 ∧ F = 0 then 2*((m:ℤ)+1)*a else 0) +
      (if E = 2*F+1 then a else 0) := by
  by_cases he : E = 0
  · subst E
    simp only [true_or, ite_true, Round3.reducedTerm, Nat.zero_div, Nat.zero_mod,
      mul_zero, zero_add, add_zero, pow_one, Nat.choose_one_right, Nat.cast_add, Nat.cast_one, coeff_monomial]
    by_cases hf : F = 0 <;> simp [hf, Eq.comm] <;> ring
  · by_cases ho : E%2 = 1
    · have hn : E%2 ≠ 0 := by omega
      have hf : E/2 = F ↔ E = 2*F+1 := by omega
      simp [he, ho, Round3.reducedTerm, hn, coeff_monomial, hf]
    · have hh : E ≠ 2*F+1 := by omega
      simp [he, ho, hh]

theorem coeff_reducedMain (m F : ℕ) (R : Polynomial ℤ) :
    (Round3.reducedMain m R).coeff F =
      (if F = 0 then 2*((m:ℤ)+1)*R.coeff 0 else 0) + R.coeff (2*F+1) := by
  unfold Round3.reducedMain
  have h (E : ℕ) : (∑ i ∈ Finset.range (m+E/2+2),
      if i = 0 ∧ (E = 0 ∨ E%2 = 1) then Round3.reducedTerm m E i (R.coeff E) else 0) =
      if E = 0 ∨ E%2 = 1 then Round3.reducedTerm m E 0 (R.coeff E) else 0 := by
    simp only [ite_and, Finset.sum_ite_eq', Finset.mem_range]
    simp
  rw [show (∑ E ∈ R.support, ∑ i ∈ Finset.range (m+E/2+2),
      if i = 0 ∧ (E = 0 ∨ E%2 = 1) then Round3.reducedTerm m E i (R.coeff E) else 0) =
      ∑ E ∈ R.support, if E = 0 ∨ E%2 = 1 then Round3.reducedTerm m E 0 (R.coeff E) else 0
      from Finset.sum_congr rfl (fun E _ => h E)]
  simp only [finsetSum_coeff, main_term_coeff, Finset.sum_add_distrib, ite_and,
    Finset.sum_ite_eq', mem_support_iff]
  split_ifs <;> simp_all

def EvenInvariant (v : ℕ) (R : Polynomial ℤ) : Prop :=
  Round3.Weighted v R ∧ ¬ (2:ℤ)^(v+1) ∣ R.coeff 0 ∧
  ∀ i, 1 ≤ i → (2:ℤ)^(v+i+1) ∣ R.coeff (2^i-1)

/-- The invariant already supplies all nonconstant divisibilities used by readout. -/
theorem invariant_high {v : ℕ} {R : Polynomial ℤ} (h : EvenInvariant v R)
    (E : ℕ) (he : E ≠ 0) : (2:ℤ)^(v+1) ∣ R.coeff E := by
  have hs : 1 ≤ E.size := Nat.size_pos.mpr (Nat.pos_of_ne_zero he)
  exact dvd_trans (pow_dvd_pow _ (by omega : v+1 ≤ v+E.size)) (h.1 E)

theorem exact_readout_invariant (m v n : ℕ) (R : Polynomial ℤ)
    (h : EvenInvariant v R) (hn : n%2 = 1) :
    padicValInt 2 (PowerSeries.coeff n (Ulas.C^m*(y*(1+y)*ev R))) = v := by
  exact exact_readout m v n R hn (by simpa using h.1 0) h.2.1 (invariant_high h)

theorem size_pow_sub_one (i : ℕ) : (2^(i+1)-1).size = i+1 := by
  induction i with
  | zero => decide
  | succ i ih =>
    have hp : 0 < 2^(i+1) := by positivity
    have he : 2^(i+1+1)-1 = 2*(2^(i+1)-1)+1 := by rw [pow_succ]; omega
    rw [show i+1+1 = (i+1)+1 by omega, he, Round3.size_double_add_one, ih]

theorem invariant_step (m v : ℕ) (R : Polynomial ℤ)
    (hm : m%2 = 0) (h : EvenInvariant v R) :
    EvenInvariant (v+1) (Round3.reduced m R) := by
  refine ⟨Round3.weighted_reduced m v R h.1, ?_, ?_⟩
  · have hrz : R.coeff 0 ≠ 0 := by
      intro hz
      exact h.2.1 (by simp [hz])
    have hrv : padicValInt 2 (R.coeff 0) = v :=
      val_exact_of_divisibility _ v (by simpa using h.1 0) h.2.1
    have hodd : ¬ (2:ℤ) ∣ ((m:ℤ)+1) := by
      intro hd
      have hd' : (2:ℕ) ∣ m+1 := by exact_mod_cast hd
      have := Nat.mod_eq_zero_of_dvd hd'
      omega
    have hmz : (m:ℤ)+1 ≠ 0 := by omega
    have hv : padicValInt 2 (2*((m:ℤ)+1)*R.coeff 0) = v+1 := by
      rw [padicValInt.mul (mul_ne_zero (by norm_num) hmz) hrz,
        padicValInt.mul (by norm_num) hmz, padicValInt.eq_zero_of_not_dvd hodd, hrv]
      have htwo : padicValInt 2 (2:ℤ) = 1 := by
        simpa using (padicValInt.self (by decide : 1 < (2:ℕ)))
      rw [htwo]
      omega
    have hnd : ¬ (2:ℤ)^(v+2) ∣ 2*((m:ℤ)+1)*R.coeff 0 := by
      intro hd
      have hh := ((padicValInt_dvd_iff (p := 2) (v+2) _).mp hd).resolve_left
        (mul_ne_zero (mul_ne_zero (by norm_num) hmz) hrz)
      omega
    have h1 := h.2.2 1 (by omega)
    norm_num at h1
    rw [Round3.coeff_reduced_zero]
    intro hd
    exact hnd (by simpa [show v+1+1 = v+2 by omega] using dvd_sub hd h1)
  · intro i hi
    have hip : 1 < 2^i := by
      have hp := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hi
      norm_num at hp
      omega
    have hs : (2^i-1).size = i := by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      exact size_pow_sub_one j
    rw [Round3.reduced_main_tail, coeff_add, coeff_reducedMain, ite_eq_right (by omega)]
    have hmain := h.2.2 (i+1) (by omega)
    have ht := Round3.weighted_reducedTail m v R h.1 (2^i-1)
    rw [hs] at ht
    have he : 2*(2^i-1)+1 = 2^(i+1)-1 := by rw [pow_succ]; omega
    rw [he]
    exact dvd_add (by convert hmain using 1 <;> congr 1 <;> omega)
      (by convert ht using 1 <;> congr 1 <;> omega)

theorem invariant_iter (m v j : ℕ) (R : Polynomial ℤ)
    (hm : m%2 = 0) (h : EvenInvariant v R) :
    EvenInvariant (v+j) (Round3.reducedIter m R j) := by
  induction j with
  | zero => simpa [Round3.reducedIter] using h
  | succ j ih => exact invariant_step m (v+j) _ hm ih

/-- The remaining even initialization is stated exactly; no axiom is introduced. -/
def EvenInitialization : Prop := ∀ k : ℕ, 1 ≤ k → ∃ R : Polynomial ℤ,
  Round2.transferDiff (2*k) 0 = y*(1+y)*ev R ∧
  EvenInvariant (3+2*padicValNat 2 k) R

theorem evenFormula_of_initialization (hinit : EvenInitialization) : EvenFormula := by
  intro k n hk hn
  obtain ⟨R, hR, hI⟩ := hinit k hk
  obtain ⟨o, ho⟩ := pow_padicValNat_dvd (p := 2) (n := n)
  have hond : ¬ 2 ∣ o := by
    intro hd
    apply pow_succ_padicValNat_not_dvd (p := 2) (by omega : n ≠ 0)
    rw [pow_succ]
    conv_rhs => rw [ho]
    exact mul_dvd_mul_left _ hd
  have ho_odd : o%2 = 1 := by
    have hh : o%2 ≠ 0 := fun hz => hond (Nat.dvd_of_mod_eq_zero hz)
    omega
  refine ⟨diff_ne_zero (2*k) n (by omega) hn, ?_⟩
  have hv := exact_readout_invariant (2*k) (3+2*padicValNat 2 k+padicValNat 2 n) o
    (Round3.reducedIter (2*k) R (padicValNat 2 n))
    (invariant_iter (2*k) _ _ R (by omega) hI) ho_odd
  rw [← diff_reduced_readout (2*k) (padicValNat 2 n) o R hR, ← ho] at hv
  unfold val targetEven
  omega
end Ulas.Round4
