module
public import URMatchingWitnessTotal
@[expose] public section
namespace URMatching
open scoped Classical
theorem nat_term_le_sum {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ)
    (i : α) (hi : i ∈ s) : f i ≤ ∑ j ∈ s, f j := by
  induction s using Finset.induction_on with
  | empty => exact False.elim (Finset.notMem_empty i hi)
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj]
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact Nat.le_add_right _ _
    · exact (ih hi).trans (Nat.le_add_left _ _)

theorem nat_prod_mono {α : Type*} [DecidableEq α] (s : Finset α) (f g : α → ℕ)
    (h : ∀ i ∈ s, f i ≤ g i) : (∏ i ∈ s, f i) ≤ ∏ i ∈ s, g i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    exact Nat.mul_le_mul (h j (Finset.mem_insert_self _ _))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem factorial_power_lower (b r t : ℕ) (hb : b ≤ t+1) :
    b^r * t.factorial ≤ (t+r).factorial := by
  induction r generalizing t with
  | zero => simp
  | succ r ih =>
    have h := ih (t+1) (hb.trans (Nat.le_succ _))
    calc
      b^(r+1) * t.factorial = b^r * (b * t.factorial) := by rw [pow_succ, Nat.mul_assoc]
      _ ≤ b^r * ((t+1) * t.factorial) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hb)
      _ = b^r * (t+1).factorial := by rw [Nat.factorial_succ]
      _ ≤ (t+1+r).factorial := h
      _ = (t+(r+1)).factorial := by rw [Nat.add_right_comm t 1 r, Nat.add_assoc]

theorem factorial_prescription_bound (N b r : ℕ) (h : b+r ≤ N) :
    b^r * (N-r).factorial ≤ N.factorial := by
  have hr : r ≤ N := (Nat.le_add_left r b).trans h
  have hb : b ≤ N-r := Nat.le_sub_of_add_le h
  simpa only [Nat.sub_add_cancel hr] using
    factorial_power_lower b r (N-r) (hb.trans (Nat.le_succ _))

theorem witness_integer_bound {N k : ℕ} (w : CycleDescription N k)
    (hw : ValidDescription w) (b : ℕ) (hb : b + 2*(k+1) ≤ N) :
    b^(2*(k+1)) * Fintype.card {σ : PermutationTuples N 100 // DescriptionOccurs w σ} ≤
      (N.factorial)^100 := by
  classical
  by_cases he : ∃ τ, DescriptionOccurs w τ
  · obtain ⟨τ,hτ⟩ := he
    rw [occurring_witness_count w τ hτ]
    have ht := witness_total_prescriptions w hw τ hτ
    have each : ∀ c ∈ (Finset.univ : Finset (Fin 100)),
        b^((witnessDomain w c).card) * (N-(witnessDomain w c).card).factorial ≤ N.factorial := by
      intro c _
      have hc : (witnessDomain w c).card ≤ 2*(k+1) := by
        rw [← ht]
        exact nat_term_le_sum Finset.univ (fun c => (witnessDomain w c).card) c (Finset.mem_univ c)
      exact factorial_prescription_bound N b _ ((Nat.add_le_add_left hc b).trans hb)
    have hp := nat_prod_mono Finset.univ _ _ each
    simpa only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      ht, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hp
  · rw [inconsistent_witness_count w he, Nat.mul_zero]
    exact Nat.zero_le _
end URMatching
