module
public import URMatchingWitnessBound
@[expose] public section
namespace URMatching
open scoped Classical
abbrev ValidWitness (N k : ℕ) := {w : CycleDescription N k // ValidDescription w}
noncomputable def witnessCount (N k : ℕ) (σ : PermutationTuples N 100) : ℕ :=
  Fintype.card {w : ValidWitness N k // DescriptionOccurs w.val σ}

theorem witness_double_count (N k : ℕ) :
    ∑ σ : PermutationTuples N 100, witnessCount N k σ =
      ∑ w : ValidWitness N k,
        Fintype.card {σ : PermutationTuples N 100 // DescriptionOccurs w.val σ} := by
  classical
  let e : (Σ σ : PermutationTuples N 100, {w : ValidWitness N k // DescriptionOccurs w.val σ}) ≃
      (Σ w : ValidWitness N k, {σ : PermutationTuples N 100 // DescriptionOccurs w.val σ}) := {
    toFun := fun z => ⟨z.2.val, ⟨z.1,z.2.property⟩⟩
    invFun := fun z => ⟨z.2.val, ⟨z.1,z.2.property⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  simpa only [Fintype.card_sigma, witnessCount] using Fintype.card_congr e

theorem nat_scaled_sum {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ)
    (q r : ℕ) (h : ∀ i ∈ s, q * f i ≤ r) :
    q * (∑ i ∈ s, f i) ≤ s.card * r := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.card_insert_of_notMem hj, Nat.mul_add, Nat.add_mul, Nat.one_mul]
    exact (Nat.add_le_add (h j (Finset.mem_insert_self _ _))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))).trans_eq (Nat.add_comm _ _)

theorem witness_half_bound {N k : ℕ} (w : CycleDescription N k) (hw : ValidDescription w)
    (b : ℕ) (hb : 0 < b) (hsmall : b+2*(k+1) ≤ N) (hlarge : N ≤ 2*b) :
    N^(2*(k+1)) * Fintype.card {σ : PermutationTuples N 100 // DescriptionOccurs w σ} ≤
      2^(2*(k+1)) * (N.factorial)^100 := by
  let E := Fintype.card {σ : PermutationTuples N 100 // DescriptionOccurs w σ}
  have h := witness_integer_bound w hw b hsmall
  refine Nat.le_of_mul_le_mul_left ?_ (Nat.pow_pos hb : 0 < b^(2*(k+1)))
  calc
    _ = N^(2*(k+1)) * (b^(2*(k+1)) * E) := by ac_rfl
    _ ≤ (2*b)^(2*(k+1)) * (b^(2*(k+1)) * E) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hlarge _)
    _ = b^(2*(k+1)) * (2^(2*(k+1)) * (b^(2*(k+1)) * E)) := by rw [Nat.mul_pow]; ac_rfl
    _ ≤ b^(2*(k+1)) * (2^(2*(k+1)) * (N.factorial)^100) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h)

theorem witness_first_moment (N k b : ℕ) (hb : 0 < b)
    (hsmall : b+2*(k+1) ≤ N) (hlarge : N ≤ 2*b) :
    ∑ σ : PermutationTuples N 100, witnessCount N k σ ≤
      200^(2*(k+1)) * Fintype.card (PermutationTuples N 100) := by
  classical
  have hN : 0 < N := hb.trans_le ((Nat.le_add_right b _).trans hsmall)
  have hs := nat_scaled_sum Finset.univ
    (fun w : ValidWitness N k => Fintype.card {σ : PermutationTuples N 100 // DescriptionOccurs w.val σ})
    (N^(2*(k+1))) (2^(2*(k+1)) * (N.factorial)^100)
    (fun w _ => witness_half_bound w.val w.property b hb hsmall hlarge)
  have hc : Fintype.card (ValidWitness N k) ≤ N^(2*(k+1)) * 100^(2*(k+1)) := by
    have h := description_count_bound N k
    convert h using 1
    simp only [pow_mul, pow_two, mul_pow]
    ac_rfl
  rw [Finset.card_univ] at hs
  refine Nat.le_of_mul_le_mul_left ?_ (Nat.pow_pos hN : 0 < N^(2*(k+1)))
  rw [witness_double_count]
  calc
    _ ≤ Fintype.card (ValidWitness N k) * (2^(2*(k+1)) * (N.factorial)^100) := hs
    _ ≤ (N^(2*(k+1)) * 100^(2*(k+1))) * (2^(2*(k+1)) * (N.factorial)^100) := Nat.mul_le_mul_right _ hc
    _ = _ := by
      simp only [PermutationTuples, Fintype.card_pi, Fintype.card_perm, Fintype.card_fin,
        Finset.prod_const, Finset.card_univ]
      rw [show (200 : ℕ) = 100*2 from rfl, Nat.mul_pow]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
end URMatching
