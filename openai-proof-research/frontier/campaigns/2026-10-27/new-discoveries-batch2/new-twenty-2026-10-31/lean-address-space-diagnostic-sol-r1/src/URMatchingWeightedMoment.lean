module
public import URMatchingWitnessMoment
public import URMatchingHoleUnion
@[expose] public section
namespace URMatching
open scoped Classical
noncomputable def witnessWeight (N h : ℕ) (σ : PermutationTuples N 100) : ℕ :=
  ∑ k ∈ Finset.range h, 2*(k+1) * witnessCount N k σ
def witnessBudget (h : ℕ) : ℕ := ∑ k ∈ Finset.range h, 2*(k+1) * 200^(2*(k+1))

theorem nat_sum_mono {α : Type*} [DecidableEq α] (s : Finset α) (f g : α → ℕ)
    (h : ∀ i ∈ s, f i ≤ g i) : (∑ i ∈ s, f i) ≤ ∑ i ∈ s, g i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact Nat.add_le_add (h j (Finset.mem_insert_self _ _))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem nat_mul_sum {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ) (q : ℕ) :
    q * (∑ i ∈ s, f i) = ∑ i ∈ s, q*f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, Nat.mul_add, ih]

theorem nat_sum_mul {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ) (q : ℕ) :
    (∑ i ∈ s, f i) * q = ∑ i ∈ s, f i*q := by
  simpa only [Nat.mul_comm] using nat_mul_sum s f q

theorem weighted_first_moment (a h : ℕ) (ha : 0 < a) (hh : h ≤ a) :
    ∑ σ : PermutationTuples (4*a) 100, witnessWeight (4*a) h σ ≤
      witnessBudget h * Fintype.card (PermutationTuples (4*a) 100) := by
  classical
  unfold witnessWeight witnessBudget
  rw [Finset.sum_comm, nat_sum_mul]
  apply nat_sum_mono
  intro k hk
  rw [← nat_mul_sum]
  rw [Nat.mul_assoc (2*(k+1))]
  apply Nat.mul_le_mul_left
  have hk' : k < h := Finset.mem_range.mp hk
  exact witness_first_moment (4*a) k (2*a) (by omega) (by omega) (by omega)

/-- Finite Markov bound, retaining the scale100 without rounding. -/
theorem finite_markov {Ω : Type*} [Fintype Ω] (S : Ω → ℕ) (N : ℕ) :
    N * (Finset.univ.filter fun σ => N ≤ 100*S σ).card ≤ 100 * ∑ σ, S σ := by
  classical
  let bad := Finset.univ.filter fun σ => N ≤ 100*S σ
  have hf : ∀ σ, (if σ ∈ bad then N else 0) ≤ 100*S σ := by
    intro σ
    split
    · rename_i h
      exact (Finset.mem_filter.mp h).2
    · exact Nat.zero_le _
  have hs := nat_sum_mono Finset.univ _ _ (fun σ _ => hf σ)
  rw [nat_mul_sum]
  simpa only [← Finset.sum_filter, Finset.sum_const,
    smul_eq_mul, bad, Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.mul_comm] using hs

noncomputable def heavyEvent (a h : ℕ) : Finset (PermutationTuples (4*a) 100) :=
  Finset.univ.filter fun σ => 4*a ≤ 100*witnessWeight (4*a) h σ

theorem heavy_event_strict (a h : ℕ) (ha : 0 < a) (hh : h ≤ a)
    (hbig : 400*witnessBudget h < 4*a) :
    4*(heavyEvent a h).card < Fintype.card (PermutationTuples (4*a) 100) := by
  have hm := finite_markov (witnessWeight (4*a) h) (4*a)
  have he := weighted_first_moment a h ha hh
  have hp : 0 < Fintype.card (PermutationTuples (4*a) 100) := Fintype.card_pos
  apply Nat.lt_of_mul_lt_mul_left (a := 4*a)
  calc
    _ = 4 * ((4*a) * (heavyEvent a h).card) := by ac_rfl
    _ ≤ 4 * (100 * ∑ σ, witnessWeight (4*a) h σ) := Nat.mul_le_mul_left 4 hm
    _ ≤ 4 * (100 * (witnessBudget h * Fintype.card (PermutationTuples (4*a) 100))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ he)
    _ = (400*witnessBudget h) * Fintype.card (PermutationTuples (4*a) 100) := by rw [show (400 : ℕ) = 4*100 from rfl]; simp only [Nat.mul_assoc]
    _ < _ := Nat.mul_lt_mul_of_pos_right hbig hp
end URMatching
