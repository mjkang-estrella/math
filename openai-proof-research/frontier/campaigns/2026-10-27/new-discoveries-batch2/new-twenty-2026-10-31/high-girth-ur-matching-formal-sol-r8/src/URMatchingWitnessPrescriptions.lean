module
public import URMatchingCycleDescriptions
@[expose] public section
namespace URMatching
open scoped Classical
noncomputable def witnessDomain {N k : ℕ} (w : CycleDescription N k)
    (c : Fin 100) : Finset (Fin N) :=
  Finset.univ.filter fun x => ∃ i : Fin (k+1),
    (w.2.2.1 i = c ∧ w.1 i = x) ∨ (w.2.2.2 i = c ∧ w.1 (i+1) = x)

theorem occurs_iff_prescriptions {N k : ℕ} (w : CycleDescription N k)
    (τ : PermutationTuples N 100) (hτ : DescriptionOccurs w τ)
    (σ : PermutationTuples N 100) :
    DescriptionOccurs w σ ↔ ∀ c, restriction (witnessDomain w c) (σ c) =
      restriction (witnessDomain w c) (τ c) := by
  classical
  constructor
  · intro h c
    apply DFunLike.ext
    intro x
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp x.property).2
    change σ c x.val = τ c x.val
    rcases hi with ⟨hc, hx⟩ | ⟨hc, hx⟩
    · subst c; rw [← hx]; exact (h i).1.trans (hτ i).1.symm
    · subst c; rw [← hx]; exact (h i).2.trans (hτ i).2.symm
  · intro h i
    constructor
    · have hx : w.1 i ∈ witnessDomain w (w.2.2.1 i) := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨i, Or.inl ⟨rfl,rfl⟩⟩⟩
      have e := congrArg (fun f : witnessDomain w (w.2.2.1 i) ↪ Fin N =>
        f ⟨w.1 i, hx⟩) (h (w.2.2.1 i))
      exact e.trans (hτ i).1
    · have hx : w.1 (i+1) ∈ witnessDomain w (w.2.2.2 i) := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨i, Or.inr ⟨rfl,rfl⟩⟩⟩
      have e := congrArg (fun f : witnessDomain w (w.2.2.2 i) ↪ Fin N =>
        f ⟨w.1 (i+1), hx⟩) (h (w.2.2.2 i))
      exact e.trans (hτ i).2

theorem occurring_witness_count {N k : ℕ} (w : CycleDescription N k)
    (τ : PermutationTuples N 100) (hτ : DescriptionOccurs w τ) :
    Fintype.card {σ : PermutationTuples N 100 // DescriptionOccurs w σ} =
      ∏ c, (N - (witnessDomain w c).card).factorial := by
  classical
  have e : {σ : PermutationTuples N 100 // DescriptionOccurs w σ} ≃
      {σ : PermutationTuples N 100 // ∀ c, restriction (witnessDomain w c) (σ c) =
        restriction (witnessDomain w c) (τ c)} :=
    Equiv.subtypeEquivRight (occurs_iff_prescriptions w τ hτ)
  exact (Fintype.card_congr e).trans
    (independent_prescription_count N 100 (witnessDomain w)
      (fun c => restriction (witnessDomain w c) (τ c)))

theorem inconsistent_witness_count {N k : ℕ} (w : CycleDescription N k)
    (h : ¬ ∃ σ, DescriptionOccurs w σ) :
    Fintype.card {σ : PermutationTuples N 100 // DescriptionOccurs w σ} = 0 := by
  classical
  let : IsEmpty {σ : PermutationTuples N 100 // DescriptionOccurs w σ} :=
    ⟨fun σ => h ⟨σ.val, σ.property⟩⟩
  exact Fintype.card_eq_zero
end URMatching
