module
public import URMatchingWitnessPrescriptions
public import URMatchingWitnessDistinct
@[expose] public section
namespace URMatching
open scoped Classical
theorem slot_mem_domain {N k : ℕ} (w : CycleDescription N k)
    (s : Bool × Fin (k+1)) : slotInput w s ∈ witnessDomain w (slotColour w s) := by
  obtain ⟨b,i⟩ := s
  cases b
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨i, Or.inl ⟨rfl,rfl⟩⟩⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨i, Or.inr ⟨rfl,rfl⟩⟩⟩

noncomputable def slotDomainMap {N k : ℕ} (w : CycleDescription N k)
    (s : Bool × Fin (k+1)) : Σ c : Fin 100, witnessDomain w c :=
  ⟨slotColour w s, ⟨slotInput w s, slot_mem_domain w s⟩⟩

theorem slotDomainMap_surjective {N k : ℕ} (w : CycleDescription N k) :
    Function.Surjective (slotDomainMap w) := by
  rintro ⟨c,x,hx⟩
  obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hx).2
  rcases hi with ⟨hc,he⟩ | ⟨hc,he⟩
  · subst c; subst x
    exact ⟨(false,i), rfl⟩
  · subst c; subst x
    exact ⟨(true,i), rfl⟩

theorem witness_total_prescriptions {N k : ℕ} (w : CycleDescription N k)
    (hw : ValidDescription w) (τ : PermutationTuples N 100) (hτ : DescriptionOccurs w τ) :
    ∑ c : Fin 100, (witnessDomain w c).card = 2 * (k+1) := by
  classical
  have inj : Function.Injective (slotDomainMap w) := by
    intro s t h
    apply slots_injective w hw τ hτ
    exact congrArg (fun z : Σ c : Fin 100, witnessDomain w c => (z.1,z.2.val)) h
  have e := Equiv.ofBijective (slotDomainMap w) ⟨inj,slotDomainMap_surjective w⟩
  have h := Fintype.card_congr e
  simpa only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin,
    Fintype.card_sigma, Fintype.card_coe] using h.symm
end URMatching
