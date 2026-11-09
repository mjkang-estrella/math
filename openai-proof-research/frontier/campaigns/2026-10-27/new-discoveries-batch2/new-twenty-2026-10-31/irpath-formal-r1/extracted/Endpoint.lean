import Finite
open Finset
namespace IR350452
/-- Every irredundant set of `G9` has at most three vertices. -/
lemma irredundant_card_le {D : Finset (Fin 9)} (h : Irredundant G9 D) : D.card ≤ 3 := by
  by_contra hlt
  have hlt : 3 < D.card := Nat.lt_of_not_ge hlt
  obtain ⟨D', hD'sub, hD'card⟩ := Finset.exists_subset_card_eq (show 4 ≤ D.card by omega)
  -- (in older Mathlib: `Finset.exists_smaller_set D 4 _`)
  exact no_irredundant_four D'
    (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hD'card⟩) (h.mono hD'sub)

lemma walk_irredundant (i : Fin 9) : Irredundant G9 (walk i) :=
  (irredundant_three_iff (walk i)
    (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, walk_card i⟩)).mpr ⟨i, rfl⟩

lemma isIRSet_iff (D : Finset (Fin 9)) : IsIRSet G9 D ↔ ∃ i : Fin 9, walk i = D := by
  change IRSet G9 D ↔ _
  rw [irSet_iff_max]
  constructor
  · rintro ⟨hirr, hmax⟩
    have hge : 3 ≤ D.card := by
      have := hmax (walk 0) (walk_irredundant 0)
      rwa [walk_card] at this
    have hcard : D.card = 3 := le_antisymm (irredundant_card_le hirr) hge
    exact (irredundant_three_iff D
      (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩)).mp hirr
  · rintro ⟨i, rfl⟩
    refine ⟨walk_irredundant i, fun D' hD' => ?_⟩
    rw [walk_card]
    exact irredundant_card_le hD'

theorem ir_G9 : IR G9 = 3 := by
  obtain ⟨D, hD, hc⟩ := ir_attained G9
  apply le_antisymm
  · exact hc ▸ irredundant_card_le hD
  · have h := ir_upper (walk_irredundant 0)
    rwa [walk_card] at h

/-- Finite check (c): swap-adjacency between the listed IR-sets is exactly path adjacency. -/
lemma swap_walk_iff :
    ∀ i j : Fin 9, Swap G9 (walk i) (walk j) ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
  decide

/-- The vertex map `Fin 9 → G9(IR)`. -/
def toIR (i : Fin 9) : {D : Finset (Fin 9) // IsIRSet G9 D} :=
  ⟨walk i, (isIRSet_iff _).mpr ⟨i, rfl⟩⟩

lemma toIR_bijective : Function.Bijective toIR := by
  constructor
  · intro i j h
    exact walk_injective (congrArg Subtype.val h)
  · rintro ⟨D, hD⟩
    obtain ⟨i, rfl⟩ := (isIRSet_iff D).mp hD
    exact ⟨i, rfl⟩

/-- `P_9 ≃g G9(IR)`. -/
noncomputable def pathIso : SimpleGraph.pathGraph 9 ≃g IRGraph G9 where
  toEquiv := Equiv.ofBijective toIR toIR_bijective
  map_rel_iff' := by
    intro i j
    show Swap G9 (walk i) (walk j) ↔ (SimpleGraph.pathGraph 9).Adj i j
    rw [SimpleGraph.pathGraph_adj, swap_walk_iff]

/-- `P_9` is an IR-graph. -/
theorem pathGraph_nine_isIRGraph : IsIRGraph (SimpleGraph.pathGraph 9) :=
  ⟨Fin 9, inferInstance, inferInstance, G9, ⟨pathIso⟩⟩

def Conjecture : Prop :=
  (∀ n : ℕ, 3 ≤ n → ¬ IsIRGraph (SimpleGraph.pathGraph n)) ∧
  (∀ n : ℕ, 5 ≤ n → ¬ IsIRGraph (SimpleGraph.cycleGraph n))

theorem conjecture_false : ¬ Conjecture := by
  rintro ⟨hP, -⟩
  exact hP 9 (by norm_num) pathGraph_nine_isIRGraph

end IR350452
