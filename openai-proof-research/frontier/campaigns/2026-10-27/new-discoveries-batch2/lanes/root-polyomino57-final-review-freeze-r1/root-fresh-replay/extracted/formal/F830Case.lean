import F830Batch0
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace F830
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof
def pairs : List (Finset GridPoint × Finset GridPoint) := pairs0
theorem coverage : free.powersetCard 1 ⊆ (pairs.map Prod.fst).toFinset := by decide
theorem checks : ∀ es ∈ pairs, CutGood (forced ∪ es.1) es.2 ∨ Disjoint (forced ∪ es.1) miss := by
  intro es he
  exact checked0 es he
theorem case_8_3_0 : ∀ Q : Finset GridPoint, Q ⊆ domain 8 3 0 → EdgeConnected Q →
    Q.card = 11 → ¬ HitsAll Q (groups 8 3 0) := by
  intro Q hQ hc hn hh
  have hf := forced_sub hh
  have hsub : Q \ forced ⊆ free := by
    intro p hp
    have ht := hQ (Finset.mem_sdiff.mp hp).1
    rw [domain_parts] at ht
    exact (Finset.mem_union.mp ht).resolve_left (Finset.mem_sdiff.mp hp).2
  have hcard : (Q \ forced).card = 1 := by
    rw [Finset.card_sdiff_of_subset hf, hn, forced_card]
  have he : Q \ forced ∈ free.powersetCard 1 := Finset.mem_powersetCard.mpr ⟨hsub,hcard⟩
  have hm := List.mem_toFinset.mp (coverage he)
  obtain ⟨es,hes,heq⟩ := List.mem_map.mp hm
  have hu : forced ∪ es.1 = Q := by rw [heq]; exact Finset.union_sdiff_of_subset hf
  have bad := checks es hes
  rw [hu] at bad
  rcases bad with cut | dis
  · exact not_connected_of_cut cut hc
  · obtain ⟨p,hp,hpg⟩ := hh miss miss_group
    exact Finset.disjoint_left.mp dis hp hpg

end F830
