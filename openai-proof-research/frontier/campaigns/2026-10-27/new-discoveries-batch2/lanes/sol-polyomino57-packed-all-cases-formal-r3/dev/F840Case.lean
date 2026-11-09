import F840Cover0
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace F840
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof
theorem coverage : ∀ E ∈ free.powersetCard 3, E ∈ pairs.map Prod.fst := cover0
theorem checks : ∀ es ∈ pairs, CutGood (forced ∪ es.1) es.2 ∨ Disjoint (forced ∪ es.1) miss := by
  intro es he
  simp only [pairs, List.mem_append] at he
  rcases he with ((((((((((((((((((((((((((((hh0 | hh1) | hh2) | hh3) | hh4) | hh5) | hh6) | hh7) | hh8) | hh9) | hh10) | hh11) | hh12) | hh13) | hh14) | hh15) | hh16) | hh17) | hh18) | hh19) | hh20) | hh21) | hh22) | hh23) | hh24) | hh25) | hh26) | hh27) | hh28)
  · exact checked0 es hh0
  · exact checked1 es hh1
  · exact checked2 es hh2
  · exact checked3 es hh3
  · exact checked4 es hh4
  · exact checked5 es hh5
  · exact checked6 es hh6
  · exact checked7 es hh7
  · exact checked8 es hh8
  · exact checked9 es hh9
  · exact checked10 es hh10
  · exact checked11 es hh11
  · exact checked12 es hh12
  · exact checked13 es hh13
  · exact checked14 es hh14
  · exact checked15 es hh15
  · exact checked16 es hh16
  · exact checked17 es hh17
  · exact checked18 es hh18
  · exact checked19 es hh19
  · exact checked20 es hh20
  · exact checked21 es hh21
  · exact checked22 es hh22
  · exact checked23 es hh23
  · exact checked24 es hh24
  · exact checked25 es hh25
  · exact checked26 es hh26
  · exact checked27 es hh27
  · exact checked28 es hh28
theorem case_8_4_0 : ∀ Q : Finset GridPoint, Q ⊆ domain 8 4 0 → EdgeConnected Q →
    Q.card = 11 → ¬ HitsAll Q (groups 8 4 0) := by
  intro Q hQ hc hn hh
  have hf := forced_sub hh
  have hsub : Q \ forced ⊆ free := by
    intro p hp
    have ht := hQ (Finset.mem_sdiff.mp hp).1
    rw [domain_parts] at ht
    exact (Finset.mem_union.mp ht).resolve_left (Finset.mem_sdiff.mp hp).2
  have hcard : (Q \ forced).card = 3 := by
    rw [Finset.card_sdiff_of_subset hf, hn, forced_card]
  have he : Q \ forced ∈ free.powersetCard 3 := Finset.mem_powersetCard.mpr ⟨hsub,hcard⟩
  have hm := coverage _ he
  obtain ⟨es,hes,heq⟩ := List.mem_map.mp hm
  have hu : forced ∪ es.1 = Q := by rw [heq]; exact Finset.union_sdiff_of_subset hf
  have bad := checks es hes
  rw [hu] at bad
  rcases bad with cut | dis
  · exact not_connected_of_cut cut hc
  · obtain ⟨p,hp,hpg⟩ := hh miss miss_group
    exact Finset.disjoint_left.mp dis hp hpg

end F840
