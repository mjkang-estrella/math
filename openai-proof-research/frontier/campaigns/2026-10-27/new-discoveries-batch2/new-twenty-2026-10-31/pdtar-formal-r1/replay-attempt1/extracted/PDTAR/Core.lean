import PDTAR.KstFamily
namespace PDTAR
open Finset
variable {V : Type} [Fintype V] [DecidableEq V]

def SamePD (G H : SimpleGraph V) : Prop := ∀ S, IsPD G S ↔ IsPD H S

theorem fort_covers_side {H K : SimpleGraph V} {A B F : Finset V}
    (hk : CompleteBetween K A B) (he : SamePD K H) (hf : IsFort H F) :
    A ⊆ closed H F ∨ B ⊆ closed H F := by
  classical
  by_cases ha : A ⊆ closed H F
  · exact .inl ha
  · right
    obtain ⟨a,ha,han⟩ := Finset.not_subset.mp ha
    intro b hb
    have hp := (he {a,b}).mp (mixed_pair_isPD hk ha hb)
    obtain ⟨u,hu⟩ := (closed_inter_comm H F _).mp ((fort_duality H _).mp hp F hf)
    obtain ⟨hc,hu⟩ := mem_inter.mp hu
    rcases mem_insert.mp hu with rfl | hu
    · exact False.elim (han hc)
    · exact (mem_singleton.mp hu) ▸ hc

theorem fort_meets_side_twice {H K : SimpleGraph V} {A B F : Finset V}
    (hk : CompleteBetween K A B) (he : SamePD K H) (hf : IsFort H F)
    (ha : 2 ≤ A.card) (hb : B.Nonempty) : 2 ≤ (closed H F ∩ A).card := by
  classical
  have hex : ∀ x ∈ A, (closed H F ∩ A.erase x).Nonempty := by
    intro x hx
    have hcard : 0 < (A.erase x).card := by rw [card_erase_of_mem hx]; omega
    have hp := (he _).mp (erase_part_isPD hk hx (card_pos.mp hcard) hb)
    exact (closed_inter_comm H F _).mp ((fort_duality H _).mp hp F hf)
  by_contra! hc
  obtain ⟨x,hx⟩ := card_pos.mp (by omega : 0 < A.card)
  obtain ⟨u,hu⟩ := hex x hx
  obtain ⟨v,hv⟩ := hex u (mem_of_mem_erase (mem_inter.mp hu).2)
  have hu' : u ∈ closed H F ∩ A := mem_inter.mpr
    ⟨(mem_inter.mp hu).1,mem_of_mem_erase (mem_inter.mp hu).2⟩
  have hv' : v ∈ closed H F ∩ A := mem_inter.mpr
    ⟨(mem_inter.mp hv).1,mem_of_mem_erase (mem_inter.mp hv).2⟩
  have heq := card_le_one.mp (by omega : (closed H F ∩ A).card ≤ 1) u hu' v hv'
  exact (mem_erase.mp (mem_inter.mp hv).2).1 heq.symm

theorem pair_fort {H K : SimpleGraph V} {A B : Finset V}
    (hk : CompleteBetween K A B) (he : SamePD K H)
    (ha : 3 ≤ A.card) (hb : 2 ≤ B.card) {x y : V}
    (hx : x ∈ A) (hy : y ∈ A) (hne : x ≠ y) :
    ∃ F, IsFort H F ∧ closed H F = B ∪ {x,y} := by
  classical
  have hn : ¬ IsPD H (A \ {x,y}) := fun hp =>
    erase_pair_not_isPD hk hx hy hne ((he _).mpr hp)
  have hd := (fort_duality H (A \ {x,y})).not.mp hn
  push Not at hd
  obtain ⟨F,hf,havoid⟩ := hd
  have havoid' : ¬ (closed H F ∩ (A \ {x,y})).Nonempty :=
    by
      intro hh
      obtain ⟨u,hu⟩ := (closed_inter_comm H F _).mpr hh
      rw [havoid] at hu
      simp at hu
  have hA : ∀ u ∈ A, u ∈ closed H F → u ∈ ({x,y} : Finset V) := by
    intro u hu hc
    by_contra hn
    exact havoid' ⟨u,mem_inter.mpr ⟨hc,mem_sdiff.mpr ⟨hu,hn⟩⟩⟩
  have hnotA : ¬ A ⊆ closed H F := by
    intro hh
    have hc := card_le_card (fun u hu => hA u hu (hh hu))
    have hp : ({x,y} : Finset V).card = 2 := by simp [hne]
    omega
  have hB : B ⊆ closed H F := (fort_covers_side hk he hf).resolve_left hnotA
  have htwo := fort_meets_side_twice hk he hf (by omega) (card_pos.mp (by omega))
  have hsub : closed H F ∩ A ⊆ ({x,y} : Finset V) := fun u hu =>
    hA u (mem_inter.mp hu).2 (mem_inter.mp hu).1
  have heq : closed H F ∩ A = {x,y} := by
    apply eq_of_subset_of_card_le hsub
    simpa [hne] using htwo
  refine ⟨F,hf,?_⟩
  apply subset_antisymm
  · intro u hu
    rcases hk.1.mem_or u with huA | huB
    · exact mem_union.mpr (.inr (hA u huA hu))
    · exact mem_union.mpr (.inl huB)
  · intro u hu
    rcases mem_union.mp hu with huB | hup
    · exact hB huB
    · have hh : u ∈ closed H F ∩ A := heq ▸ hup
      exact (mem_inter.mp hh).1
end PDTAR
