import PDTAR.Final
namespace PDTAR
open Finset

/-- Every distinct pair is PD in K(3,3). -/
theorem small_k33_pair (x y : Fin 3 ⊕ Fin 3) (hxy : x ≠ y) :
    IsPD (completeBipartiteGraph (Fin 3) (Fin 3)) {x,y} := by
  refine ⟨2,small_step_of_one_missing (small_sum_noIsolated 3 3 (by omega) (by omega)) ?_⟩
  intro u v hu hv
  rcases x with x | x <;> rcases y with y | y <;>
    rcases u with u | u <;> rcases v with v | v
  all_goals simp_all [propagate,closed,completeBipartiteGraph]
  all_goals omega

/-- No singleton is PD in K(3,3). -/
theorem small_k33_singleton (x : Fin 3 ⊕ Fin 3) :
    ¬ IsPD (completeBipartiteGraph (Fin 3) (Fin 3)) {x} := by
  let K := completeBipartiteGraph (Fin 3) (Fin 3)
  have hp := sum_parts 3 3
  have ht : ∀ {A B : Finset (Fin 3 ⊕ Fin 3)}, CompleteBetween K A B →
      3 ≤ A.card → ∀ x ∈ A, ¬ IsPD K {x} := by
    intro A B hk ha x hx hpd
    obtain ⟨y,hy,hyx,_⟩ := core_third ha x x
    obtain ⟨z,hz,hzx,hzy⟩ := core_third ha x y
    obtain ⟨u,hu⟩ := (fort_duality K _).mp hpd _ (pair_isFort hk hy hz hzy.symm)
    have huA : u ∈ A := by
      rcases mem_insert.mp (mem_inter.mp hu).1 with rfl | hh
      · exact hy
      · exact mem_singleton.mp hh ▸ hz
    rcases (mem_closed K _ _).mp (mem_inter.mp hu).2 with hs | ⟨v,hv,ha⟩
    · have hux := mem_singleton.mp hs
      have hh := (mem_inter.mp hu).1
      simp [hux,hyx.symm,hzx.symm] at hh
    · have hvx := mem_singleton.mp hv
      subst v
      rcases (hk.2 _ _).mp ha with h | h
      · exact hk.1.not_both huA h.2
      · exact hk.1.not_both hx h.1
  rcases hp.1.mem_or x with hx | hx
  · exact ht hp (by simp [leftPart]) x hx
  · exact ht (completeBetween_swap hp) (by simp [rightPart]) x hx

/-- The small-degree obstruction in the source proof, expressed by three neighbours. -/
theorem small_k33_three_neighbors {H : SimpleGraph (Fin 3 ⊕ Fin 3)}
    (hH : NoIsolated H) (he : SamePD (completeBipartiteGraph (Fin 3) (Fin 3)) H)
    (v : Fin 3 ⊕ Fin 3) :
    ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ H.Adj v a ∧ H.Adj v b ∧ H.Adj v c := by
  classical
  obtain ⟨u,hvu⟩ := hH v
  have hn : ¬ IsPD H {u} := fun h => small_k33_singleton u ((he _).mpr h)
  have hd := (fort_duality H {u}).not.mp hn
  push Not at hd
  obtain ⟨F,hf,havoid⟩ := hd
  have huC : u ∉ closed H F := by
    intro hu
    obtain ⟨w,hw⟩ := (closed_inter_comm H F {u}).mpr ⟨u,by simp [hu]⟩
    rw [havoid] at hw; simp at hw
  have hvF : v ∉ F := fun h => huC (core_fort_neighbor h hvu)
  have hvC : v ∈ closed H F := by
    have hp := (he _).mp (small_k33_pair u v (H.ne_of_adj hvu).symm)
    obtain ⟨w,hw⟩ := (closed_inter_comm H F {u,v}).mp ((fort_duality H _).mp hp F hf)
    have hww := (mem_inter.mp hw).2
    rcases mem_insert.mp hww with hwu | hwv
    · exact False.elim (huC (hwu ▸ (mem_inter.mp hw).1))
    · exact mem_singleton.mp hwv ▸ (mem_inter.mp hw).1
  obtain ⟨a,ha,b,hb,hab,hva,hvb⟩ := fort_two_neighbors H hf hvC hvF
  have hua : u ≠ a := fun h => huC (subset_closed H F (h.symm ▸ ha))
  have hub : u ≠ b := fun h => huC (subset_closed H F (h.symm ▸ hb))
  exact ⟨u,a,b,hua,hub,hab,hvu,hva,hvb⟩
end PDTAR
