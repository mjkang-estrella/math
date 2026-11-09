import PDTAR.Final
namespace PDTAR
set_option linter.unusedSectionVars false
open Finset
variable {V : Type} [Fintype V] [DecidableEq V]
theorem small_star_pair_fort {H K : SimpleGraph V} {A B : Finset V}
    (hk : CompleteBetween K A B) (he : SamePD K H)
    (ha : 3 ≤ A.card) (hb : B.Nonempty) {x y : V}
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
  have htwo := fort_meets_side_twice hk he hf (by omega) hb
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

/-- A PD singleton cannot lie in a proper union of components. -/
theorem small_star_component {H : SimpleGraph V} {F : Finset V} {c : V}
    (hc : c ∈ F) (hF : closed H F = F) (hp : IsPD H {c}) : F = univ := by
  have hs : closed H {c} ⊆ F := hF ▸ closed_singleton_subset H hc
  have hstep : ∀ O, O ⊆ F → step H O ⊆ F := by
    intro O hO u hu
    rcases (mem_step H O u).mp hu with hu | ⟨v,hv,ha,_⟩
    · exact hO hu
    · rw [← hF]; exact core_fort_neighbor (hO hv) ha
  obtain ⟨n,hn⟩ := hp
  apply univ_subset_iff.mp
  rw [← hn]
  cases n with
  | zero => exact singleton_subset_iff.mpr hc
  | succ n =>
    change propagate H (closed H {c}) n ⊆ F
    clear hn
    induction n with
    | zero => exact hs
    | succ n ih => exact hstep _ ih

/-- The two vertices of a pair fort are twins outside the pair. -/
theorem small_star_twins {H : SimpleGraph V} {c x : V}
    (hf : IsFort H {c,x}) {v : V} (hc : v ≠ c) (hx : v ≠ x) :
    H.Adj v c ↔ H.Adj v x := by
  constructor
  · intro ha
    obtain ⟨w,hw,hwc,ha⟩ := hf.2 v (by simp [hc,hx]) c (by simp) ha
    have hwx : w = x := by simpa [hwc] using hw
    exact hwx ▸ ha
  · intro ha
    obtain ⟨w,hw,hwx,ha⟩ := hf.2 v (by simp [hc,hx]) x (by simp) ha
    have hwc : w = c := by simpa [hwx] using hw
    exact hwc ▸ ha

/-- Swapping a pair fort preserves adjacency. -/
theorem small_star_swap {H : SimpleGraph V} {c x : V}
    (hf : IsFort H {c,x}) : reductionPull (Equiv.swap c x) H = H := by
  classical
  ext u v
  change H.Adj (Equiv.swap c x u) (Equiv.swap c x v) ↔ H.Adj u v
  by_cases hcx : c = x
  · subst x; simp
  have ht := @small_star_twins V _ _ H c x hf
  by_cases hu : u = c <;> by_cases hux : u = x <;>
    by_cases hv : v = c <;> by_cases hvx : v = x
  all_goals subst_vars
  all_goals simp_all [Equiv.swap_apply_def, H.adj_comm]
  all_goals exact (ht hu hux).symm.trans (H.adj_comm _ _)

/-- In a pair fort, PD singleton status is the same at either vertex. -/
theorem small_star_pair_PD {H : SimpleGraph V} {c x : V}
    (hf : IsFort H {c,x}) (hp : IsPD H {c}) : IsPD H {x} := by
  classical
  have hp' : IsPD (reductionPull (Equiv.swap c x) H) {c} := by
    rw [small_star_swap hf]; exact hp
  have hh := (reduction_isPD_transport (Equiv.swap c x) H {c}).mp hp'
  simpa using hh
end PDTAR
