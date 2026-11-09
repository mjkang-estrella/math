import PDTAR.SmallStarLocal
namespace PDTAR
set_option linter.unnecessarySimpa false
open Finset
variable {V : Type} [Fintype V] [DecidableEq V]

/-- A fort supported on the centre and a leaf pair cannot contain the centre. -/
theorem small_star_avoids_center {H : SimpleGraph V} {F : Finset V} {c x y : V}
    (hH : NoIsolated H) (hf : IsFort H F) (hC : closed H F = {c,x,y})
    (hp : IsPD H {c}) (hx : ¬ IsPD H {x}) (hy : ¬ IsPD H {y})
    (hz : ∃ z, z ∉ ({c,x,y} : Finset V)) : c ∉ F := by
  classical
  intro hc
  have hs : F ⊆ {c,x,y} := hC ▸ subset_closed H F
  by_cases hxF : x ∈ F
  · by_cases hyF : y ∈ F
    · have heq : F = {c,x,y} := subset_antisymm hs (by simp [insert_subset_iff,hc,hxF,hyF])
      have hall := small_star_component hc (by rw [hC,heq]) hp
      obtain ⟨z,hz⟩ := hz
      exact hz (heq ▸ hall ▸ mem_univ z)
    · have hsub : F ⊆ {c,x} := by
        intro u hu
        have := hs hu
        simp only [mem_insert,mem_singleton] at this ⊢
        rcases this with h | h | h
        · exact .inl h
        · exact .inr h
        · exact False.elim (hyF (h ▸ hu))
      have heq := core_pair_fort_eq hH hf hsub
      exact hx (small_star_pair_PD (heq ▸ hf) hp)
  · have hsub : F ⊆ {c,y} := by
      intro u hu
      have := hs hu
      simp only [mem_insert,mem_singleton] at this ⊢
      rcases this with h | h | h
      · exact .inl h
      · exact False.elim (hxF (h ▸ hu))
      · exact .inr h
    have heq := core_pair_fort_eq hH hf hsub
    exact hy (small_star_pair_PD (heq ▸ hf) hp)

/-- Labelled rigidity of a star from its PD family. -/
theorem small_star_rigid {K H : SimpleGraph V} {A : Finset V} {c : V}
    (hk : CompleteBetween K A {c}) (he : SamePD K H)
    (ha : 3 ≤ A.card) (hH : NoIsolated H) : H = K := by
  classical
  have hcA : c ∉ A := fun h => hk.1.not_both h (by simp)
  have hp : IsPD H {c} := (he _).mp ⟨1,eq_univ_of_forall (by
    intro u
    rcases hk.1.mem_or u with hu | hu
    · exact (mem_closed K _ _).mpr (.inr ⟨c,by simp,(hk.2 _ _).mpr (.inr ⟨by simp,hu⟩)⟩)
    · exact subset_closed K _ hu)⟩
  have hnon : ∀ x ∈ A, ¬ IsPD H {x} := by
    intro x hx hp'
    obtain ⟨y,hy,hyx,_⟩ := core_third ha x x
    obtain ⟨z,hz,hzx,hzy⟩ := core_third ha x y
    have hf := pair_isFort hk hy hz hzy.symm
    obtain ⟨u,hu⟩ := (fort_duality K _).mp ((he _).mpr hp') _ hf
    have huA : u ∈ A := by
      rcases mem_insert.mp (mem_inter.mp hu).1 with rfl | hh
      · exact hy
      · exact mem_singleton.mp hh ▸ hz
    rcases (mem_closed K _ _).mp (mem_inter.mp hu).2 with huS | ⟨v,hv,hvu⟩
    · have hux := mem_singleton.mp huS
      have hh := (mem_inter.mp hu).1
      simp [hux,hyx.symm,hzx.symm] at hh
    · have hvx := mem_singleton.mp hv
      subst v
      rcases (hk.2 _ _).mp hvu with h | h
      · exact hk.1.not_both huA h.2
      · exact hk.1.not_both hx h.1
  have hfort : ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
      IsFort H {x,y} ∧ closed H {x,y} = {c,x,y} := by
    intro x hx y hy hxy
    obtain ⟨F,hf,hC⟩ := small_star_pair_fort hk he ha (by simp) hx hy hxy
    have hC' : closed H F = {c,x,y} := by simpa only [singleton_union] using hC
    have hcF : c ∉ F := by
      apply small_star_avoids_center hH hf hC' hp (hnon x hx) (hnon y hy)
      obtain ⟨z,hz,hzx,hzy⟩ := core_third ha x y
      have hzc : z ≠ c := fun h => hcA (h ▸ hz)
      exact ⟨z,by simp [hzx,hzy,hzc]⟩
    have hs : F ⊆ {x,y} := by
      intro u hu
      have hh := hC' ▸ subset_closed H F hu
      simp only [mem_insert,mem_singleton] at hh ⊢
      exact hh.resolve_left (fun h => hcF (h ▸ hu))
    have hF := core_pair_fort_eq hH hf hs
    exact ⟨hF ▸ hf,by simpa [hF] using hC'⟩
  have hcross : ∀ x ∈ A, H.Adj c x := by
    intro x hx
    obtain ⟨y,hy,hyx,_⟩ := core_third ha x x
    obtain ⟨hf,hC⟩ := hfort x hx y hy hyx.symm
    have hcC : c ∈ closed H {x,y} := by rw [hC]; simp
    have hcF : c ∉ ({x,y} : Finset V) := by
      have hcx : c ≠ x := fun h => hcA (h.symm ▸ hx)
      have hcy : c ≠ y := fun h => hcA (h.symm ▸ hy)
      simp [hcx,hcy]
    obtain ⟨u,hu,v,hv,huv,hcu,hcv⟩ := fort_two_neighbors H hf hcC hcF
    rcases core_pair_exhaust (by simpa using hu) (by simpa using hv) huv with h | h
    · exact h.1 ▸ hcu
    · exact h.2 ▸ hcv
  have hind : ∀ x ∈ A, ∀ y ∈ A, ¬ H.Adj x y := by
    intro x hx y hy hxy
    obtain ⟨z,hz,hzx,hzy⟩ := core_third ha x y
    obtain ⟨_,hC⟩ := hfort x hx z hz hzx.symm
    have hyC := core_fort_neighbor (by simp : x ∈ ({x,z} : Finset V)) hxy
    rw [hC] at hyC
    have hyc : y ≠ c := fun h => hcA (h ▸ hy)
    simpa [hyc,H.ne_of_adj hxy |>.symm,hzy.symm] using hyC
  ext u v
  rw [hk.2]
  rcases hk.1.mem_or u with hu | hu <;> rcases hk.1.mem_or v with hv | hv
  · have huc : u ≠ c := fun h => hcA (h ▸ hu)
    have hvc : v ≠ c := fun h => hcA (h ▸ hv)
    simp [hu,hv,hind u hu v hv,huc,hvc]
  · have hv := mem_singleton.mp hv; subst v
    simp [hu,hcross u hu |>.symm]
  · have hu := mem_singleton.mp hu; subst u
    simp [hv,hcross v hv]
  · have hu := mem_singleton.mp hu; have hv := mem_singleton.mp hv
    subst u; subst v; simp [hcA]
end PDTAR
