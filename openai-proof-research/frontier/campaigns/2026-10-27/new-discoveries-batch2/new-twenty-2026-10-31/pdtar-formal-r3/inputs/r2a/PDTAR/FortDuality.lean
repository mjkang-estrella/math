import PDTAR.Basic
namespace PDTAR
set_option linter.unusedSectionVars false
open Finset
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

theorem fort_step_avoids {F O : Finset V} (hF : IsFort G F)
    (h : ∀ u ∈ F, u ∉ O) : ∀ u ∈ F, u ∉ step G O := by
  intro u hu hs
  rcases (mem_step G O u).mp hs with ho | ⟨v,hv,ha,huniq⟩
  · exact h u hu ho
  · obtain ⟨w,hw,hne,hadj⟩ := hF.2 v (fun hf => h v hf hv) u hu ha
    exact hne (huniq w hadj (h w hw))

theorem fort_propagate_avoids {F O : Finset V} (hF : IsFort G F)
    (h : ∀ u ∈ F, u ∉ O) (n : ℕ) : ∀ u ∈ F, u ∉ propagate G O n := by
  induction n with
  | zero => exact h
  | succ n ih => exact fort_step_avoids G hF ih

theorem stable_complement_fort {O : Finset V} (hO : O ≠ univ)
    (hs : step G O = O) : IsFort G (univ \ O) := by
  classical
  constructor
  · have hex : ∃ u, u ∉ O := by
      by_contra! h
      exact hO (eq_univ_of_forall h)
    obtain ⟨u,hu⟩ := hex
    exact ⟨u, by simp [hu]⟩
  · intro v hv u hu ha
    have hvO : v ∈ O := by simpa using hv
    have huO : u ∉ O := (mem_sdiff.mp hu).2
    by_contra! hn
    have hforce : u ∈ step G O := (mem_step G O u).mpr (.inr ⟨v,hvO,ha,by
      intro w hw hwo
      by_contra hne
      exact hn w (by simp [hwo]) hne hw⟩)
    exact huO (hs ▸ hforce)

theorem fort_duality (S : Finset V) : IsPD G S ↔
    ∀ F, IsFort G F → (F ∩ closed G S).Nonempty := by
  classical
  constructor
  · rintro ⟨n,hn⟩ F hF
    by_contra! hm
    have havoid : ∀ u ∈ F, u ∉ closed G S := by
      intro u hu hc
      have hh := mem_inter.mpr ⟨hu,hc⟩
      rw [hm] at hh
      simp at hh
    obtain ⟨u,hu⟩ := hF.1
    cases n with
    | zero =>
      have he : S = univ := hn
      exact havoid u hu (subset_closed G S (he ▸ mem_univ u))
    | succ n =>
      change propagate G (closed G S) n = univ at hn
      exact fort_propagate_avoids G hF havoid n u hu (hn ▸ mem_univ u)
  · intro hall
    obtain ⟨n,_,hs⟩ := propagate_stable G (closed G S)
    by_cases he : propagate G (closed G S) n = univ
    · exact ⟨n+1,he⟩
    · have hf := stable_complement_fort G he hs
      obtain ⟨u,hu⟩ := hall _ hf
      have huO := (mem_sdiff.mp (mem_inter.mp hu).1).2
      exact False.elim (huO (propagate_increasing G (closed G S) (Nat.zero_le n)
        (mem_inter.mp hu).2))

theorem closed_singleton_subset {F : Finset V} {x : V} (hx : x ∈ F) :
    closed G {x} ⊆ closed G F := closed_mono G (singleton_subset_iff.mpr hx)

theorem fort_two_neighbors {F : Finset V} (hf : IsFort G F) {x : V}
    (hx : x ∈ closed G F) (hn : x ∉ F) :
    ∃ u ∈ F, ∃ w ∈ F, u ≠ w ∧ G.Adj x u ∧ G.Adj x w := by
  rcases (mem_closed G F x).mp hx with h | ⟨u,hu,ha⟩
  · exact False.elim (hn h)
  · obtain ⟨w,hw,hne,ha'⟩ := hf.2 x hn u hu ha.symm
    exact ⟨u,hu,w,hw,Ne.symm hne,ha.symm,ha'⟩

theorem singleton_fort_iff (x : V) : IsFort G {x} ↔ ∀ y, ¬ G.Adj x y := by
  classical
  constructor
  · intro hf y ha
    have hy : y ∉ ({x} : Finset V) := by simpa using G.ne_of_adj ha.symm
    obtain ⟨w,hw,hne,_⟩ := hf.2 y hy x (by simp) ha.symm
    exact hne (mem_singleton.mp hw)
  · intro h
    refine ⟨by simp, ?_⟩
    intro v _ u hu ha
    have he := mem_singleton.mp hu
    subst u
    exact False.elim (h v ha.symm)

theorem closed_inter_comm (F S : Finset V) :
    (F ∩ closed G S).Nonempty ↔ (closed G F ∩ S).Nonempty := by
  constructor
  · rintro ⟨u,hu⟩
    obtain ⟨hf,hc⟩ := mem_inter.mp hu
    rcases (mem_closed G S u).mp hc with hs | ⟨v,hv,ha⟩
    · exact ⟨u,mem_inter.mpr ⟨subset_closed G F hf,hs⟩⟩
    · exact ⟨v,mem_inter.mpr ⟨(mem_closed G F v).mpr (.inr ⟨u,hf,ha.symm⟩),hv⟩⟩
  · rintro ⟨u,hu⟩
    obtain ⟨hc,hs⟩ := mem_inter.mp hu
    rcases (mem_closed G F u).mp hc with hf | ⟨v,hv,ha⟩
    · exact ⟨u,mem_inter.mpr ⟨hf,subset_closed G S hs⟩⟩
    · exact ⟨v,mem_inter.mpr ⟨hv,(mem_closed G S v).mpr (.inr ⟨u,hs,ha.symm⟩)⟩⟩
end PDTAR
