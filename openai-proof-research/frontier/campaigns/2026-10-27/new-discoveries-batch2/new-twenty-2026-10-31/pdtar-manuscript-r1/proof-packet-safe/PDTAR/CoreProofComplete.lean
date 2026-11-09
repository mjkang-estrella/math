import PDTAR.CoreProofDegree
import PDTAR.CoreProofIndependent
namespace PDTAR
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open Finset
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Two distinct elements constrained to a pair exhaust that pair. -/
theorem core_pair_exhaust {u v x y : V} (hu : u = x ∨ u = y)
    (hv : v = x ∨ v = y) (hne : u ≠ v) :
    (u = x ∧ v = y) ∨ (u = y ∧ v = x) := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact False.elim (hne rfl)
  · exact .inl ⟨rfl,rfl⟩
  · exact .inr ⟨rfl,rfl⟩
  · exact False.elim (hne rfl)

theorem core_fourth {A : Finset V} (ha : 4 ≤ A.card) (x y z : V) :
    ∃ w ∈ A, w ≠ x ∧ w ≠ y ∧ w ≠ z := by
  classical
  by_contra! h
  have hs : A ⊆ {x,y,z} := by
    intro w hw
    by_cases hx : w = x
    · simp [hx]
    by_cases hy : w = y
    · simp [hy]
    simp [h w hw hx hy]
  have hc := card_le_card hs
  have h1 := card_insert_le x ({y,z} : Finset V)
  have h2 := card_insert_le y ({z} : Finset V)
  simp only [card_singleton] at h2
  omega

/-- The cross neighbourhood of a fort vertex is exactly the supported pair. -/
theorem core_supported_cross {H : SimpleGraph V} {A B F : Finset V}
    (hp : Parts A B) {p b d : V} (hC : closed H F = A ∪ {b,d}) (hpF : p ∈ F)
    (htwo : ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ H.Adj p u ∧ H.Adj p v) :
    H.Adj p b ∧ H.Adj p d ∧ (∀ u ∈ B, H.Adj p u → u = b ∨ u = d) := by
  have hsub : ∀ u ∈ B, H.Adj p u → u = b ∨ u = d := by
    intro u hu hadj
    exact core_pair_internal ⟨hp.1.symm,by simpa [union_comm] using hp.2⟩ hC hpF hu hadj
  obtain ⟨u,hu,v,hv,huv,hpu,hpv⟩ := htwo
  rcases core_pair_exhaust (hsub u hu hpu) (hsub v hv hpv) huv with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨hpu,hpv,hsub⟩
  · exact ⟨hpv,hpu,hsub⟩

/-- A supported vertex has two internal neighbours in a fort supported on a disjoint pair. -/
theorem core_disjoint_support {H : SimpleGraph V} {A B F : Finset V}
    (hp : Parts A B) {p b c e : V} (hpA : p ∈ A) (hb : b ∈ B)
    (hbc : b ≠ c) (hbe : b ≠ e) (hpc : ¬ H.Adj p c) (hpe : ¬ H.Adj p e)
    (hpb : H.Adj p b) (hf : IsFort H F) (hC : closed H F = A ∪ {c,e}) :
    ∃ u ∈ F, ∃ v ∈ F, u ∈ A ∧ v ∈ A ∧ u ≠ v ∧ H.Adj p u ∧ H.Adj p v := by
  have hpC : p ∈ closed H F := by rw [hC]; simp [hpA]
  have hpF : p ∉ F := by
    intro hpF
    have hbC := core_fort_neighbor hpF hpb
    rw [hC] at hbC
    rcases mem_union.mp hbC with hbA | hbp
    · exact hp.not_both hbA hb
    · simp only [mem_insert,mem_singleton] at hbp
      exact hbp.elim hbc hbe
  obtain ⟨u,hu,v,hv,huv,hpu,hpv⟩ := fort_two_neighbors H hf hpC hpF
  have hin : ∀ u ∈ F, H.Adj p u → u ∈ A := by
    intro u hu hpu
    have huC := subset_closed H F hu
    rw [hC] at huC
    rcases mem_union.mp huC with huA | hup
    · exact huA
    · rcases mem_insert.mp hup with rfl | hup
      · exact False.elim (hpc hpu)
      · exact False.elim (hpe ((mem_singleton.mp hup) ▸ hpu))
  exact ⟨u,hu,v,hv,hin u hu hpu,hin v hv hpv,huv,hpu,hpv⟩

/-- Lemma 6 with the large side second. -/
theorem core_complete_large {K H : SimpleGraph V} {A B : Finset V}
    (hk : CompleteBetween K A B) (he : SamePD K H)
    (ha : 3 ≤ A.card) (hb : 4 ≤ B.card)
    (hA : ∀ p ∈ A, ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ H.Adj p u ∧ H.Adj p v)
    (hB : ∀ p ∈ B, ∃ u ∈ A, ∃ v ∈ A, u ≠ v ∧ H.Adj p u ∧ H.Adj p v) :
    ∀ a ∈ A, ∀ b ∈ B, H.Adj a b := by
  classical
  intro a haA b hbB
  obtain ⟨d,hd,hdb,_⟩ := core_third (by omega : 3 ≤ B.card) b b
  obtain ⟨F,hf,hC⟩ := pair_fort (completeBetween_swap hk) he (by omega) (by omega) hbB hd hdb.symm
  have hmiss : ∀ p ∈ F, p ∉ A := by
    intro p hpF hpA
    have hpcross := core_supported_cross hk.1 hC hpF (hA p hpA)
    obtain ⟨c,hc,hcb,hcd⟩ := core_third (by omega : 3 ≤ B.card) b d
    obtain ⟨e,heB,heb,hed,hec⟩ := core_fourth hb b d c
    obtain ⟨F',hf',hC'⟩ := pair_fort (completeBetween_swap hk) he (by omega) (by omega) hc heB hec.symm
    have hpc : ¬ H.Adj p c := fun h => (hpcross.2.2 c hc h).elim hcb hcd
    have hpe : ¬ H.Adj p e := fun h => (hpcross.2.2 e heB h).elim heb hed
    obtain ⟨q,hqF',r,hrF',hqA,hrA,hqr,hpq,hpr⟩ :=
      core_disjoint_support hk.1 hpA hbB hcb.symm heb.symm hpc hpe hpcross.1 hf' hC'
    have hqcross := core_supported_cross hk.1 hC' hqF' (hA q hqA)
    have hqb : ¬ H.Adj q b := fun h => (hqcross.2.2 b hbB h).elim hcb.symm heb.symm
    have hqd : ¬ H.Adj q d := fun h => (hqcross.2.2 d hd h).elim hcd.symm hed.symm
    obtain ⟨u,_,v,_,huA,hvA,huv,hqu,hqv⟩ :=
      core_disjoint_support hk.1 hqA hc hcb hcd hqb hqd hqcross.1 hf hC
    have hpq : p ≠ q := H.ne_of_adj hpq
    obtain ⟨P,hP,hCP⟩ := pair_fort hk he ha (by omega) hpA hqA hpq
    have hpP : p ∉ P := by
      intro hpP
      have hreq := core_pair_internal hk.1 hCP hpP hrA hpr
      have hrq := hreq.resolve_left (fun h => H.ne_of_adj hpr h.symm)
      exact hqr hrq.symm
    have hqP : q ∉ P := by
      intro hqP
      have hueq := core_pair_internal hk.1 hCP hqP huA hqu
      have hveq := core_pair_internal hk.1 hCP hqP hvA hqv
      have hup := hueq.resolve_right (fun h => H.ne_of_adj hqu h.symm)
      have hvp := hveq.resolve_right (fun h => H.ne_of_adj hqv h.symm)
      exact huv (hup.trans hvp.symm)
    have hPB : P ⊆ B := by
      intro x hx
      have hh := subset_closed H P hx
      rw [hCP] at hh
      rcases mem_union.mp hh with hxB | hxp
      · exact hxB
      · rcases mem_insert.mp hxp with rfl | hxp
        · exact False.elim (hpP hx)
        · exact False.elim (hqP ((mem_singleton.mp hxp) ▸ hx))
    have hpCP : p ∈ closed H P := by rw [hCP]; simp
    obtain ⟨x,hx,y,hy,hxy,hpx,hpy⟩ := fort_two_neighbors H hP hpCP hpP
    have hpair := core_pair_exhaust (hpcross.2.2 x (hPB hx) hpx) (hpcross.2.2 y (hPB hy) hpy) hxy
    have hbP : b ∈ P := by
      rcases hpair with ⟨rfl,_⟩ | ⟨_,rfl⟩
      · exact hx
      · exact hy
    obtain ⟨x,hxA,y,hyA,hxy,hbx,hby⟩ := hB b hbB
    have hxp := (core_pair_internal hk.1 hCP hbP hxA hbx).resolve_right
      (fun h => hqb (h ▸ hbx.symm))
    have hyp := (core_pair_internal hk.1 hCP hbP hyA hby).resolve_right
      (fun h => hqb (h ▸ hby.symm))
    exact hxy (hxp.trans hyp.symm)
  have hsub : F ⊆ {b,d} := by
    intro u hu
    have huC := subset_closed H F hu
    rw [hC] at huC
    exact (mem_union.mp huC).resolve_left (hmiss u hu)
  have hF := core_pair_fort_eq (core_noIsolated hk he (by omega) (by omega)) hf hsub
  have haC : a ∈ closed H F := by rw [hC]; simp [haA]
  have haF : a ∉ F := fun h => hmiss a h haA
  obtain ⟨x,hx,y,hy,hxy,hax,hay⟩ := fort_two_neighbors H hf haC haF
  rw [hF] at hx hy
  have hpair := core_pair_exhaust (by simpa only [mem_insert,mem_singleton] using hx)
    (by simpa only [mem_insert,mem_singleton] using hy) hxy
  rcases hpair with ⟨rfl,_⟩ | ⟨_,rfl⟩
  · exact hax
  · exact hay
end PDTAR
