import PDTAR.CoreSmallProof
namespace PDTAR
open Finset

/-- One missing observed vertex is forced in a graph without isolated vertices. -/
theorem small_step_of_one_missing {V : Type} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} (hH : NoIsolated H) {O : Finset V}
    (hO : ∀ x y, x ∉ O → y ∉ O → x = y) : step H O = univ := by
  apply eq_univ_of_forall
  intro u
  by_cases hu : u ∈ O
  · exact subset_step H O hu
  obtain ⟨v,huv⟩ := hH u
  have hv : v ∈ O := by
    by_contra hv
    exact H.ne_of_adj huv (hO u v hu hv)
  exact (mem_step H O u).mpr (.inr ⟨v,hv,huv.symm,fun w _ hw => hO w u hw hu⟩)

/-- The PD family is insensitive to the internal edge on the two-vertex side. -/
theorem small_two_family (t : ℕ) (ht : 1 ≤ t)
    (H : SimpleGraph (Fin 2 ⊕ Fin t))
    (hcross : ∀ a b, H.Adj (Sum.inl a) (Sum.inr b))
    (hright : ∀ b c, ¬ H.Adj (Sum.inr b) (Sum.inr c))
    (S : Finset (Fin 2 ⊕ Fin t)) :
    IsPD H S ↔ S.Nonempty ∧ ((∃ a, Sum.inl a ∈ S) ∨
      ∀ b c, Sum.inr b ∉ S → Sum.inr c ∉ S → b = c) := by
  classical
  have hH : NoIsolated H := by
    intro v
    cases v with
    | inl a => exact ⟨Sum.inr ⟨0,by omega⟩,hcross _ _⟩
    | inr b => exact ⟨Sum.inl 0,(hcross _ _).symm⟩
  constructor
  · intro hp
    have hne : S.Nonempty := by
      by_contra hn
      have hs : S = ∅ := not_nonempty_iff_eq_empty.mp hn
      have hf : IsFort H univ := ⟨univ_nonempty,by simp⟩
      have := (fort_duality H S).mp hp univ hf
      simp [hs,closed] at this
    refine ⟨hne,?_⟩
    by_cases hl : ∃ a, Sum.inl a ∈ S
    · exact .inl hl
    right
    intro b c hb hc
    by_contra hbc
    have hf : IsFort H {Sum.inr b,Sum.inr c} := by
      refine ⟨by simp,?_⟩
      intro v _ u hu hvu
      cases v with
      | inr d =>
        rcases mem_insert.mp hu with rfl | hu
        · exact False.elim (hright d b hvu)
        · exact False.elim (hright d c ((mem_singleton.mp hu) ▸ hvu))
      | inl a =>
        rcases mem_insert.mp hu with rfl | hu
        · exact ⟨Sum.inr c,by simp,by simpa using Ne.symm hbc,hcross _ _⟩
        · have he := mem_singleton.mp hu
          subst u
          exact ⟨Sum.inr b,by simp,by simpa using hbc,hcross _ _⟩
    obtain ⟨u,hu⟩ := (fort_duality H S).mp hp _ hf
    have havoid : ∀ d, Sum.inr d ∈ closed H S → Sum.inr d ∈ S := by
      intro d hd
      rcases (mem_closed H S _).mp hd with hd | ⟨v,hv,hvd⟩
      · exact hd
      cases v with
      | inl a => exact False.elim (hl ⟨a,hv⟩)
      | inr e => exact False.elim (hright e d hvd)
    rcases mem_insert.mp (mem_inter.mp hu).1 with rfl | hu'
    · exact hb (havoid b (mem_inter.mp hu).2)
    · exact hc (havoid c ((mem_singleton.mp hu') ▸ (mem_inter.mp hu).2))
  · rintro ⟨hne,hl | hr⟩
    · obtain ⟨a,ha⟩ := hl
      have hB : ∀ b, Sum.inr b ∈ closed H S := fun b =>
        (mem_closed H S _).mpr (.inr ⟨Sum.inl a,ha,hcross _ _⟩)
      refine ⟨2,small_step_of_one_missing hH ?_⟩
      intro x y hx hy
      cases x with
      | inr b => exact False.elim (hx (hB b))
      | inl b =>
        cases y with
        | inr c => exact False.elim (hy (hB c))
        | inl c =>
          have hba : b ≠ a := fun he => hx (he ▸ subset_closed H S ha)
          have hca : c ≠ a := fun he => hy (he ▸ subset_closed H S ha)
          congr 1
          fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all
    · by_cases hl : ∃ a, Sum.inl a ∈ S
      · obtain ⟨a,ha⟩ := hl
        -- A mixed pair already dominates if S also meets the other side.
        by_cases hb : ∃ b, Sum.inr b ∈ S
        · obtain ⟨b,hb⟩ := hb
          refine ⟨1,eq_univ_of_forall fun x => ?_⟩
          cases x with
          | inl c => exact (mem_closed H S _).mpr (.inr ⟨Sum.inr b,hb,(hcross _ _).symm⟩)
          | inr c => exact (mem_closed H S _).mpr (.inr ⟨Sum.inl a,ha,hcross _ _⟩)
        · have hB : ∀ b, Sum.inr b ∈ closed H S := fun b =>
            (mem_closed H S _).mpr (.inr ⟨Sum.inl a,ha,hcross _ _⟩)
          refine ⟨2,small_step_of_one_missing hH ?_⟩
          intro x y hx hy
          cases x with
          | inr b => exact False.elim (hx (hB b))
          | inl b =>
            cases y with
            | inr c => exact False.elim (hy (hB c))
            | inl c =>
              have hba : b ≠ a := fun he => hx (he ▸ subset_closed H S ha)
              have hca : c ≠ a := fun he => hy (he ▸ subset_closed H S ha)
              congr 1
              fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all
      · obtain ⟨v,hv⟩ := hne
        cases v with
        | inl a => exact False.elim (hl ⟨a,hv⟩)
        | inr b =>
          have hA : ∀ a, Sum.inl a ∈ closed H S := fun a =>
            (mem_closed H S _).mpr (.inr ⟨Sum.inr b,hv,(hcross _ _).symm⟩)
          refine ⟨2,small_step_of_one_missing hH ?_⟩
          intro x y hx hy
          cases x with
          | inl a => exact False.elim (hx (hA a))
          | inr c =>
            cases y with
            | inl a => exact False.elim (hy (hA a))
            | inr d => exact congrArg Sum.inr (hr c d
                (fun hc => hx (subset_closed H S hc)) (fun hd => hy (subset_closed H S hd)))
end PDTAR
