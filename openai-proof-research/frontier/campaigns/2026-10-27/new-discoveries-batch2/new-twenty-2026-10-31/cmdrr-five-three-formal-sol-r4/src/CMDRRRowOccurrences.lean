import CMDRRIncidenceSums

open scoped Classical
namespace CMDRR
namespace Game
variable {M W : Type}
theorem all_teams_iff_other (g : Game M W) (a : {p // p ∈ g.teams}) (P : W → Prop) :
    (∀ t ∈ g.teams, P t.2) ↔ P a.1.2 ∧ P (g.other a).1.2 := by
  constructor
  · intro h
    exact ⟨h _ a.2,h _ (g.other a).2⟩
  · rintro ⟨ha,hb⟩ t ht
    by_cases he : t = a.1
    · simpa [he] using ha
    · have he' := (g.opposite_unique a.2).choose_spec.2 t ⟨ht,he⟩
      change t = (g.other a).1 at he'
      simpa [he'] using hb
end Game

namespace Source
variable {M W O : Type} [Fintype O]
variable {s : Matching M W} {d : Schedule M W O} (h : Source s d)
noncomputable def rowOccurrence (m : M) (w : Row (s := s) m) : O :=
  (h.partnership_unique w.2).choose
theorem rowOccurrence_partner (m : M) (w : Row (s := s) m) :
    (d.game (h.rowOccurrence m w)).Partners m w.1 :=
  (h.partnership_unique w.2).choose_spec.1

theorem rowOccurrence_injective (m : M) : Function.Injective (h.rowOccurrence m) := by
  intro a b he
  apply Subtype.ext
  have ha := h.rowOccurrence_partner m a
  have hb := h.rowOccurrence_partner m b
  rw [← he] at hb
  exact (d.game _).partner_unique_woman ha hb

theorem rowOccurrence_all (m : M) (w : Row (s := s) m) (P : W → Prop) :
    (∀ t ∈ (d.game (h.rowOccurrence m w)).teams, P t.2) ↔
      P w.1 ∧ P (h.rowPerm m w).1 := by
  let o := h.rowOccurrence m w
  let a : {p // p ∈ (d.game o).teams} := ⟨(m,w.1),h.rowOccurrence_partner m w⟩
  have he : h.cellsEquiv ⟨o,a⟩ = rowCell m w := rfl
  have hu := h.U_incidence ⟨o,a⟩
  rw [he,← h.rowCell_perm] at hu
  have hv := congrArg (fun c : Cell s => c.1.2) hu
  change (h.rowPerm m w).1 = ((d.game o).other a).1.2 at hv
  simpa only [hv] using (d.game o).all_teams_iff_other a P

/-- Actual row edges correspond bijectively to game occurrences containing that man.
This preserves both female endpoints and counts an occurrence once per man. -/
theorem row_internal_occurrences [Fintype W] (m : M) (P : W → Prop) :
    count (fun w : Row (s := s) m => P w.1 ∧ P (h.rowPerm m w).1) =
    count (fun o => (∃ w, (d.game o).Partners m w) ∧
      ∀ t ∈ (d.game o).teams, P t.2) := by
  classical
  let e : {w : Row (s := s) m // P w.1 ∧ P (h.rowPerm m w).1} ≃
      {o : O // (∃ w, (d.game o).Partners m w) ∧ ∀ t ∈ (d.game o).teams, P t.2} :=
    Equiv.ofBijective
      (fun w => ⟨h.rowOccurrence m w.1,
        ⟨⟨w.1.1,h.rowOccurrence_partner m w.1⟩,
          (h.rowOccurrence_all m w.1 P).mpr w.2⟩⟩)
      (by
        constructor
        · intro a b he
          apply Subtype.ext
          exact h.rowOccurrence_injective m (congrArg Subtype.val he)
        · rintro ⟨o,⟨⟨w,hw⟩,hP⟩⟩
          let a : Row (s := s) m := ⟨w,h.allowed hw⟩
          have ho : h.rowOccurrence m a = o :=
            h.occurrence_eq (h.rowOccurrence_partner m a) hw
          have ha : P a.1 ∧ P (h.rowPerm m a).1 := by
            apply (h.rowOccurrence_all m a P).mp
            rw [ho]
            exact hP
          exact ⟨⟨a,ha⟩,Subtype.ext ho⟩)
  rw [count_eq_card,count_eq_card]
  exact @Fintype.card_congr _ _
    (@Subtype.fintype (Row (s := s) m) (fun w => P w.1 ∧ P (h.rowPerm m w).1)
      (fun _ => Classical.propDecidable _) inferInstance)
    (@Subtype.fintype O (fun o => (∃ w, (d.game o).Partners m w) ∧
      ∀ t ∈ (d.game o).teams, P t.2) (fun _ => Classical.propDecidable _) inferInstance) e
end Source
end CMDRR
