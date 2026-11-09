import CMDRRGameIncidences
open scoped Classical BigOperators
namespace CMDRR

theorem count_as_sum {α : Type} [Fintype α] (p : α → Prop) [DecidablePred p] :
    count p = ∑ x : α, if p x then 1 else 0 := by
  classical
  simp only [count, Finset.sum_boole]
  congr 1
  ext x
  simp

namespace Source
variable {O : Type} [Fintype O] {d : Schedule (Fin 5) (Fin 5) O}
variable (h : Source canonical d)

include h in
theorem female_single_weighted :
    (∑ o : O, if (d.game o).Women 3 4 then
      count (fun m : Fin 5 => m.val < 3 ∧ ∃ w, (d.game o).Partners m w) else 0) +
    z d = 2 + A d := by
  classical
  have he : ∀ o : O,
      (if (d.game o).Women 3 4 then
        count (fun m : Fin 5 => m.val < 3 ∧ ∃ w, (d.game o).Partners m w) else 0) +
      (if (d.game o).Men 3 4 ∧ (d.game o).Women 3 4 then 1 else 0) =
      (if (d.game o).Women 3 4 then 1 else 0) +
      (if (d.game o).Women 3 4 ∧
        ∃ m n : Fin 5, m.val < 3 ∧ n.val < 3 ∧ (d.game o).Men m n then 1 else 0) := by
    intro o
    by_cases hw : (d.game o).Women 3 4
    · simpa only [hw,ite_true,and_true,true_and] using (d.game o).spouse_man_incidence
    · simp [hw]
  have hs := congrArg (fun f : O → ℕ => ∑ o, f o) (funext he)
  simp only [Finset.sum_add_distrib] at hs
  have hz := count_as_sum (fun o => (d.game o).Men 3 4 ∧ (d.game o).Women 3 4)
  have ha := count_as_sum (fun o => (d.game o).Women 3 4 ∧
    ∃ m n : Fin 5, m.val < 3 ∧ n.val < 3 ∧ (d.game o).Men m n)
  have hw := count_as_sum (fun o => (d.game o).Women 3 4)
  change z d = _ at hz
  change A d = _ at ha
  rw [← hz,← ha,← hw,h.canonical_women_repeat] at hs
  exact hs

/-- Fubini counts spouse-man incidences, without dividing unordered games. -/
theorem spouse_incidence_fubini (P : O → Prop) [DecidablePred P] :
    (∑ m : Fin 5, if m.val < 3 then
      count (fun o => (∃ w, (d.game o).Partners m w) ∧ P o) else 0) =
    ∑ o : O, if P o then
      count (fun m : Fin 5 => m.val < 3 ∧ ∃ w, (d.game o).Partners m w) else 0 := by
  classical
  simp only [count_as_sum]
  have hl : ∀ m : Fin 5, (if m.val < 3 then
      ∑ o : O, if (∃ w, (d.game o).Partners m w) ∧ P o then 1 else 0 else 0) =
      ∑ o : O, if m.val < 3 ∧ (∃ w, (d.game o).Partners m w) ∧ P o then 1 else 0 := by
    intro m
    by_cases hm : m.val < 3 <;> simp [hm]
  simp only [hl]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  by_cases hp : P o <;> simp [hp]
end Source
end CMDRR
