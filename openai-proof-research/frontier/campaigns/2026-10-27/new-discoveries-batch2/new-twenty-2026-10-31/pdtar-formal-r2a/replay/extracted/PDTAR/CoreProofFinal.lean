import PDTAR.CoreProofComplete
namespace PDTAR
open Finset

/-- The full Core remainder, including the swapped large-side case. -/
theorem core_remaining_proved : CoreRemaining := by
  intro V _ _ K H A B hk ha hb hn he
  have hA := fun p hp => core_cross_two hk he ha hb hn (a := p) hp
  have hB := fun p hp => core_cross_two (completeBetween_swap hk) he hb ha
    (hn.elim (fun h => Or.inr h) (fun h => Or.inl h)) (a := p) hp
  apply core_eq_of_cross_complete hk he ha hb
  by_cases hb4 : 4 ≤ B.card
  · exact core_complete_large hk he ha hb4 hA hB
  · have ha4 : 4 ≤ A.card := by omega
    have hc := core_complete_large (completeBetween_swap hk) he hb ha4 hB hA
    exact fun a ha b hb => (hc b hb a ha).symm
end PDTAR
