import FamilyRows
set_option autoImplicit false
namespace Polyomino57
-- Uses the existing seven-cell coverage and existing family growth step.
theorem coverage_after_seven (F : ℕ → List GridPoint → Prop)
    (base : ∀ row ∈ layer7.toList, F 7 row)
    (steps : ∀ n, 7 ≤ n → n < 11 → ∀ row, F n row → FamilyRowClosed (F (n+1)) row)
    {P : Finset GridPoint} (hg : Grown P) (hlo : 7 ≤ P.card) (hhi : P.card ≤ 11) :
    ∃ row, F P.card row ∧ ∃ hr : row.toFinset.Nonempty,
      normalize P (growth_sound hg).1 = normalize row.toFinset hr := by
  induction hg with
  | singleton p => simp at hlo
  | @insert Q a b hg ha hb hab ih =>
    by_cases hc : (insert b Q).card = 7
    · obtain ⟨row,hm,hr,he⟩ := seven_normalized_coverage (insert b Q)
        (growth_sound (.insert hg ha hb hab)) hc
      rw [hc]
      exact ⟨row,base row hm,hr,he⟩
    · have hcard := Finset.card_insert_of_notMem hb
      obtain ⟨row,hm,hr,he⟩ := ih (by omega) (by omega)
      obtain ⟨S,hS,hSne,hEq⟩ := family_growth_step (F (Q.card+1)) Q
        (growth_sound hg).1 row hr he (steps Q.card (by omega) (by omega) row hm) ha hb hab
      rw [hcard]
      exact ⟨S,hS,hSne,hEq⟩
end Polyomino57
