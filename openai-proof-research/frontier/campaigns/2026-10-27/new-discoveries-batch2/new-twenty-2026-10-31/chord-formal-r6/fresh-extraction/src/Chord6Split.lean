import Chord6Swap
namespace Chord.Round6
open Equiv Model3 Model4

private theorem sameCycle_closed {α : Type*} [Finite α] (f : Perm α)
    (P : α → Prop) (step : ∀ x, P x → P (f x)) {a b : α}
    (ha : P a) (h : Perm.SameCycle f a b) : P b := by
  obtain ⟨k,rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction k with
  | zero => exact ha
  | succ k ih => rw [pow_succ', Perm.mul_apply]; exact step _ ih

/-- The innermost monochromatic chord cuts off an explicit closed face.
Its two band sides therefore lie in different face cycles. -/
theorem innermost_distinct {n} (D : Diagram (n+1)) (c : Sides (n+1))
    (a : Fin (2*(n+1))) (ha : a < D.partner a)
    (hc : c (D.partner a) = c a)
    (hi : ∀ i, a < i → i < D.partner a → c i ≠ c a) :
    ¬Perm.SameCycle (Model2.faceEquiv D c) (chordDart a) (chordDart (D.partner a)) := by
  let b := D.partner a
  have hab : a.val < b.val := ha
  have hb := b.isLt
  have ha' := a.isLt
  have hcb : c b = c a := hc
  have hface (x : Fin (6*(n+1))) : (Model2.faceEquiv D c x).val = face D c x.val := rfl
  cases hca : c a with
  | false =>
    let P : Fin (6*(n+1)) → Prop := fun x =>
      x = chordDart a ∨ (x.val % 3 = 0 ∧ a.val < x.val / 3 ∧ x.val / 3 ≤ b.val)
    have step : ∀ x, P x → P (Model2.faceEquiv D c x) := by
      intro x hx
      rcases hx with rfl | ⟨hr, hlo, hhi⟩
      · right
        have hval : (Model2.faceEquiv D c (chordDart a)).val = 3*b.val := by
          change rho c (theta D (chordDart a).val) = _
          rw [theta_chordDart]
          change rho c (3*b.val+2) = 3*b.val
          simp only [rho, show (3*b.val+2)/3 = b.val by omega, show (3*b.val+2)%3 = 2 by omega]
          simp [side, b.isLt, hcb, hca]
        change _ % 3 = 0 ∧ a.val < _ / 3 ∧ _ / 3 ≤ b.val
        rw [hval]; omega
      · let i : Fin (2*(n+1)) := ⟨x.val/3-1, by omega⟩
        have hiv : a.val ≤ i.val := by dsimp [i]; omega
        have hil : i.val < b.val := by dsimp [i]; omega
        have hv : theta D x.val = 3*i.val+1 := by
          simp only [theta, hr]
          rw [show x.val/3+2*(n+1)-1 = (x.val/3-1)+2*(n+1) by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
        by_cases he : i = a
        · left
          apply Fin.ext
          rw [hface]
          unfold face
          rw [hv, he]
          simp only [rho]
          rw [show (3*a.val+1)/3 = a.val by omega, show (3*a.val+1)%3 = 1 by omega]
          simp [side, a.isLt, hca, chordDart]
        · have hci : c i = true := by
            have hh := hi i (by change a.val < i.val; exact lt_of_le_of_ne hiv (fun hh => he (Fin.ext hh.symm)))
              (by exact hil)
            cases hh' : c i <;> simp_all
          right
          have hv' : (Model2.faceEquiv D c x).val = 3*i.val := by
            rw [hface]; unfold face; rw [hv]
            simp only [rho]
            rw [show (3*i.val+1)/3 = i.val by omega, show (3*i.val+1)%3 = 1 by omega]
            simp [side, i.isLt, hci]
          change _ % 3 = 0 ∧ a.val < _ / 3 ∧ _ / 3 ≤ b.val
          rw [hv']
          have hne : i.val ≠ a.val := fun hh => he (Fin.ext hh)
          omega
    intro hs
    have hp := sameCycle_closed _ P step (Or.inl rfl) hs
    rcases hp with hh | ⟨hh,_,_⟩
    · have he := congrArg Fin.val hh
      simp only [chordDart] at he
      omega
    · simp only [chordDart] at hh
      omega
  | true =>
    let P : Fin (6*(n+1)) → Prop := fun x =>
      x = chordDart b ∨ (x.val % 3 = 1 ∧ a.val ≤ x.val / 3 ∧ x.val / 3 < b.val)
    have step : ∀ x, P x → P (Model2.faceEquiv D c x) := by
      intro x hx
      rcases hx with rfl | ⟨hr,hlo,hhi⟩
      · right
        have hval : (Model2.faceEquiv D c (chordDart b)).val = 3*a.val+1 := by
          change rho c (theta D (chordDart b).val) = _
          rw [theta_chordDart]
          have he : D.partner b = a := D.involutive a
          rw [he]
          simp only [chordDart, rho, show (3*a.val+2)/3 = a.val by omega, show (3*a.val+2)%3 = 2 by omega]
          simp [side, a.isLt, hca]
        change _ % 3 = 1 ∧ a.val ≤ _ / 3 ∧ _ / 3 < b.val
        rw [hval]; omega
      · let i : Fin (2*(n+1)) := ⟨x.val/3+1, by omega⟩
        have hiv : a.val < i.val := by dsimp [i]; omega
        have hil : i.val ≤ b.val := by dsimp [i]; omega
        have hv : theta D x.val = 3*i.val := by
          simp only [theta, hr]
          rw [Nat.mod_eq_of_lt i.isLt]
        by_cases he : i = b
        · left
          apply Fin.ext
          rw [hface]
          unfold face
          rw [hv, he]
          simp only [rho]
          rw [show (3*b.val)/3 = b.val by omega, show (3*b.val)%3 = 0 by omega]
          simp [side, b.isLt, hcb, hca, chordDart]
        · have hci : c i = false := by
            have hh := hi i hiv (by change i.val < b.val; exact lt_of_le_of_ne hil (fun hh => he (Fin.ext hh)))
            cases hh' : c i <;> simp_all
          right
          have hv' : (Model2.faceEquiv D c x).val = 3*i.val+1 := by
            rw [hface]; unfold face; rw [hv]
            simp only [rho]
            rw [show (3*i.val)/3 = i.val by omega, show (3*i.val)%3 = 0 by omega]
            simp [side, i.isLt, hci]
          change _ % 3 = 1 ∧ a.val ≤ _ / 3 ∧ _ / 3 < b.val
          rw [hv']
          have hne : i.val ≠ b.val := fun hh => he (Fin.ext hh)
          omega
    intro hs
    have hp := sameCycle_closed _ P step (Or.inl rfl) hs.symm
    rcases hp with hh | ⟨hh,_,_⟩
    · have he := congrArg Fin.val hh
      simp only [chordDart] at he
      omega
    · simp only [chordDart] at hh
      omega

/-- The refined planarity deletion follows from band erasure alone. -/
theorem monochromaticSplit_of_bandErasure (erase : BandErasure) : Comb4.MonochromaticSplit := by
  intro n D c a ha hc hi
  let S := Comb4.removeChordSubdiagram D a
  have hp : ∀ i, S.positions i ≠ a := by
    intro i
    have hh := (Comb4.keptAfter D a).orderIsoOfFin (Comb4.keptAfter_card D a) i |>.property
    change S.positions i ∈ Comb4.keptAfter D a at hh
    have hnot : S.positions i ≠ a ∧ S.positions i ≠ D.partner a := by
      simpa only [Comb4.keptAfter, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
        Finset.mem_singleton, true_and, not_or] using hh
    exact hnot.1
  have he := Round5.bandErasure_iff_every.mp erase n D _ S c a hp
  have hne : chordDart a ≠ chordDart (D.partner a) := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [chordDart] at hv
    have hv' : a.val = (D.partner a).val := by omega
    exact D.noFixed a (Fin.ext hv'.symm)
  have hs := (swap_orbitCount_refined _ (Model2.faceEquiv D c) _ _ hne).2
    (innermost_distinct D c a ha (hc a) hi)
  rw [he, ← boundary_eq_orbitCount (by omega : n+1 ≠ 0) D c] at hs
  exact hs.symm

#print axioms innermost_distinct
#print axioms monochromaticSplit_of_bandErasure
end Chord.Round6
