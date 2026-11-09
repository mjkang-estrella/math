import ChordComb4FiveSelection
namespace Chord.Comb4

/-- Every nonempty side of a bipartite assignment has an innermost chord:
no endpoint of that side lies strictly between its ends. This is the
combinatorial choice needed for the face-splitting planarity induction. -/
theorem innermost_monochromatic {n} (D : Diagram n) (color : Sides n)
    (hc : ∀ i, color (D.partner i) = color i)
    (hx : ∀ a b, Crosses D a b → color a ≠ color b)
    (b : Bool) (hex : ∃ a, a < D.partner a ∧ color a = b) :
    ∃ a, a < D.partner a ∧ color a = b ∧
      ∀ i, a < i → i < D.partner a → color i ≠ b := by
  classical
  let P : Nat → Prop := fun d => ∃ a, a < D.partner a ∧ color a = b ∧
    (D.partner a).val - a.val = d
  have hP : ∃ d, P d := by
    obtain ⟨a,ha,hb⟩ := hex
    exact ⟨_,a,ha,hb,rfl⟩
  obtain ⟨a,ha,hb,hd⟩ := Nat.find_spec hP
  refine ⟨a,ha,hb,?_⟩
  intro i hai hia hi
  have hp := D.noFixed i
  have hcl : color (D.partner i) = b := (hc i).trans hi
  have hav := ha
  have haiv := hai
  have hiav := hia
  change a.val < (D.partner a).val at hav
  change a.val < i.val at haiv
  change i.val < (D.partner a).val at hiav
  by_cases hleft : D.partner i < a
  · have hcross : Crosses D (D.partner i) a := by
      refine ⟨?_,ha,Or.inl ?_⟩
      · rw [D.involutive]; exact lt_trans hleft hai
      · rw [D.involutive]; exact ⟨hleft,hai,hia⟩
    exact hx _ _ hcross (hcl.trans hb.symm)
  have hleft' : D.partner i ≠ a := by
    intro he
    have := congrArg D.partner he
    rw [D.involutive] at this
    exact (ne_of_lt hia) this
  by_cases hright : D.partner a < D.partner i
  · have hcross : Crosses D a i :=
      ⟨ha,lt_trans hia hright,Or.inl ⟨hai,hia,hright⟩⟩
    exact hx _ _ hcross (hb.trans hi.symm)
  have hright' : D.partner i ≠ D.partner a := by
    intro he
    have := congrArg D.partner he
    simp only [D.involutive] at this
    exact (ne_of_lt hai) this.symm
  have hlow : a.val < (D.partner i).val := by
    change ¬ (D.partner i).val < a.val at hleft
    have hh : (D.partner i).val ≠ a.val := fun h => hleft' (Fin.ext h)
    omega
  have hupp : (D.partner i).val < (D.partner a).val := by
    change ¬ (D.partner a).val < (D.partner i).val at hright
    have hh : (D.partner i).val ≠ (D.partner a).val := fun h => hright' (Fin.ext h)
    omega
  by_cases hil : i < D.partner i
  · have hmin := Nat.find_min' hP (show P ((D.partner i).val-i.val) from ⟨i,hil,hi,rfl⟩)
    omega
  · have hil' : D.partner i < i := lt_of_le_of_ne (le_of_not_gt hil) hp
    have hmin := Nat.find_min' hP (show P (i.val-(D.partner i).val) from by
      refine ⟨D.partner i,?_,hcl,?_⟩
      · rw [D.involutive]; exact hil'
      · rw [D.involutive])
    omega
end Chord.Comb4
