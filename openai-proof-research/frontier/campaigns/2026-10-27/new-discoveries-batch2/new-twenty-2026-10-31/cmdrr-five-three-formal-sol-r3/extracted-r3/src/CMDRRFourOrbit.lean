import CMDRRCycles

namespace CMDRR
/-- Structural four-point orbit lemma. There is no enumeration of permutations:
injectivity and the absence of fixed points force the remaining image. -/
theorem four_orbit {α : Type} (p : Equiv.Perm α) (x a b c : α)
    (hxb : x ≠ b) (hxc : x ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (cover : ∀ y, y = x ∨ y = a ∨ y = b ∨ y = c)
    (derange : ∀ y, p y ≠ y) (hpx : p x = a)
    (noTwo : p a ≠ x) :
    (p a = b ∧ p b = c ∧ p c = x) ∨
    (p a = c ∧ p c = b ∧ p b = x) := by
  have pa_ne_a := derange a
  have pa_options : p a = b ∨ p a = c := by
    rcases cover (p a) with h | h | h | h
    · exact (noTwo h).elim
    · exact (pa_ne_a h).elim
    · exact Or.inl h
    · exact Or.inr h
  have pb_ne_a : p b ≠ a := by
    intro he
    exact hxb (p.injective (hpx.trans he.symm))
  have pc_ne_a : p c ≠ a := by
    intro he
    exact hxc (p.injective (hpx.trans he.symm))
  rcases pa_options with hpab | hpac
  · have pc_ne_b : p c ≠ b := by
      intro he
      exact hac (p.injective (hpab.trans he.symm))
    have hpc : p c = x := by
      rcases cover (p c) with h | h | h | h
      · exact h
      · exact (pc_ne_a h).elim
      · exact (pc_ne_b h).elim
      · exact (derange c h).elim
    have hpb : p b = c := by
      rcases cover (p b) with h | h | h | h
      · exact (hbc (p.injective (h.trans hpc.symm))).elim
      · exact (pb_ne_a h).elim
      · exact (derange b h).elim
      · exact h
    exact Or.inl ⟨hpab,hpb,hpc⟩
  · have pb_ne_c : p b ≠ c := by
      intro he
      exact hab (p.injective (hpac.trans he.symm))
    have hpb : p b = x := by
      rcases cover (p b) with h | h | h | h
      · exact h
      · exact (pb_ne_a h).elim
      · exact (derange b h).elim
      · exact (pb_ne_c h).elim
    have hpc : p c = b := by
      rcases cover (p c) with h | h | h | h
      · exact (hbc (p.injective (hpb.trans h.symm))).elim
      · exact (pc_ne_a h).elim
      · exact h
      · exact (derange c h).elim
    exact Or.inr ⟨hpac,hpc,hpb⟩
end CMDRR
