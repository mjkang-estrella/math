import PDTAR.Final
open PDTAR
example : IsPD (small_two_added 3) {Sum.inr 0} := by
  rw [small_two_family 3 (by omega) _ (by intros; trivial) (by intros; exact id)]
  simp only [Finset.singleton_nonempty, Finset.mem_singleton, Sum.inl_ne_inr,
    exists_false, false_or, true_and]
  have hbad : ¬ (∀ b c : Fin 3, Sum.inr b ∉ ({Sum.inr 0} : Finset (Fin 2 ⊕ Fin 3)) →
      Sum.inr c ∉ ({Sum.inr 0} : Finset (Fin 2 ⊕ Fin 3)) → b = c) := by
    intro h
    have he := h 1 2 (by simp) (by simp)
    omega
  simp_all
