import CrownVFamCutB

/-!
Shape finalizers for the converse classification: each turns an explicit
description of `T` into a valid family whose cut is exactly `T`.
-/

namespace CrownV

variable {n : ℕ}

/-- `T` = the full X side gives `fullX`. -/
theorem famEq_fullX {T : Finset (V n)} (hX : ∀ l : Fin n, Sum.inl l ∈ T)
    (hY : ∀ l : Fin n, Sum.inr l ∉ T) :
    ∃ f : Fam n, FamValid n f ∧ famCut n f = T := by
  refine ⟨.fullX, trivial, ?_⟩
  rw [famCut_fullX]
  ext v
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := inl_of_isX (mem_Xside.1 h)
    exact hX k
  · intro h
    cases v with
    | inl l => exact mem_Xside.2 isX_inl
    | inr l => exact absurd h (hY l)

/-- `T` = the X side minus `a k` gives `delX k`. -/
theorem famEq_delX {T : Finset (V n)} {k : Fin n}
    (hX : ∀ l : Fin n, Sum.inl l ∈ T ↔ l ≠ k) (hY : ∀ l : Fin n, Sum.inr l ∉ T) :
    ∃ f : Fam n, FamValid n f ∧ famCut n f = T := by
  refine ⟨.delX k, trivial, ?_⟩
  rw [famCut_delX]
  ext v
  constructor
  · intro h
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.1 h
    cases v with
    | inl l => exact (hX l).2 (fun e => hne (congrArg Sum.inl e))
    | inr l =>
      rw [mem_Xside, isX_inr] at hmem
      exact absurd hmem (by decide)
  · intro h
    refine Finset.mem_erase.2 ⟨?_, ?_⟩
    · cases v with
      | inl l => exact fun e => (hX l).1 h (Sum.inl.inj e)
      | inr l => exact fun e => inl_ne_inr e.symm
    · cases v with
      | inl l => exact mem_Xside.2 isX_inl
      | inr l => exact absurd h (hY l)

/-- `T` = the full Y side gives `fullY`. -/
theorem famEq_fullY {T : Finset (V n)} (hY : ∀ l : Fin n, Sum.inr l ∈ T)
    (hX : ∀ l : Fin n, Sum.inl l ∉ T) :
    ∃ f : Fam n, FamValid n f ∧ famCut n f = T := by
  refine ⟨.fullY, trivial, ?_⟩
  rw [famCut_fullY]
  ext v
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := inr_of_sideY (mem_Yside.1 h)
    exact hY k
  · intro h
    cases v with
    | inr l => exact mem_Yside.2 isX_inr
    | inl l => exact absurd h (hX l)

/-- `T` = the Y side minus `b k` gives `delY k`. -/
theorem famEq_delY {T : Finset (V n)} {k : Fin n}
    (hY : ∀ l : Fin n, Sum.inr l ∈ T ↔ l ≠ k) (hX : ∀ l : Fin n, Sum.inl l ∉ T) :
    ∃ f : Fam n, FamValid n f ∧ famCut n f = T := by
  refine ⟨.delY k, trivial, ?_⟩
  rw [famCut_delY]
  ext v
  constructor
  · intro h
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.1 h
    cases v with
    | inr l => exact (hY l).2 (fun e => hne (congrArg Sum.inr e))
    | inl l =>
      rw [mem_Yside, isX_inl] at hmem
      exact absurd hmem (by decide)
  · intro h
    refine Finset.mem_erase.2 ⟨?_, ?_⟩
    · cases v with
      | inr l => exact fun e => (hY l).1 h (Sum.inr.inj e)
      | inl l => exact fun e => inl_ne_inr e
    · cases v with
      | inr l => exact mem_Yside.2 isX_inr
      | inl l => exact absurd h (hX l)

/-- `T` = everything outside the four survivors `a u, a v, b u, b v` (`u ≠ v`)
gives `mix u v`; the hypotheses describe exactly the `univ \ T`-members. -/
theorem famEq_mixed {T : Finset (V n)} {u v : Fin n} (huv : u ≠ v)
    (hX : ∀ l : Fin n, Sum.inl l ∈ Finset.univ \ T ↔ l = u ∨ l = v)
    (hY : ∀ l : Fin n, Sum.inr l ∈ Finset.univ \ T ↔ l = u ∨ l = v) :
    ∃ f : Fam n, FamValid n f ∧ famCut n f = T := by
  refine ⟨.mix u v, huv, ?_⟩
  rw [famCut_mix]
  ext w
  constructor
  · intro h
    have hnm : w ∉ mixKeep u v := (Finset.mem_sdiff.1 h).2
    by_contra hT
    have hD : w ∈ Finset.univ \ T := mem_sdiff_univ_of_notMem hT
    cases w with
    | inl l => exact hnm (inl_mixKeep_mem ((hX l).1 hD))
    | inr l => exact hnm (inr_mixKeep_mem ((hY l).1 hD))
  · intro h
    refine Finset.mem_sdiff.2 ⟨Finset.mem_univ w, ?_⟩
    intro hm
    cases w with
    | inl l =>
      have hdu : l = u ∨ l = v := by
        rcases Finset.mem_insert.1 hm with e | e
        · exact Or.inl (Sum.inl.inj e)
        · rcases Finset.mem_insert.1 e with e | e
          · exact Or.inr (Sum.inl.inj e)
          · rcases Finset.mem_insert.1 e with e | e
            · exact absurd e (inl_ne_inr)
            · rcases Finset.mem_insert.1 e with e | e
              · exact absurd e (inl_ne_inr)
              · exact absurd e (Finset.notMem_empty _)
      have hD : Sum.inl l ∈ Finset.univ \ T := (hX l).2 hdu
      exact (Finset.mem_sdiff.1 hD).2 h
    | inr l =>
      have hdu : l = u ∨ l = v := by
        rcases Finset.mem_insert.1 hm with e | e
        · exact absurd e.symm (inl_ne_inr)
        · rcases Finset.mem_insert.1 e with e | e
          · exact absurd e.symm (inl_ne_inr)
          · rcases Finset.mem_insert.1 e with e | e
            · exact Or.inl (Sum.inr.inj e)
            · rcases Finset.mem_insert.1 e with e | e
              · exact Or.inr (Sum.inr.inj e)
              · exact absurd e (Finset.notMem_empty _)
      have hD : Sum.inr l ∈ Finset.univ \ T := (hY l).2 hdu
      exact (Finset.mem_sdiff.1 hD).2 h

end CrownV
