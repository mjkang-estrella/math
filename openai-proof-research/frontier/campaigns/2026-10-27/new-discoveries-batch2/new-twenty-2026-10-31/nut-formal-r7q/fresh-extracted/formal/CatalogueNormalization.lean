import CatalogueTrees
import OrderedSwitch
namespace Nut8

/-- A structural matrix on any catalogue support admits an ordered, positive
spanning parent tree after permutation and sign switching. -/
theorem catalogue_normalization (code : Nat) (hc : code ∈ GraphClosure7_000.targets)
    (C : QuotientMatrix) (s : ℤ) (h : Structural C s) (hs : SupportCode C code) :
    ∃ (e : Equiv.Perm (Fin 8)) (d : Fin 8 → ℤ) (p : Fin 8 → Fin 8),
      (∀ i, d i = 1 ∨ d i = -1) ∧
      Structural (switch d (C.submatrix e e)) s ∧
      ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧
        0 < switch d (C.submatrix e e) (p i) i := by
  obtain ⟨e,p,hp⟩ := catalogue_ordered_tree code hc
  obtain ⟨d,hd,hn⟩ := ordered_switch_exists (C.submatrix e e) p (fun i hi => (hp i hi).1)
  refine ⟨e,d,p,hd,structural_switch d hd _ s (admissible_relabel e C (-1) s h), ?_⟩
  intro i hi
  refine ⟨(hp i hi).1, ?_⟩
  rw [hn i hi]
  apply abs_pos.mpr
  apply (hs _ _ ?_).mpr (hp i hi).2
  apply e.injective.ne
  intro he
  have he' := congrArg Fin.val he
  have ht := (hp i hi).1
  omega
end Nut8
