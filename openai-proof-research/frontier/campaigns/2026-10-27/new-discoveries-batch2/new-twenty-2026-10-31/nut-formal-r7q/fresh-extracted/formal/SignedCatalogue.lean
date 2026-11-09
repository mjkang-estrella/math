import SignedEnumeration
import CatalogueTrees
namespace Nut8

def signedCatalogue (code : Nat) (e : Equiv.Perm (Fin 8))
    (p : Fin 8 → Fin 8) : Finset QuotientMatrix :=
  (unsignedPatterns code).biUnion fun U => signedPatterns (U.submatrix e e) p

/-- Completeness in the exact permutation and tree supplied by the caller. -/
theorem signedCatalogue_complete (code : Nat) (C : QuotientMatrix) (s : ℤ)
    (h : Structural C s) (hc : SupportCode C code)
    (e : Equiv.Perm (Fin 8)) (p : Fin 8 → Fin 8)
    (hp : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧
      graphBit 8 code (e (p i)).val (e i).val = true) :
    ∃ d : Fin 8 → ℤ, (∀ i, d i = 1 ∨ d i = -1) ∧
      switch d (C.submatrix e e) ∈ signedCatalogue code e p := by
  obtain ⟨d,hd,hn⟩ := ordered_switch_exists (C.submatrix e e) p (fun i hi => (hp i hi).1)
  refine ⟨d,hd,Finset.mem_biUnion.mpr ⟨unsignedQuotient C,
    unsignedPatterns_complete C s code h hc, ?_⟩⟩
  have hu : (unsignedQuotient C).submatrix e e =
      unsignedQuotient (switch d (C.submatrix e e)) := by
    funext i j
    exact (switch_abs d hd (C.submatrix e e) i j).symm
  rw [hu]
  apply signedPatterns_complete _ s (structural_switch d hd _ s
    (admissible_relabel e C (-1) s h))
  intro i hi
  refine ⟨(hp i hi).1, ?_⟩
  rw [hn i hi]
  apply abs_pos.mpr
  exact (hc _ _ (e.injective.ne (by
    intro he
    have := congrArg Fin.val he
    have := (hp i hi).1
    omega))).mpr (hp i hi).2

/-- Every catalogue support has an exactly enumerated switched representative. -/
theorem catalogue_signed_normalization (code : Nat)
    (hc : code ∈ GraphClosure7_000.targets) :
    ∃ (e : Equiv.Perm (Fin 8)) (p : Fin 8 → Fin 8),
      ∀ (C : QuotientMatrix) (s : ℤ), Structural C s → SupportCode C code →
        ∃ d : Fin 8 → ℤ, (∀ i, d i = 1 ∨ d i = -1) ∧
          switch d (C.submatrix e e) ∈ signedCatalogue code e p := by
  obtain ⟨e,p,hp⟩ := catalogue_ordered_tree code hc
  exact ⟨e,p,fun C s h hs => signedCatalogue_complete code C s h hs e p hp⟩

/-- The precise remaining finite obligation suffices for the root-fixed endpoint. -/
theorem per_support_of_signed_catalogues
    (certificates : ∀ code ∈ GraphClosure7_000.targets,
      ∃ (e : Equiv.Perm (Fin 8)) (p : Fin 8 → Fin 8),
        (∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧
          graphBit 8 code (e (p i)).val (e i).val = true) ∧
        ∀ A ∈ signedCatalogue code e p,
          ¬ (A.det = 0 ∧ ∀ i, A.adjugate i i ≠ 0)) : PerSupport := by
  intro code hc C s h hs
  obtain ⟨e,p,hp,hcert⟩ := certificates code hc
  obtain ⟨d,hd,hm⟩ := signedCatalogue_complete code C s h hs e p hp
  exact obstruction_of_relabel e C
    (obstruction_of_switch d hd _ (hcert _ hm))
end Nut8
