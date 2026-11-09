import LiftGraph
namespace XorMagic
abbrev NonzeroFour := {a : Four // a ≠ 0}
theorem four_add_self (a : Four) : a + a = 0 := by revert a; decide
theorem nonzeroFour_card : Fintype.card NonzeroFour = 3 := by decide

def fibreMatching (V : Type) (a : NonzeroFour) (p : V × Four) : V × Four :=
  (p.1, p.2 + a.1)
theorem fibreMatching_involutive (V : Type) (a : NonzeroFour) :
    Function.Involutive (fibreMatching V a) := by
  intro p; simp [fibreMatching, add_assoc, four_add_self]
theorem fibreMatching_no_fixed (V : Type) (a : NonzeroFour)
    (p : V × Four) : fibreMatching V a p ≠ p := by
  intro h
  have h' : p.2 + a.1 = p.2 + 0 := by simpa [fibreMatching] using congrArg Prod.snd h
  exact a.2 (add_left_cancel h')
theorem fibreMatching_distinct (V : Type) (p : V × Four) :
    Function.Injective (fun a : NonzeroFour => fibreMatching V a p) := by
  intro a b h
  apply Subtype.ext
  exact add_left_cancel (congrArg Prod.snd h)
theorem fibreMatching_cover {V : Type} (p q : V × Four) :
    (p.1 = q.1 ∧ p.2 ≠ q.2) ↔ ∃ a : NonzeroFour, fibreMatching V a p = q := by
  constructor
  · rintro ⟨h,h'⟩
    exact ⟨⟨q.2-p.2, sub_ne_zero.mpr (Ne.symm h')⟩, Prod.ext h (by simp [fibreMatching])⟩
  · rintro ⟨a,h⟩
    change (p.1, p.2 + a.1) = q at h
    have hf : p.1 = q.1 := by simpa only using congrArg Prod.fst h
    refine ⟨hf, ?_⟩
    intro he
    exact fibreMatching_no_fixed V a p (h.trans (Prod.ext hf.symm he.symm))

/-- Translating in endpoint charts gives all four matchings of a full block. -/
def blockMate {V : Type} {d : ℕ} {G : SimpleGraph V} [Fintype V]
    (F : MatchingDecomposition G d) (C : Fin d → V → Four ≃ Four)
    (i : Fin d) (a : Four) (p : V × Four) : V × Four :=
  (F.mate i p.1, (C i (F.mate i p.1)).symm (C i p.1 p.2 + a))
theorem blockMate_involutive {V : Type} {d : ℕ} {G : SimpleGraph V} [Fintype V]
    (F : MatchingDecomposition G d) (C : Fin d → V → Four ≃ Four)
    (i : Fin d) (a : Four) : Function.Involutive (blockMate F C i a) := by
  intro p
  apply Prod.ext
  · exact F.involutive i p.1
  · simp [blockMate, F.involutive, add_assoc, four_add_self]
theorem blockMate_no_fixed {V : Type} {d : ℕ} {G : SimpleGraph V} [Fintype V]
    (F : MatchingDecomposition G d) (C : Fin d → V → Four ≃ Four)
    (i : Fin d) (a : Four) (p : V × Four) : blockMate F C i a p ≠ p := by
  intro h
  exact F.no_fixed i p.1 (congrArg Prod.fst h)
theorem blockMate_distinct {V : Type} {d : ℕ} {G : SimpleGraph V} [Fintype V]
    (F : MatchingDecomposition G d) (C : Fin d → V → Four ≃ Four)
    (p : V × Four) : Function.Injective (fun ia : Fin d × Four => blockMate F C ia.1 ia.2 p) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  have hij := F.distinct p.1 (congrArg Prod.fst h)
  change i = j at hij
  subst j
  refine Prod.ext rfl ?_
  apply add_left_cancel (a := C i p.1 p.2)
  exact (C i (F.mate i p.1)).symm.injective (congrArg Prod.snd h)
end XorMagic
