import ComplementBlocks
set_option linter.unusedSectionVars false
namespace XorMagic
variable {V : Type} [Fintype V] [LinearOrder V] {G : SimpleGraph V} {d : ℕ}
namespace EdgeTransport
variable (T : EdgeTransport G) (F : MatchingDecomposition G d)
/-- Lower endpoints use the identity chart; upper endpoints use inverse transport. -/
def matchingChart (i : Fin d) (v : V) : Four ≃ Four :=
  if v < F.mate i v then Equiv.refl _ else (T.map (F.mate i v) v).symm

theorem matchingChart_transport (i : Fin d) (v : V) (x : Four) :
    (T.matchingChart F i (F.mate i v)).symm (T.matchingChart F i v x) =
      T.map v (F.mate i v) x := by
  have ha : G.Adj v (F.mate i v) := (F.cover _ _).mpr ⟨i,rfl⟩
  have hn := F.no_fixed i v
  by_cases h : v < F.mate i v
  · simp [matchingChart, F.involutive, h, not_lt_of_gt h]
  · have hh : F.mate i v < v := lt_of_le_of_ne (le_of_not_gt h) hn
    have he : T.map (F.mate i v) v = (T.map v (F.mate i v)).symm := by
      apply Equiv.ext
      intro y
      apply (T.map v (F.mate i v)).injective
      simp only [Equiv.apply_symm_apply]
      exact T.reverse ha.symm y
    simp [matchingChart, F.involutive, h, hh, he]

theorem blockMate_zero (i : Fin d) (p : V × Four) :
    blockMate F (T.matchingChart F) i 0 p =
      (F.mate i p.1, T.map p.1 (F.mate i p.1) p.2) := by
  simp [blockMate, T.matchingChart_transport]

theorem blockMate_nonzero_cover (p q : V × Four) :
    (G.Adj p.1 q.1 ∧ T.map p.1 q.1 p.2 ≠ q.2) ↔
    ∃ ia : Fin d × NonzeroFour, blockMate F (T.matchingChart F) ia.1 ia.2.1 p = q := by
  constructor
  · rintro ⟨ha,hn⟩
    obtain ⟨i,hi⟩ := (F.cover _ _).mp ha
    let a := T.matchingChart F i q.1 q.2 - T.matchingChart F i p.1 p.2
    have hzero : a ≠ 0 := by
      intro hz
      have he := sub_eq_zero.mp hz
      apply hn
      rw [← hi]
      rw [← T.matchingChart_transport F i p.1 p.2]
      rw [← he, hi, Equiv.symm_apply_apply]
    refine ⟨(i,⟨a,hzero⟩), Prod.ext hi ?_⟩
    change (T.matchingChart F i (F.mate i p.1)).symm (_ + a) = q.2
    rw [hi]
    simp [a]
  · rintro ⟨⟨i,a⟩,he⟩
    have hv : F.mate i p.1 = q.1 := congrArg Prod.fst he
    refine ⟨(F.cover _ _).mpr ⟨i,hv⟩, ?_⟩
    intro hx
    have hz : blockMate F (T.matchingChart F) i 0 p = q := by
      rw [T.blockMate_zero F]
      exact Prod.ext hv (by simpa only [hv] using hx)
    have heq : (i,a.1) = (i,0) := blockMate_distinct F (T.matchingChart F) p (he.trans hz.symm)
    exact a.2 (congrArg Prod.snd heq)
end EdgeTransport
end XorMagic
