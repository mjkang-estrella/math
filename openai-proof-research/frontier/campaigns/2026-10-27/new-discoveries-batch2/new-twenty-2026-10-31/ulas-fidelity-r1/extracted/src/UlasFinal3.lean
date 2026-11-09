import UlasWeight

namespace Ulas.Round3
/-- All six mathematical obligations remain explicit and uninhabited here. -/
def Remaining : Prop := Ulas.Remaining

/-- The literal refutation needs only the universal fifteen-family bound. -/
theorem mathdb_of_fifteen (h : FifteenBound) : ¬ Conj61 := by
  intro hc
  obtain ⟨n, hn, _⟩ := (hc.2.2.2.2.2 3).exists_gt 0
  exact never_fifteen h 0 n hn.1 (by simpa [oddEq] using hn.2)

/-- CONDITIONAL full theorem. This file does not assert Remaining. -/
theorem full_theorem (h : Remaining) :
    EvenFormula ∧ OddOneBound ∧ OddThreeBound ∧ OddOneEquality ∧
    OddThreeEquality ∧ FifteenBound ∧ NeverFifteen := Ulas.full_theorem h

/-- CONDITIONAL endpoint; not the requested unconditional theorem. -/
theorem mathdb_342364 (h : Remaining) : ¬ Conj61 := Ulas.mathdb_342364 h

/-- CONDITIONAL endpoint; not the requested unconditional theorem. -/
theorem conj61_some (h : Remaining) : Conj61Some := Ulas.conj61_some h
end Ulas.Round3
