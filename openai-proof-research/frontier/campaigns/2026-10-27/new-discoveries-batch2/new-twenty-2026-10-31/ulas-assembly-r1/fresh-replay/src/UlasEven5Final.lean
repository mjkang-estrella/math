import UlasEven5Invariant
namespace Ulas.Even5
/-- Exactly the five remaining odd obligations; the even formula is proved above. -/
def Remaining : Prop := OddOneBound ∧ OddThreeBound ∧ OddOneEquality ∧
  OddThreeEquality ∧ FifteenBound

theorem full_theorem (h : Remaining) :
    EvenFormula ∧ OddOneBound ∧ OddThreeBound ∧ OddOneEquality ∧
    OddThreeEquality ∧ FifteenBound ∧ NeverFifteen :=
  Ulas.full_theorem ⟨evenFormula_proved,h⟩

theorem mathdb_342364 (h : Remaining) : ¬ Conj61 :=
  Ulas.mathdb_342364 ⟨evenFormula_proved,h⟩

theorem conj61_some (h : Remaining) : Conj61Some :=
  Ulas.conj61_some ⟨evenFormula_proved,h⟩
end Ulas.Even5
