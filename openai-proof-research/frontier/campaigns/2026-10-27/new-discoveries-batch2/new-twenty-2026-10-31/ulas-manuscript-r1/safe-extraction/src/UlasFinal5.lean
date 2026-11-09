import UlasEven5Final
import UlasOdd5Final

namespace Ulas.Final5

theorem full_theorem_E2 :
    EvenFormula ∧ OddOneBound ∧ OddThreeBound ∧ OddOneEquality ∧
    OddThreeEquality ∧ FifteenBound ∧ NeverFifteen :=
  Ulas.full_theorem ⟨Ulas.Even5.evenFormula_proved, Ulas.Round5Odd.odd_theorem⟩

theorem mathdb_342364 : ¬ Conj61 :=
  Ulas.mathdb_342364 ⟨Ulas.Even5.evenFormula_proved, Ulas.Round5Odd.odd_theorem⟩

theorem conj61_some : Conj61Some :=
  Ulas.conj61_some ⟨Ulas.Even5.evenFormula_proved, Ulas.Round5Odd.odd_theorem⟩

#print full_theorem_E2
#print mathdb_342364
#print conj61_some
#print axioms full_theorem_E2
#print axioms mathdb_342364
#print axioms conj61_some
end Ulas.Final5
