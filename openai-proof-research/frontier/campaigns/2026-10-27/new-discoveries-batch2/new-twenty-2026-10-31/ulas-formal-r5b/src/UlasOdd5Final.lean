import UlasOdd5Equality
namespace Ulas.Round5Odd
/-- All five odd obligations, unconditionally. -/
theorem odd_theorem : OddOneBound ∧ OddThreeBound ∧ OddOneEquality ∧
    OddThreeEquality ∧ FifteenBound :=
  ⟨oddOneBound,oddThreeBound,oddOneEquality,oddThreeEquality,fifteenBound⟩
/-- The only remaining obligation belongs to the separate even lane. -/
def Remaining : Prop := EvenFormula

theorem full_theorem (h : EvenFormula) :
    EvenFormula ∧ OddOneBound ∧ OddThreeBound ∧ OddOneEquality ∧
    OddThreeEquality ∧ FifteenBound ∧ NeverFifteen :=
  Ulas.full_theorem ⟨h,oddOneBound,oddThreeBound,oddOneEquality,oddThreeEquality,fifteenBound⟩

/-- Unconditional refutation under the per-k reading. Root decides acceptance. -/
theorem mathdb_342364 : ¬ Conj61 := Round3.mathdb_of_fifteen fifteenBound
/-- The existential reading is conditional only on the separate even formula. -/
theorem conj61_some (h : EvenFormula) : Conj61Some :=
  Ulas.conj61_some ⟨h,oddOneBound,oddThreeBound,oddOneEquality,oddThreeEquality,fifteenBound⟩
end Ulas.Round5Odd
