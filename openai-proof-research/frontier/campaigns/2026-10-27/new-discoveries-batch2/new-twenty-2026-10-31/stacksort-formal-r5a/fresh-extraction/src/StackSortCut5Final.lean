import StackSortCut5Clip
import StackSortFinal4

namespace StackSort.Cut5
open Seeds2

/-- Round 5A: the frozen common-cut identity, for every supported r and s. -/
theorem commonCutCount_proved : StackSort.Round3.CommonCutCount := by
  intro M r s hM hr hrB hs hsB
  have hr21 := (Nat.le_min.mp hrB).2
  have hs21 := (Nat.le_min.mp hsB).2
  rw [literalX_eq_XI M r s hM hr hs hr21 hs21,
    literalI_eq_II M r s hM hr hs hr21 hs21,
    correction_eq_raw M r s hr hrB hs hsB]
  exact commonCutCount_raw M r s hM

#print axioms commonCutCount_proved
#print axioms commonCutCount_raw
#print axioms glue_injective
#print axioms glue_surjective
end StackSort.Cut5
