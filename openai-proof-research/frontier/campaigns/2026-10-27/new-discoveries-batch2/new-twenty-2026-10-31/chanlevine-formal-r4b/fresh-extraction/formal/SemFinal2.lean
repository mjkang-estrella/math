import Sem3Obstruction
import Sem3Removal
import SemRegression
namespace ChanLevine.Sem3

/-- PARTIAL handback: exactly the bounded return-word construction remains here. -/
theorem cycleTestBridge (hw : CycleTestWord) : CycleTestBridge :=
  ChanLevine.cycleTestBridge closedWordRecurrence hw closedWordCycleTest

/-- PARTIAL handback: sink normalization is still unproved. -/
theorem connectedFibres (hnorm : RecurrentNormalization) : ConnectedFibres :=
  ChanLevine.connectedFibres hnorm

/-- The source recurrence definition implies the cycle test without hypotheses. -/
theorem recurrent_cycleTest {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    {c : Config n} (hc : NatRecurrent c) : CycleTest c := by
  obtain ⟨w, hw, h⟩ := recurrent_closed_word hc
  exact closedWordCycleTest n hn c w hw h

/-- Unconditional source-facing signed recurrence and diverse-walk bridge. -/
theorem ambientBridge_unconditional : AmbientBridge := ambientBridge

#print axioms closedCoverage
#print axioms closedWordRecurrence
#print axioms closedWordCycleTest
#print axioms ambientBridge_unconditional
#print axioms cycleTestBridge
#print axioms connectedFibres
end ChanLevine.Sem3
