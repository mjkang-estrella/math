import Sem5Trap
namespace ChanLevine.Sem5

/-- Source recurrence is exactly the cycle test, without residual premises. -/
theorem cycleTestBridge : CycleTestBridge := Sem4.cycleTestBridge cappedDeficitTrap

/-- Equal-level, equal-weight recurrent states have a common legal descendant. -/
theorem connectedFibres : ConnectedFibres := ChanLevine.connectedFibres recurrentNormalization

#print axioms cappedDeficitTrap
#print axioms recurrentNormalization
#print axioms cycleTestBridge
#print axioms connectedFibres
end ChanLevine.Sem5
