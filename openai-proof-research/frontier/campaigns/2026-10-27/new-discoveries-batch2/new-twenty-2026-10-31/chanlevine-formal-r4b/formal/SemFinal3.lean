import Sem4Residual
namespace ChanLevine.Sem4

/-- PARTIAL: exactly CappedDeficitTrap remains in the cycle-test direction. -/
theorem cycleTestBridge (htrap : CappedDeficitTrap) : CycleTestBridge :=
  Sem3.cycleTestBridge (cycleTestWord htrap)

/-- PARTIAL: recurrent normalization is still unresolved. -/
theorem connectedFibres (hnorm : RecurrentNormalization) : ConnectedFibres :=
  ChanLevine.connectedFibres hnorm

/-- The unchanged two-premise round-3b interface is retained explicitly. -/
theorem cycleTestBridge_of_word (hw : CycleTestWord) : CycleTestBridge :=
  Sem3.cycleTestBridge hw

#print axioms quota_terminal_exists
#print axioms no_empty_rotor_closed_set
#print axioms balanced_return
#print axioms cycleTestWord
#print axioms cycleTestBridge
#print axioms connectedFibres
end ChanLevine.Sem4
