import NInputs132
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_7545 : CNF.NClause := [(58,false),(27,false),(62,false),(69,false),(76,true),(78,true),(85,true),(89,true)]
theorem inp_7545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7545 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7545 (by decide) v hb
def cl_7546 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,true),(78,true),(85,true),(89,true)]
theorem inp_7546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7546 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7546 (by decide) v hb
def cl_7548 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,true),(78,true),(85,true),(89,true)]
theorem inp_7548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7548 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7548 (by decide) v hb
def cl_7549 : CNF.NClause := [(58,false),(27,false),(62,false),(69,true),(76,true),(78,true),(85,true),(89,true)]
theorem inp_7549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7549 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7549 (by decide) v hb
def cl_7550 : CNF.NClause := [(58,false),(27,true),(62,false),(69,true),(76,true),(78,true),(85,true),(89,true)]
theorem inp_7550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7550 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7550 (by decide) v hb
def cl_7552 : CNF.NClause := [(58,false),(27,true),(62,true),(69,true),(76,true),(78,true),(85,true),(89,true)]
theorem inp_7552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7552 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7552 (by decide) v hb
def cl_7553 : CNF.NClause := [(59,true),(28,false),(62,false),(70,false),(73,false),(81,false),(84,false),(90,false)]
theorem inp_7553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7553 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7553 (by decide) v hb
def cl_7554 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,false),(81,false),(84,false),(90,false)]
theorem inp_7554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7554 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7554 v hb
def cl_7555 : CNF.NClause := [(59,false),(28,false),(62,true),(70,false),(73,false),(81,false),(84,false),(90,false)]
theorem inp_7555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7555 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7555 (by decide) v hb
def cl_7556 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,false),(81,false),(84,false),(90,false)]
theorem inp_7556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7556 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7556 v hb
def cl_7557 : CNF.NClause := [(59,false),(28,false),(62,false),(70,true),(73,false),(81,false),(84,false),(90,false)]
theorem inp_7557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7557 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7557 v hb
def cl_7558 : CNF.NClause := [(59,false),(28,true),(62,false),(70,true),(73,false),(81,false),(84,false),(90,false)]
theorem inp_7558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7558 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7558 v hb
def cl_7559 : CNF.NClause := [(59,false),(28,false),(62,true),(70,true),(73,false),(81,false),(84,false),(90,false)]
theorem inp_7559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7559 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7559 v hb
def cl_7560 : CNF.NClause := [(59,false),(28,true),(62,true),(70,true),(73,false),(81,false),(84,false),(90,false)]
theorem inp_7560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7560 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7560 (by decide) v hb
def cl_7561 : CNF.NClause := [(59,false),(28,false),(62,false),(70,false),(73,true),(81,false),(84,false),(90,false)]
theorem inp_7561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7561 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7561 (by decide) v hb
def cl_7562 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,true),(81,false),(84,false),(90,false)]
theorem inp_7562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7562 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7562 v hb
def cl_7563 : CNF.NClause := [(59,false),(28,false),(62,true),(70,false),(73,true),(81,false),(84,false),(90,false)]
theorem inp_7563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7563 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7563 (by decide) v hb
def cl_7564 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,true),(81,false),(84,false),(90,false)]
theorem inp_7564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7564 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7564 v hb
def cl_7565 : CNF.NClause := [(59,false),(28,false),(62,false),(70,true),(73,true),(81,false),(84,false),(90,false)]
theorem inp_7565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7565 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7565 (by decide) v hb
def cl_7566 : CNF.NClause := [(59,false),(28,true),(62,false),(70,true),(73,true),(81,false),(84,false),(90,false)]
theorem inp_7566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7566 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7566 (by decide) v hb
def cl_7567 : CNF.NClause := [(59,false),(28,false),(62,true),(70,true),(73,true),(81,false),(84,false),(90,false)]
theorem inp_7567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7567 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7567 (by decide) v hb
def cl_7568 : CNF.NClause := [(59,false),(28,true),(62,true),(70,true),(73,true),(81,false),(84,false),(90,false)]
theorem inp_7568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7568 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7568 (by decide) v hb
def cl_7569 : CNF.NClause := [(59,false),(28,false),(62,false),(70,false),(73,false),(81,true),(84,false),(90,false)]
theorem inp_7569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7569 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7569 (by decide) v hb
def cl_7570 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,false),(81,true),(84,false),(90,false)]
theorem inp_7570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7570 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7570 v hb
def cl_7571 : CNF.NClause := [(59,false),(28,false),(62,true),(70,false),(73,false),(81,true),(84,false),(90,false)]
theorem inp_7571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7571 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7571 (by decide) v hb
def cl_7572 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,false),(81,true),(84,false),(90,false)]
theorem inp_7572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7572 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7572 v hb
def cl_7573 : CNF.NClause := [(59,false),(28,false),(62,false),(70,true),(73,false),(81,true),(84,false),(90,false)]
theorem inp_7573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7573 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7573 (by decide) v hb
def cl_7574 : CNF.NClause := [(59,false),(28,true),(62,false),(70,true),(73,false),(81,true),(84,false),(90,false)]
theorem inp_7574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7574 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7574 (by decide) v hb
def cl_7575 : CNF.NClause := [(59,false),(28,false),(62,true),(70,true),(73,false),(81,true),(84,false),(90,false)]
theorem inp_7575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7575 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7575 (by decide) v hb
def cl_7576 : CNF.NClause := [(59,false),(28,true),(62,true),(70,true),(73,false),(81,true),(84,false),(90,false)]
theorem inp_7576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7576 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7576 (by decide) v hb
def cl_7577 : CNF.NClause := [(59,false),(28,false),(62,false),(70,false),(73,true),(81,true),(84,false),(90,false)]
theorem inp_7577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7577 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7577 (by decide) v hb
def cl_7578 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,true),(81,true),(84,false),(90,false)]
theorem inp_7578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7578 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7578 v hb
def cl_7579 : CNF.NClause := [(59,false),(28,false),(62,true),(70,false),(73,true),(81,true),(84,false),(90,false)]
theorem inp_7579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7579 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7579 (by decide) v hb
def cl_7580 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,true),(81,true),(84,false),(90,false)]
theorem inp_7580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7580 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7580 v hb
def cl_7581 : CNF.NClause := [(59,false),(28,false),(62,false),(70,true),(73,true),(81,true),(84,false),(90,false)]
theorem inp_7581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7581 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7581 (by decide) v hb
def cl_7582 : CNF.NClause := [(59,false),(28,true),(62,false),(70,true),(73,true),(81,true),(84,false),(90,false)]
theorem inp_7582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7582 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7582 (by decide) v hb
def cl_7583 : CNF.NClause := [(59,false),(28,false),(62,true),(70,true),(73,true),(81,true),(84,false),(90,false)]
theorem inp_7583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7583 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7583 (by decide) v hb
def cl_7584 : CNF.NClause := [(59,false),(28,true),(62,true),(70,true),(73,true),(81,true),(84,false),(90,false)]
theorem inp_7584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7584 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7584 (by decide) v hb
def cl_7585 : CNF.NClause := [(59,false),(28,false),(62,false),(70,false),(73,false),(81,false),(84,true),(90,false)]
theorem inp_7585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7585 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7585 (by decide) v hb
def cl_7586 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,false),(81,false),(84,true),(90,false)]
theorem inp_7586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7586 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7586 v hb
def cl_7587 : CNF.NClause := [(59,false),(28,false),(62,true),(70,false),(73,false),(81,false),(84,true),(90,false)]
theorem inp_7587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7587 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7587 (by decide) v hb
def cl_7588 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,false),(81,false),(84,true),(90,false)]
theorem inp_7588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7588 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7588 v hb
def cl_7589 : CNF.NClause := [(59,false),(28,false),(62,false),(70,true),(73,false),(81,false),(84,true),(90,false)]
theorem inp_7589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7589 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7589 (by decide) v hb
def cl_7590 : CNF.NClause := [(59,false),(28,true),(62,false),(70,true),(73,false),(81,false),(84,true),(90,false)]
theorem inp_7590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7590 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7590 (by decide) v hb
def cl_7591 : CNF.NClause := [(59,false),(28,false),(62,true),(70,true),(73,false),(81,false),(84,true),(90,false)]
theorem inp_7591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7591 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7591 (by decide) v hb
def cl_7592 : CNF.NClause := [(59,false),(28,true),(62,true),(70,true),(73,false),(81,false),(84,true),(90,false)]
theorem inp_7592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7592 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7592 (by decide) v hb
def cl_7593 : CNF.NClause := [(59,false),(28,false),(62,false),(70,false),(73,true),(81,false),(84,true),(90,false)]
theorem inp_7593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7593 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7593 (by decide) v hb
def cl_7594 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,true),(81,false),(84,true),(90,false)]
theorem inp_7594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7594 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7594 (by decide) v hb
def cl_7595 : CNF.NClause := [(59,false),(28,false),(62,true),(70,false),(73,true),(81,false),(84,true),(90,false)]
theorem inp_7595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7595 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7595 (by decide) v hb
def cl_7596 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,true),(81,false),(84,true),(90,false)]
theorem inp_7596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7596 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7596 (by decide) v hb
end Percolation.NReplay
