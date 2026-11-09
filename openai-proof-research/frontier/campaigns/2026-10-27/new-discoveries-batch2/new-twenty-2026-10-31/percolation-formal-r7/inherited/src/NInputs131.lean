import NInputs130
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_7443 : CNF.NClause := [(58,false),(27,false),(62,true),(69,false),(76,false),(78,true),(85,false),(89,false)]
theorem inp_7443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7443 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7443 (by decide) v hb
def cl_7444 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,false),(78,true),(85,false),(89,false)]
theorem inp_7444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7444 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7444 (by decide) v hb
def cl_7445 : CNF.NClause := [(58,false),(27,false),(62,false),(69,true),(76,false),(78,true),(85,false),(89,false)]
theorem inp_7445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7445 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7445 (by decide) v hb
def cl_7446 : CNF.NClause := [(58,false),(27,true),(62,false),(69,true),(76,false),(78,true),(85,false),(89,false)]
theorem inp_7446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7446 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7446 (by decide) v hb
def cl_7447 : CNF.NClause := [(58,false),(27,false),(62,true),(69,true),(76,false),(78,true),(85,false),(89,false)]
theorem inp_7447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7447 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7447 (by decide) v hb
def cl_7448 : CNF.NClause := [(58,false),(27,true),(62,true),(69,true),(76,false),(78,true),(85,false),(89,false)]
theorem inp_7448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7448 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7448 (by decide) v hb
def cl_7449 : CNF.NClause := [(58,false),(27,false),(62,false),(69,false),(76,true),(78,true),(85,false),(89,false)]
theorem inp_7449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7449 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7449 (by decide) v hb
def cl_7450 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,true),(78,true),(85,false),(89,false)]
theorem inp_7450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7450 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7450 (by decide) v hb
def cl_7451 : CNF.NClause := [(58,false),(27,false),(62,true),(69,false),(76,true),(78,true),(85,false),(89,false)]
theorem inp_7451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7451 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7451 (by decide) v hb
def cl_7452 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,true),(78,true),(85,false),(89,false)]
theorem inp_7452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7452 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7452 (by decide) v hb
def cl_7453 : CNF.NClause := [(58,false),(27,false),(62,false),(69,true),(76,true),(78,true),(85,false),(89,false)]
theorem inp_7453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7453 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7453 (by decide) v hb
def cl_7454 : CNF.NClause := [(58,false),(27,true),(62,false),(69,true),(76,true),(78,true),(85,false),(89,false)]
theorem inp_7454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7454 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7454 (by decide) v hb
def cl_7455 : CNF.NClause := [(58,false),(27,false),(62,true),(69,true),(76,true),(78,true),(85,false),(89,false)]
theorem inp_7455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7455 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7455 (by decide) v hb
def cl_7456 : CNF.NClause := [(58,false),(27,true),(62,true),(69,true),(76,true),(78,true),(85,false),(89,false)]
theorem inp_7456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7456 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7456 (by decide) v hb
def cl_7457 : CNF.NClause := [(58,false),(27,false),(62,false),(69,false),(76,false),(78,false),(85,true),(89,false)]
theorem inp_7457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7457 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7457 (by decide) v hb
def cl_7458 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,false),(78,false),(85,true),(89,false)]
theorem inp_7458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7458 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7458 v hb
def cl_7459 : CNF.NClause := [(58,false),(27,false),(62,true),(69,false),(76,false),(78,false),(85,true),(89,false)]
theorem inp_7459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7459 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7459 (by decide) v hb
def cl_7460 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,false),(78,false),(85,true),(89,false)]
theorem inp_7460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7460 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7460 v hb
def cl_7461 : CNF.NClause := [(58,false),(27,false),(62,false),(69,true),(76,false),(78,false),(85,true),(89,false)]
theorem inp_7461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7461 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7461 (by decide) v hb
def cl_7462 : CNF.NClause := [(58,false),(27,true),(62,false),(69,true),(76,false),(78,false),(85,true),(89,false)]
theorem inp_7462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7462 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7462 (by decide) v hb
def cl_7463 : CNF.NClause := [(58,false),(27,false),(62,true),(69,true),(76,false),(78,false),(85,true),(89,false)]
theorem inp_7463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7463 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7463 (by decide) v hb
def cl_7464 : CNF.NClause := [(58,false),(27,true),(62,true),(69,true),(76,false),(78,false),(85,true),(89,false)]
theorem inp_7464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7464 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7464 (by decide) v hb
def cl_7465 : CNF.NClause := [(58,false),(27,false),(62,false),(69,false),(76,true),(78,false),(85,true),(89,false)]
theorem inp_7465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7465 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7465 (by decide) v hb
def cl_7466 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,true),(78,false),(85,true),(89,false)]
theorem inp_7466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7466 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7466 v hb
def cl_7467 : CNF.NClause := [(58,false),(27,false),(62,true),(69,false),(76,true),(78,false),(85,true),(89,false)]
theorem inp_7467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7467 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7467 (by decide) v hb
def cl_7468 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,true),(78,false),(85,true),(89,false)]
theorem inp_7468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7468 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7468 v hb
def cl_7469 : CNF.NClause := [(58,false),(27,false),(62,false),(69,true),(76,true),(78,false),(85,true),(89,false)]
theorem inp_7469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7469 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7469 (by decide) v hb
def cl_7470 : CNF.NClause := [(58,false),(27,true),(62,false),(69,true),(76,true),(78,false),(85,true),(89,false)]
theorem inp_7470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7470 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7470 (by decide) v hb
def cl_7471 : CNF.NClause := [(58,false),(27,false),(62,true),(69,true),(76,true),(78,false),(85,true),(89,false)]
theorem inp_7471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7471 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7471 (by decide) v hb
def cl_7472 : CNF.NClause := [(58,false),(27,true),(62,true),(69,true),(76,true),(78,false),(85,true),(89,false)]
theorem inp_7472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7472 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7472 (by decide) v hb
def cl_7473 : CNF.NClause := [(58,false),(27,false),(62,false),(69,false),(76,false),(78,true),(85,true),(89,false)]
theorem inp_7473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7473 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7473 (by decide) v hb
def cl_7474 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,false),(78,true),(85,true),(89,false)]
theorem inp_7474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7474 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7474 (by decide) v hb
def cl_7475 : CNF.NClause := [(58,false),(27,false),(62,true),(69,false),(76,false),(78,true),(85,true),(89,false)]
theorem inp_7475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7475 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7475 (by decide) v hb
def cl_7476 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,false),(78,true),(85,true),(89,false)]
theorem inp_7476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7476 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7476 (by decide) v hb
def cl_7477 : CNF.NClause := [(58,false),(27,false),(62,false),(69,true),(76,false),(78,true),(85,true),(89,false)]
theorem inp_7477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7477 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7477 (by decide) v hb
def cl_7478 : CNF.NClause := [(58,false),(27,true),(62,false),(69,true),(76,false),(78,true),(85,true),(89,false)]
theorem inp_7478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7478 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7478 (by decide) v hb
def cl_7479 : CNF.NClause := [(58,false),(27,false),(62,true),(69,true),(76,false),(78,true),(85,true),(89,false)]
theorem inp_7479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7479 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7479 (by decide) v hb
def cl_7480 : CNF.NClause := [(58,false),(27,true),(62,true),(69,true),(76,false),(78,true),(85,true),(89,false)]
theorem inp_7480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7480 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7480 (by decide) v hb
def cl_7481 : CNF.NClause := [(58,false),(27,false),(62,false),(69,false),(76,true),(78,true),(85,true),(89,false)]
theorem inp_7481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7481 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7481 (by decide) v hb
def cl_7482 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,true),(78,true),(85,true),(89,false)]
theorem inp_7482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7482 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7482 (by decide) v hb
def cl_7483 : CNF.NClause := [(58,false),(27,false),(62,true),(69,false),(76,true),(78,true),(85,true),(89,false)]
theorem inp_7483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7483 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7483 (by decide) v hb
def cl_7484 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,true),(78,true),(85,true),(89,false)]
theorem inp_7484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7484 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7484 (by decide) v hb
def cl_7485 : CNF.NClause := [(58,false),(27,false),(62,false),(69,true),(76,true),(78,true),(85,true),(89,false)]
theorem inp_7485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7485 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7485 (by decide) v hb
def cl_7486 : CNF.NClause := [(58,false),(27,true),(62,false),(69,true),(76,true),(78,true),(85,true),(89,false)]
theorem inp_7486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7486 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7486 (by decide) v hb
def cl_7488 : CNF.NClause := [(58,false),(27,true),(62,true),(69,true),(76,true),(78,true),(85,true),(89,false)]
theorem inp_7488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7488 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7488 (by decide) v hb
def cl_7489 : CNF.NClause := [(58,false),(27,false),(62,false),(69,false),(76,false),(78,false),(85,false),(89,true)]
theorem inp_7489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7489 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7489 (by decide) v hb
def cl_7490 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,false),(78,false),(85,false),(89,true)]
theorem inp_7490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7490 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7490 v hb
def cl_7491 : CNF.NClause := [(58,false),(27,false),(62,true),(69,false),(76,false),(78,false),(85,false),(89,true)]
theorem inp_7491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7491 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7491 (by decide) v hb
def cl_7492 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,false),(78,false),(85,false),(89,true)]
theorem inp_7492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7492 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7492 v hb
def cl_7493 : CNF.NClause := [(58,false),(27,false),(62,false),(69,true),(76,false),(78,false),(85,false),(89,true)]
theorem inp_7493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7493 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7493 (by decide) v hb
end Percolation.NReplay
