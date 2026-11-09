import NInputs131
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_7494 : CNF.NClause := [(58,false),(27,true),(62,false),(69,true),(76,false),(78,false),(85,false),(89,true)]
theorem inp_7494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7494 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7494 (by decide) v hb
def cl_7495 : CNF.NClause := [(58,false),(27,false),(62,true),(69,true),(76,false),(78,false),(85,false),(89,true)]
theorem inp_7495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7495 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7495 (by decide) v hb
def cl_7496 : CNF.NClause := [(58,false),(27,true),(62,true),(69,true),(76,false),(78,false),(85,false),(89,true)]
theorem inp_7496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7496 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7496 (by decide) v hb
def cl_7497 : CNF.NClause := [(58,false),(27,false),(62,false),(69,false),(76,true),(78,false),(85,false),(89,true)]
theorem inp_7497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7497 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7497 (by decide) v hb
def cl_7498 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,true),(78,false),(85,false),(89,true)]
theorem inp_7498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7498 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7498 (by decide) v hb
def cl_7499 : CNF.NClause := [(58,false),(27,false),(62,true),(69,false),(76,true),(78,false),(85,false),(89,true)]
theorem inp_7499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7499 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7499 (by decide) v hb
def cl_7500 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,true),(78,false),(85,false),(89,true)]
theorem inp_7500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7500 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7500 (by decide) v hb
def cl_7501 : CNF.NClause := [(58,false),(27,false),(62,false),(69,true),(76,true),(78,false),(85,false),(89,true)]
theorem inp_7501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7501 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7501 (by decide) v hb
def cl_7502 : CNF.NClause := [(58,false),(27,true),(62,false),(69,true),(76,true),(78,false),(85,false),(89,true)]
theorem inp_7502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7502 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7502 (by decide) v hb
def cl_7503 : CNF.NClause := [(58,false),(27,false),(62,true),(69,true),(76,true),(78,false),(85,false),(89,true)]
theorem inp_7503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7503 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7503 (by decide) v hb
def cl_7504 : CNF.NClause := [(58,false),(27,true),(62,true),(69,true),(76,true),(78,false),(85,false),(89,true)]
theorem inp_7504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7504 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7504 (by decide) v hb
def cl_7505 : CNF.NClause := [(58,false),(27,false),(62,false),(69,false),(76,false),(78,true),(85,false),(89,true)]
theorem inp_7505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7505 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7505 (by decide) v hb
def cl_7506 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,false),(78,true),(85,false),(89,true)]
theorem inp_7506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7506 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7506 (by decide) v hb
def cl_7507 : CNF.NClause := [(58,false),(27,false),(62,true),(69,false),(76,false),(78,true),(85,false),(89,true)]
theorem inp_7507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7507 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7507 (by decide) v hb
def cl_7508 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,false),(78,true),(85,false),(89,true)]
theorem inp_7508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7508 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7508 (by decide) v hb
def cl_7509 : CNF.NClause := [(58,false),(27,false),(62,false),(69,true),(76,false),(78,true),(85,false),(89,true)]
theorem inp_7509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7509 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7509 (by decide) v hb
def cl_7510 : CNF.NClause := [(58,false),(27,true),(62,false),(69,true),(76,false),(78,true),(85,false),(89,true)]
theorem inp_7510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7510 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7510 (by decide) v hb
def cl_7511 : CNF.NClause := [(58,false),(27,false),(62,true),(69,true),(76,false),(78,true),(85,false),(89,true)]
theorem inp_7511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7511 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7511 (by decide) v hb
def cl_7512 : CNF.NClause := [(58,false),(27,true),(62,true),(69,true),(76,false),(78,true),(85,false),(89,true)]
theorem inp_7512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7512 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7512 (by decide) v hb
def cl_7513 : CNF.NClause := [(58,false),(27,false),(62,false),(69,false),(76,true),(78,true),(85,false),(89,true)]
theorem inp_7513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7513 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7513 (by decide) v hb
def cl_7514 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,true),(78,true),(85,false),(89,true)]
theorem inp_7514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7514 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7514 (by decide) v hb
def cl_7515 : CNF.NClause := [(58,false),(27,false),(62,true),(69,false),(76,true),(78,true),(85,false),(89,true)]
theorem inp_7515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7515 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7515 (by decide) v hb
def cl_7516 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,true),(78,true),(85,false),(89,true)]
theorem inp_7516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7516 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7516 (by decide) v hb
def cl_7517 : CNF.NClause := [(58,false),(27,false),(62,false),(69,true),(76,true),(78,true),(85,false),(89,true)]
theorem inp_7517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7517 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7517 (by decide) v hb
def cl_7518 : CNF.NClause := [(58,false),(27,true),(62,false),(69,true),(76,true),(78,true),(85,false),(89,true)]
theorem inp_7518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7518 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7518 (by decide) v hb
def cl_7520 : CNF.NClause := [(58,false),(27,true),(62,true),(69,true),(76,true),(78,true),(85,false),(89,true)]
theorem inp_7520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7520 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7520 (by decide) v hb
def cl_7521 : CNF.NClause := [(58,false),(27,false),(62,false),(69,false),(76,false),(78,false),(85,true),(89,true)]
theorem inp_7521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7521 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7521 (by decide) v hb
def cl_7522 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,false),(78,false),(85,true),(89,true)]
theorem inp_7522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7522 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7522 v hb
def cl_7523 : CNF.NClause := [(58,false),(27,false),(62,true),(69,false),(76,false),(78,false),(85,true),(89,true)]
theorem inp_7523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7523 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7523 (by decide) v hb
def cl_7524 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,false),(78,false),(85,true),(89,true)]
theorem inp_7524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7524 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7524 v hb
def cl_7525 : CNF.NClause := [(58,false),(27,false),(62,false),(69,true),(76,false),(78,false),(85,true),(89,true)]
theorem inp_7525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7525 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7525 (by decide) v hb
def cl_7526 : CNF.NClause := [(58,false),(27,true),(62,false),(69,true),(76,false),(78,false),(85,true),(89,true)]
theorem inp_7526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7526 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7526 (by decide) v hb
def cl_7527 : CNF.NClause := [(58,false),(27,false),(62,true),(69,true),(76,false),(78,false),(85,true),(89,true)]
theorem inp_7527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7527 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7527 (by decide) v hb
def cl_7528 : CNF.NClause := [(58,false),(27,true),(62,true),(69,true),(76,false),(78,false),(85,true),(89,true)]
theorem inp_7528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7528 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7528 (by decide) v hb
def cl_7529 : CNF.NClause := [(58,false),(27,false),(62,false),(69,false),(76,true),(78,false),(85,true),(89,true)]
theorem inp_7529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7529 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7529 (by decide) v hb
def cl_7530 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,true),(78,false),(85,true),(89,true)]
theorem inp_7530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7530 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7530 v hb
def cl_7531 : CNF.NClause := [(58,false),(27,false),(62,true),(69,false),(76,true),(78,false),(85,true),(89,true)]
theorem inp_7531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7531 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7531 (by decide) v hb
def cl_7532 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,true),(78,false),(85,true),(89,true)]
theorem inp_7532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7532 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7532 (by decide) v hb
def cl_7533 : CNF.NClause := [(58,false),(27,false),(62,false),(69,true),(76,true),(78,false),(85,true),(89,true)]
theorem inp_7533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7533 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7533 (by decide) v hb
def cl_7534 : CNF.NClause := [(58,false),(27,true),(62,false),(69,true),(76,true),(78,false),(85,true),(89,true)]
theorem inp_7534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7534 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7534 (by decide) v hb
def cl_7535 : CNF.NClause := [(58,false),(27,false),(62,true),(69,true),(76,true),(78,false),(85,true),(89,true)]
theorem inp_7535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7535 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7535 (by decide) v hb
def cl_7536 : CNF.NClause := [(58,false),(27,true),(62,true),(69,true),(76,true),(78,false),(85,true),(89,true)]
theorem inp_7536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7536 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7536 (by decide) v hb
def cl_7537 : CNF.NClause := [(58,false),(27,false),(62,false),(69,false),(76,false),(78,true),(85,true),(89,true)]
theorem inp_7537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7537 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7537 (by decide) v hb
def cl_7538 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,false),(78,true),(85,true),(89,true)]
theorem inp_7538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7538 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7538 (by decide) v hb
def cl_7539 : CNF.NClause := [(58,false),(27,false),(62,true),(69,false),(76,false),(78,true),(85,true),(89,true)]
theorem inp_7539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7539 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7539 (by decide) v hb
def cl_7540 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,false),(78,true),(85,true),(89,true)]
theorem inp_7540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7540 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7540 (by decide) v hb
def cl_7541 : CNF.NClause := [(58,false),(27,false),(62,false),(69,true),(76,false),(78,true),(85,true),(89,true)]
theorem inp_7541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7541 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7541 (by decide) v hb
def cl_7542 : CNF.NClause := [(58,false),(27,true),(62,false),(69,true),(76,false),(78,true),(85,true),(89,true)]
theorem inp_7542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7542 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7542 (by decide) v hb
def cl_7543 : CNF.NClause := [(58,false),(27,false),(62,true),(69,true),(76,false),(78,true),(85,true),(89,true)]
theorem inp_7543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7543 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7543 (by decide) v hb
def cl_7544 : CNF.NClause := [(58,false),(27,true),(62,true),(69,true),(76,false),(78,true),(85,true),(89,true)]
theorem inp_7544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7544 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7544 (by decide) v hb
end Percolation.NReplay
