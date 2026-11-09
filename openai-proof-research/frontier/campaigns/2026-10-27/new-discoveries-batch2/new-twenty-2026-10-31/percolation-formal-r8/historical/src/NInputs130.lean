import NInputs129
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_7385 : CNF.NClause := [(57,false),(26,false),(62,false),(71,false),(75,true),(79,true),(83,false),(91,true)]
theorem inp_7385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7385 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7385 (by decide) v hb
def cl_7386 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,true),(79,true),(83,false),(91,true)]
theorem inp_7386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7386 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7386 (by decide) v hb
def cl_7387 : CNF.NClause := [(57,false),(26,false),(62,true),(71,false),(75,true),(79,true),(83,false),(91,true)]
theorem inp_7387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7387 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7387 (by decide) v hb
def cl_7388 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,true),(79,true),(83,false),(91,true)]
theorem inp_7388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7388 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7388 (by decide) v hb
def cl_7389 : CNF.NClause := [(57,false),(26,false),(62,false),(71,true),(75,true),(79,true),(83,false),(91,true)]
theorem inp_7389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7389 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7389 (by decide) v hb
def cl_7390 : CNF.NClause := [(57,false),(26,true),(62,false),(71,true),(75,true),(79,true),(83,false),(91,true)]
theorem inp_7390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7390 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7390 (by decide) v hb
def cl_7392 : CNF.NClause := [(57,false),(26,true),(62,true),(71,true),(75,true),(79,true),(83,false),(91,true)]
theorem inp_7392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7392 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7392 (by decide) v hb
def cl_7393 : CNF.NClause := [(57,false),(26,false),(62,false),(71,false),(75,false),(79,false),(83,true),(91,true)]
theorem inp_7393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7393 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7393 (by decide) v hb
def cl_7394 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,false),(79,false),(83,true),(91,true)]
theorem inp_7394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7394 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7394 (by decide) v hb
def cl_7395 : CNF.NClause := [(57,false),(26,false),(62,true),(71,false),(75,false),(79,false),(83,true),(91,true)]
theorem inp_7395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7395 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7395 (by decide) v hb
def cl_7396 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,false),(79,false),(83,true),(91,true)]
theorem inp_7396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7396 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7396 (by decide) v hb
def cl_7397 : CNF.NClause := [(57,false),(26,false),(62,false),(71,true),(75,false),(79,false),(83,true),(91,true)]
theorem inp_7397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7397 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7397 (by decide) v hb
def cl_7398 : CNF.NClause := [(57,false),(26,true),(62,false),(71,true),(75,false),(79,false),(83,true),(91,true)]
theorem inp_7398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7398 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7398 (by decide) v hb
def cl_7399 : CNF.NClause := [(57,false),(26,false),(62,true),(71,true),(75,false),(79,false),(83,true),(91,true)]
theorem inp_7399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7399 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7399 (by decide) v hb
def cl_7400 : CNF.NClause := [(57,false),(26,true),(62,true),(71,true),(75,false),(79,false),(83,true),(91,true)]
theorem inp_7400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7400 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7400 (by decide) v hb
def cl_7402 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,true),(79,false),(83,true),(91,true)]
theorem inp_7402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7402 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7402 (by decide) v hb
def cl_7403 : CNF.NClause := [(57,false),(26,false),(62,true),(71,false),(75,true),(79,false),(83,true),(91,true)]
theorem inp_7403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7403 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7403 (by decide) v hb
def cl_7404 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,true),(79,false),(83,true),(91,true)]
theorem inp_7404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7404 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7404 (by decide) v hb
def cl_7406 : CNF.NClause := [(57,false),(26,true),(62,false),(71,true),(75,true),(79,false),(83,true),(91,true)]
theorem inp_7406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7406 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7406 (by decide) v hb
def cl_7408 : CNF.NClause := [(57,false),(26,true),(62,true),(71,true),(75,true),(79,false),(83,true),(91,true)]
theorem inp_7408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7408 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7408 (by decide) v hb
def cl_7409 : CNF.NClause := [(57,false),(26,false),(62,false),(71,false),(75,false),(79,true),(83,true),(91,true)]
theorem inp_7409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7409 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7409 (by decide) v hb
def cl_7410 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,false),(79,true),(83,true),(91,true)]
theorem inp_7410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7410 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7410 (by decide) v hb
def cl_7411 : CNF.NClause := [(57,false),(26,false),(62,true),(71,false),(75,false),(79,true),(83,true),(91,true)]
theorem inp_7411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7411 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7411 (by decide) v hb
def cl_7412 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,false),(79,true),(83,true),(91,true)]
theorem inp_7412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7412 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7412 (by decide) v hb
def cl_7413 : CNF.NClause := [(57,false),(26,false),(62,false),(71,true),(75,false),(79,true),(83,true),(91,true)]
theorem inp_7413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7413 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7413 (by decide) v hb
def cl_7414 : CNF.NClause := [(57,false),(26,true),(62,false),(71,true),(75,false),(79,true),(83,true),(91,true)]
theorem inp_7414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7414 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7414 (by decide) v hb
def cl_7417 : CNF.NClause := [(57,false),(26,false),(62,false),(71,false),(75,true),(79,true),(83,true),(91,true)]
theorem inp_7417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7417 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7417 (by decide) v hb
def cl_7418 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,true),(79,true),(83,true),(91,true)]
theorem inp_7418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7418 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7418 (by decide) v hb
def cl_7419 : CNF.NClause := [(57,false),(26,false),(62,true),(71,false),(75,true),(79,true),(83,true),(91,true)]
theorem inp_7419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7419 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7419 (by decide) v hb
def cl_7420 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,true),(79,true),(83,true),(91,true)]
theorem inp_7420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7420 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7420 (by decide) v hb
def cl_7422 : CNF.NClause := [(57,false),(26,true),(62,false),(71,true),(75,true),(79,true),(83,true),(91,true)]
theorem inp_7422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7422 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7422 (by decide) v hb
def cl_7424 : CNF.NClause := [(57,false),(26,true),(62,true),(71,true),(75,true),(79,true),(83,true),(91,true)]
theorem inp_7424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7424 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7424 (by decide) v hb
def cl_7425 : CNF.NClause := [(58,true),(27,false),(62,false),(69,false),(76,false),(78,false),(85,false),(89,false)]
theorem inp_7425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7425 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7425 (by decide) v hb
def cl_7426 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,false),(78,false),(85,false),(89,false)]
theorem inp_7426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7426 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7426 v hb
def cl_7427 : CNF.NClause := [(58,false),(27,false),(62,true),(69,false),(76,false),(78,false),(85,false),(89,false)]
theorem inp_7427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7427 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7427 (by decide) v hb
def cl_7428 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,false),(78,false),(85,false),(89,false)]
theorem inp_7428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7428 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7428 v hb
def cl_7429 : CNF.NClause := [(58,false),(27,false),(62,false),(69,true),(76,false),(78,false),(85,false),(89,false)]
theorem inp_7429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7429 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7429 (by decide) v hb
def cl_7430 : CNF.NClause := [(58,false),(27,true),(62,false),(69,true),(76,false),(78,false),(85,false),(89,false)]
theorem inp_7430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7430 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7430 (by decide) v hb
def cl_7431 : CNF.NClause := [(58,false),(27,false),(62,true),(69,true),(76,false),(78,false),(85,false),(89,false)]
theorem inp_7431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7431 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7431 (by decide) v hb
def cl_7432 : CNF.NClause := [(58,false),(27,true),(62,true),(69,true),(76,false),(78,false),(85,false),(89,false)]
theorem inp_7432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7432 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7432 (by decide) v hb
def cl_7433 : CNF.NClause := [(58,false),(27,false),(62,false),(69,false),(76,true),(78,false),(85,false),(89,false)]
theorem inp_7433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7433 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7433 (by decide) v hb
def cl_7434 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,true),(78,false),(85,false),(89,false)]
theorem inp_7434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7434 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7434 v hb
def cl_7435 : CNF.NClause := [(58,false),(27,false),(62,true),(69,false),(76,true),(78,false),(85,false),(89,false)]
theorem inp_7435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7435 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7435 (by decide) v hb
def cl_7436 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,true),(78,false),(85,false),(89,false)]
theorem inp_7436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7436 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7436 v hb
def cl_7437 : CNF.NClause := [(58,false),(27,false),(62,false),(69,true),(76,true),(78,false),(85,false),(89,false)]
theorem inp_7437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7437 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7437 (by decide) v hb
def cl_7438 : CNF.NClause := [(58,false),(27,true),(62,false),(69,true),(76,true),(78,false),(85,false),(89,false)]
theorem inp_7438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7438 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7438 (by decide) v hb
def cl_7439 : CNF.NClause := [(58,false),(27,false),(62,true),(69,true),(76,true),(78,false),(85,false),(89,false)]
theorem inp_7439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7439 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7439 (by decide) v hb
def cl_7440 : CNF.NClause := [(58,false),(27,true),(62,true),(69,true),(76,true),(78,false),(85,false),(89,false)]
theorem inp_7440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7440 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7440 (by decide) v hb
def cl_7441 : CNF.NClause := [(58,false),(27,false),(62,false),(69,false),(76,false),(78,true),(85,false),(89,false)]
theorem inp_7441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7441 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7441 (by decide) v hb
def cl_7442 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,false),(78,true),(85,false),(89,false)]
theorem inp_7442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7442 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7442 (by decide) v hb
end Percolation.NReplay
