import NInputs112
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_6437 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(74,false),(77,false),(85,true),(90,false)]
theorem inp_6437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6437 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6437 (by decide) v hb
def cl_6438 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,false),(77,false),(85,true),(90,false)]
theorem inp_6438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6438 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6438 v hb
def cl_6439 : CNF.NClause := [(50,false),(19,false),(63,true),(71,true),(74,false),(77,false),(85,true),(90,false)]
theorem inp_6439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6439 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6439 (by decide) v hb
def cl_6440 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,false),(77,false),(85,true),(90,false)]
theorem inp_6440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6440 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6440 v hb
def cl_6441 : CNF.NClause := [(50,false),(19,false),(63,false),(71,false),(74,true),(77,false),(85,true),(90,false)]
theorem inp_6441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6441 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6441 (by decide) v hb
def cl_6442 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,true),(77,false),(85,true),(90,false)]
theorem inp_6442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6442 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6442 v hb
def cl_6443 : CNF.NClause := [(50,false),(19,false),(63,true),(71,false),(74,true),(77,false),(85,true),(90,false)]
theorem inp_6443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6443 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6443 (by decide) v hb
def cl_6444 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,true),(77,false),(85,true),(90,false)]
theorem inp_6444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6444 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6444 v hb
def cl_6445 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(74,true),(77,false),(85,true),(90,false)]
theorem inp_6445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6445 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6445 (by decide) v hb
def cl_6446 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,true),(77,false),(85,true),(90,false)]
theorem inp_6446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6446 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6446 (by decide) v hb
def cl_6447 : CNF.NClause := [(50,false),(19,false),(63,true),(71,true),(74,true),(77,false),(85,true),(90,false)]
theorem inp_6447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6447 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6447 (by decide) v hb
def cl_6448 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,true),(77,false),(85,true),(90,false)]
theorem inp_6448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6448 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6448 (by decide) v hb
def cl_6449 : CNF.NClause := [(50,false),(19,false),(63,false),(71,false),(74,false),(77,true),(85,true),(90,false)]
theorem inp_6449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6449 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6449 (by decide) v hb
def cl_6450 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,false),(77,true),(85,true),(90,false)]
theorem inp_6450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6450 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6450 v hb
def cl_6451 : CNF.NClause := [(50,false),(19,false),(63,true),(71,false),(74,false),(77,true),(85,true),(90,false)]
theorem inp_6451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6451 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6451 (by decide) v hb
def cl_6452 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,false),(77,true),(85,true),(90,false)]
theorem inp_6452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6452 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6452 v hb
def cl_6453 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(74,false),(77,true),(85,true),(90,false)]
theorem inp_6453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6453 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6453 (by decide) v hb
def cl_6454 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,false),(77,true),(85,true),(90,false)]
theorem inp_6454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6454 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6454 v hb
def cl_6455 : CNF.NClause := [(50,false),(19,false),(63,true),(71,true),(74,false),(77,true),(85,true),(90,false)]
theorem inp_6455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6455 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6455 (by decide) v hb
def cl_6456 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,false),(77,true),(85,true),(90,false)]
theorem inp_6456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6456 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6456 v hb
def cl_6457 : CNF.NClause := [(50,false),(19,false),(63,false),(71,false),(74,true),(77,true),(85,true),(90,false)]
theorem inp_6457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6457 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6457 (by decide) v hb
def cl_6458 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,true),(77,true),(85,true),(90,false)]
theorem inp_6458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6458 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6458 (by decide) v hb
def cl_6459 : CNF.NClause := [(50,false),(19,false),(63,true),(71,false),(74,true),(77,true),(85,true),(90,false)]
theorem inp_6459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6459 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6459 (by decide) v hb
def cl_6460 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,true),(77,true),(85,true),(90,false)]
theorem inp_6460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6460 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6460 (by decide) v hb
def cl_6461 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(74,true),(77,true),(85,true),(90,false)]
theorem inp_6461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6461 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6461 (by decide) v hb
def cl_6462 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,true),(77,true),(85,true),(90,false)]
theorem inp_6462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6462 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6462 (by decide) v hb
def cl_6463 : CNF.NClause := [(50,false),(19,false),(63,true),(71,true),(74,true),(77,true),(85,true),(90,false)]
theorem inp_6463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6463 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6463 (by decide) v hb
def cl_6464 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,true),(77,true),(85,true),(90,false)]
theorem inp_6464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6464 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6464 (by decide) v hb
def cl_6465 : CNF.NClause := [(50,false),(19,false),(63,false),(71,false),(74,false),(77,false),(85,false),(90,true)]
theorem inp_6465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6465 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6465 (by decide) v hb
def cl_6466 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,false),(77,false),(85,false),(90,true)]
theorem inp_6466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6466 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6466 (by decide) v hb
def cl_6467 : CNF.NClause := [(50,false),(19,false),(63,true),(71,false),(74,false),(77,false),(85,false),(90,true)]
theorem inp_6467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6467 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6467 (by decide) v hb
def cl_6468 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,false),(77,false),(85,false),(90,true)]
theorem inp_6468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6468 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6468 (by decide) v hb
def cl_6469 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(74,false),(77,false),(85,false),(90,true)]
theorem inp_6469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6469 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6469 (by decide) v hb
def cl_6470 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,false),(77,false),(85,false),(90,true)]
theorem inp_6470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6470 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6470 (by decide) v hb
def cl_6471 : CNF.NClause := [(50,false),(19,false),(63,true),(71,true),(74,false),(77,false),(85,false),(90,true)]
theorem inp_6471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6471 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6471 (by decide) v hb
def cl_6472 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,false),(77,false),(85,false),(90,true)]
theorem inp_6472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6472 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6472 (by decide) v hb
def cl_6473 : CNF.NClause := [(50,false),(19,false),(63,false),(71,false),(74,true),(77,false),(85,false),(90,true)]
theorem inp_6473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6473 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6473 (by decide) v hb
def cl_6474 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,true),(77,false),(85,false),(90,true)]
theorem inp_6474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6474 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6474 (by decide) v hb
def cl_6475 : CNF.NClause := [(50,false),(19,false),(63,true),(71,false),(74,true),(77,false),(85,false),(90,true)]
theorem inp_6475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6475 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6475 (by decide) v hb
def cl_6476 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,true),(77,false),(85,false),(90,true)]
theorem inp_6476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6476 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6476 (by decide) v hb
def cl_6477 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(74,true),(77,false),(85,false),(90,true)]
theorem inp_6477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6477 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6477 (by decide) v hb
def cl_6478 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,true),(77,false),(85,false),(90,true)]
theorem inp_6478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6478 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6478 (by decide) v hb
def cl_6479 : CNF.NClause := [(50,false),(19,false),(63,true),(71,true),(74,true),(77,false),(85,false),(90,true)]
theorem inp_6479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6479 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6479 (by decide) v hb
def cl_6480 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,true),(77,false),(85,false),(90,true)]
theorem inp_6480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6480 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6480 (by decide) v hb
def cl_6481 : CNF.NClause := [(50,false),(19,false),(63,false),(71,false),(74,false),(77,true),(85,false),(90,true)]
theorem inp_6481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6481 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6481 (by decide) v hb
def cl_6482 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,false),(77,true),(85,false),(90,true)]
theorem inp_6482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6482 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6482 (by decide) v hb
def cl_6483 : CNF.NClause := [(50,false),(19,false),(63,true),(71,false),(74,false),(77,true),(85,false),(90,true)]
theorem inp_6483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6483 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6483 (by decide) v hb
def cl_6484 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,false),(77,true),(85,false),(90,true)]
theorem inp_6484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6484 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6484 (by decide) v hb
def cl_6485 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(74,false),(77,true),(85,false),(90,true)]
theorem inp_6485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6485 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6485 (by decide) v hb
def cl_6486 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,false),(77,true),(85,false),(90,true)]
theorem inp_6486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6486 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6486 (by decide) v hb
end Percolation.NReplay
