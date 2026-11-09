import NInputs074
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_4484 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,false),(78,false),(83,false),(87,false)]
theorem inp_4484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4484 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4484 v hb
def cl_4485 : CNF.NClause := [(35,false),(4,false),(63,false),(68,true),(73,false),(78,false),(83,false),(87,false)]
theorem inp_4485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4485 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4485 (by decide) v hb
def cl_4486 : CNF.NClause := [(35,false),(4,true),(63,false),(68,true),(73,false),(78,false),(83,false),(87,false)]
theorem inp_4486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4486 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4486 (by decide) v hb
def cl_4487 : CNF.NClause := [(35,false),(4,false),(63,true),(68,true),(73,false),(78,false),(83,false),(87,false)]
theorem inp_4487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4487 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4487 (by decide) v hb
def cl_4488 : CNF.NClause := [(35,false),(4,true),(63,true),(68,true),(73,false),(78,false),(83,false),(87,false)]
theorem inp_4488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4488 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4488 (by decide) v hb
def cl_4489 : CNF.NClause := [(35,false),(4,false),(63,false),(68,false),(73,true),(78,false),(83,false),(87,false)]
theorem inp_4489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4489 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4489 (by decide) v hb
def cl_4490 : CNF.NClause := [(35,false),(4,true),(63,false),(68,false),(73,true),(78,false),(83,false),(87,false)]
theorem inp_4490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4490 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4490 (by decide) v hb
def cl_4491 : CNF.NClause := [(35,false),(4,false),(63,true),(68,false),(73,true),(78,false),(83,false),(87,false)]
theorem inp_4491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4491 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4491 (by decide) v hb
def cl_4492 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,true),(78,false),(83,false),(87,false)]
theorem inp_4492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4492 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4492 (by decide) v hb
def cl_4493 : CNF.NClause := [(35,false),(4,false),(63,false),(68,true),(73,true),(78,false),(83,false),(87,false)]
theorem inp_4493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4493 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4493 (by decide) v hb
def cl_4494 : CNF.NClause := [(35,false),(4,true),(63,false),(68,true),(73,true),(78,false),(83,false),(87,false)]
theorem inp_4494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4494 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4494 (by decide) v hb
def cl_4495 : CNF.NClause := [(35,false),(4,false),(63,true),(68,true),(73,true),(78,false),(83,false),(87,false)]
theorem inp_4495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4495 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4495 (by decide) v hb
def cl_4496 : CNF.NClause := [(35,false),(4,true),(63,true),(68,true),(73,true),(78,false),(83,false),(87,false)]
theorem inp_4496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4496 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4496 (by decide) v hb
def cl_4497 : CNF.NClause := [(35,false),(4,false),(63,false),(68,false),(73,false),(78,true),(83,false),(87,false)]
theorem inp_4497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4497 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4497 (by decide) v hb
def cl_4498 : CNF.NClause := [(35,false),(4,true),(63,false),(68,false),(73,false),(78,true),(83,false),(87,false)]
theorem inp_4498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4498 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4498 (by decide) v hb
def cl_4499 : CNF.NClause := [(35,false),(4,false),(63,true),(68,false),(73,false),(78,true),(83,false),(87,false)]
theorem inp_4499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4499 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4499 (by decide) v hb
def cl_4500 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,false),(78,true),(83,false),(87,false)]
theorem inp_4500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4500 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4500 (by decide) v hb
def cl_4501 : CNF.NClause := [(35,false),(4,false),(63,false),(68,true),(73,false),(78,true),(83,false),(87,false)]
theorem inp_4501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4501 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4501 (by decide) v hb
def cl_4502 : CNF.NClause := [(35,false),(4,true),(63,false),(68,true),(73,false),(78,true),(83,false),(87,false)]
theorem inp_4502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4502 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4502 (by decide) v hb
def cl_4503 : CNF.NClause := [(35,false),(4,false),(63,true),(68,true),(73,false),(78,true),(83,false),(87,false)]
theorem inp_4503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4503 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4503 (by decide) v hb
def cl_4504 : CNF.NClause := [(35,false),(4,true),(63,true),(68,true),(73,false),(78,true),(83,false),(87,false)]
theorem inp_4504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4504 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4504 (by decide) v hb
def cl_4505 : CNF.NClause := [(35,false),(4,false),(63,false),(68,false),(73,true),(78,true),(83,false),(87,false)]
theorem inp_4505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4505 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4505 (by decide) v hb
def cl_4506 : CNF.NClause := [(35,false),(4,true),(63,false),(68,false),(73,true),(78,true),(83,false),(87,false)]
theorem inp_4506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4506 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4506 (by decide) v hb
def cl_4507 : CNF.NClause := [(35,false),(4,false),(63,true),(68,false),(73,true),(78,true),(83,false),(87,false)]
theorem inp_4507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4507 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4507 (by decide) v hb
def cl_4508 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,true),(78,true),(83,false),(87,false)]
theorem inp_4508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4508 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4508 (by decide) v hb
def cl_4509 : CNF.NClause := [(35,false),(4,false),(63,false),(68,true),(73,true),(78,true),(83,false),(87,false)]
theorem inp_4509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4509 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4509 (by decide) v hb
def cl_4510 : CNF.NClause := [(35,false),(4,true),(63,false),(68,true),(73,true),(78,true),(83,false),(87,false)]
theorem inp_4510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4510 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4510 (by decide) v hb
def cl_4511 : CNF.NClause := [(35,false),(4,false),(63,true),(68,true),(73,true),(78,true),(83,false),(87,false)]
theorem inp_4511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4511 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4511 (by decide) v hb
def cl_4512 : CNF.NClause := [(35,false),(4,true),(63,true),(68,true),(73,true),(78,true),(83,false),(87,false)]
theorem inp_4512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4512 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4512 (by decide) v hb
def cl_4513 : CNF.NClause := [(35,false),(4,false),(63,false),(68,false),(73,false),(78,false),(83,true),(87,false)]
theorem inp_4513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4513 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4513 (by decide) v hb
def cl_4514 : CNF.NClause := [(35,false),(4,true),(63,false),(68,false),(73,false),(78,false),(83,true),(87,false)]
theorem inp_4514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4514 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4514 (by decide) v hb
def cl_4515 : CNF.NClause := [(35,false),(4,false),(63,true),(68,false),(73,false),(78,false),(83,true),(87,false)]
theorem inp_4515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4515 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4515 (by decide) v hb
def cl_4516 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,false),(78,false),(83,true),(87,false)]
theorem inp_4516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4516 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4516 (by decide) v hb
def cl_4517 : CNF.NClause := [(35,false),(4,false),(63,false),(68,true),(73,false),(78,false),(83,true),(87,false)]
theorem inp_4517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4517 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4517 (by decide) v hb
def cl_4518 : CNF.NClause := [(35,false),(4,true),(63,false),(68,true),(73,false),(78,false),(83,true),(87,false)]
theorem inp_4518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4518 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4518 (by decide) v hb
def cl_4519 : CNF.NClause := [(35,false),(4,false),(63,true),(68,true),(73,false),(78,false),(83,true),(87,false)]
theorem inp_4519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4519 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4519 (by decide) v hb
def cl_4520 : CNF.NClause := [(35,false),(4,true),(63,true),(68,true),(73,false),(78,false),(83,true),(87,false)]
theorem inp_4520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4520 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4520 (by decide) v hb
def cl_4521 : CNF.NClause := [(35,false),(4,false),(63,false),(68,false),(73,true),(78,false),(83,true),(87,false)]
theorem inp_4521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4521 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4521 (by decide) v hb
def cl_4522 : CNF.NClause := [(35,false),(4,true),(63,false),(68,false),(73,true),(78,false),(83,true),(87,false)]
theorem inp_4522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4522 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4522 (by decide) v hb
def cl_4523 : CNF.NClause := [(35,false),(4,false),(63,true),(68,false),(73,true),(78,false),(83,true),(87,false)]
theorem inp_4523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4523 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4523 (by decide) v hb
def cl_4524 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,true),(78,false),(83,true),(87,false)]
theorem inp_4524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4524 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4524 (by decide) v hb
def cl_4525 : CNF.NClause := [(35,false),(4,false),(63,false),(68,true),(73,true),(78,false),(83,true),(87,false)]
theorem inp_4525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4525 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4525 (by decide) v hb
def cl_4526 : CNF.NClause := [(35,false),(4,true),(63,false),(68,true),(73,true),(78,false),(83,true),(87,false)]
theorem inp_4526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4526 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4526 (by decide) v hb
def cl_4527 : CNF.NClause := [(35,false),(4,false),(63,true),(68,true),(73,true),(78,false),(83,true),(87,false)]
theorem inp_4527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4527 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4527 (by decide) v hb
def cl_4528 : CNF.NClause := [(35,false),(4,true),(63,true),(68,true),(73,true),(78,false),(83,true),(87,false)]
theorem inp_4528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4528 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4528 (by decide) v hb
def cl_4529 : CNF.NClause := [(35,false),(4,false),(63,false),(68,false),(73,false),(78,true),(83,true),(87,false)]
theorem inp_4529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4529 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4529 (by decide) v hb
def cl_4530 : CNF.NClause := [(35,false),(4,true),(63,false),(68,false),(73,false),(78,true),(83,true),(87,false)]
theorem inp_4530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4530 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4530 (by decide) v hb
def cl_4531 : CNF.NClause := [(35,false),(4,false),(63,true),(68,false),(73,false),(78,true),(83,true),(87,false)]
theorem inp_4531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4531 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4531 (by decide) v hb
def cl_4532 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,false),(78,true),(83,true),(87,false)]
theorem inp_4532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4532 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4532 (by decide) v hb
def cl_4533 : CNF.NClause := [(35,false),(4,false),(63,false),(68,true),(73,false),(78,true),(83,true),(87,false)]
theorem inp_4533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4533 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4533 (by decide) v hb
end Percolation.NReplay
