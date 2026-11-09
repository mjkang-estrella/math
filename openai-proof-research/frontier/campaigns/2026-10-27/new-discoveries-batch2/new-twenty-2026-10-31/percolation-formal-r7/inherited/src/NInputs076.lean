import NInputs075
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_4534 : CNF.NClause := [(35,false),(4,true),(63,false),(68,true),(73,false),(78,true),(83,true),(87,false)]
theorem inp_4534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4534 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4534 (by decide) v hb
def cl_4535 : CNF.NClause := [(35,false),(4,false),(63,true),(68,true),(73,false),(78,true),(83,true),(87,false)]
theorem inp_4535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4535 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4535 (by decide) v hb
def cl_4536 : CNF.NClause := [(35,false),(4,true),(63,true),(68,true),(73,false),(78,true),(83,true),(87,false)]
theorem inp_4536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4536 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4536 (by decide) v hb
def cl_4537 : CNF.NClause := [(35,false),(4,false),(63,false),(68,false),(73,true),(78,true),(83,true),(87,false)]
theorem inp_4537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4537 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4537 (by decide) v hb
def cl_4538 : CNF.NClause := [(35,false),(4,true),(63,false),(68,false),(73,true),(78,true),(83,true),(87,false)]
theorem inp_4538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4538 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4538 (by decide) v hb
def cl_4539 : CNF.NClause := [(35,false),(4,false),(63,true),(68,false),(73,true),(78,true),(83,true),(87,false)]
theorem inp_4539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4539 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4539 (by decide) v hb
def cl_4540 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,true),(78,true),(83,true),(87,false)]
theorem inp_4540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4540 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4540 (by decide) v hb
def cl_4541 : CNF.NClause := [(35,false),(4,false),(63,false),(68,true),(73,true),(78,true),(83,true),(87,false)]
theorem inp_4541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4541 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4541 (by decide) v hb
def cl_4542 : CNF.NClause := [(35,false),(4,true),(63,false),(68,true),(73,true),(78,true),(83,true),(87,false)]
theorem inp_4542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4542 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4542 (by decide) v hb
def cl_4543 : CNF.NClause := [(35,false),(4,false),(63,true),(68,true),(73,true),(78,true),(83,true),(87,false)]
theorem inp_4543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4543 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4543 (by decide) v hb
def cl_4544 : CNF.NClause := [(35,false),(4,true),(63,true),(68,true),(73,true),(78,true),(83,true),(87,false)]
theorem inp_4544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4544 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4544 (by decide) v hb
def cl_4545 : CNF.NClause := [(35,false),(4,false),(63,false),(68,false),(73,false),(78,false),(83,false),(87,true)]
theorem inp_4545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4545 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4545 (by decide) v hb
def cl_4546 : CNF.NClause := [(35,false),(4,true),(63,false),(68,false),(73,false),(78,false),(83,false),(87,true)]
theorem inp_4546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4546 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4546 (by decide) v hb
def cl_4547 : CNF.NClause := [(35,false),(4,false),(63,true),(68,false),(73,false),(78,false),(83,false),(87,true)]
theorem inp_4547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4547 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4547 (by decide) v hb
def cl_4548 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,false),(78,false),(83,false),(87,true)]
theorem inp_4548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4548 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4548 (by decide) v hb
def cl_4549 : CNF.NClause := [(35,false),(4,false),(63,false),(68,true),(73,false),(78,false),(83,false),(87,true)]
theorem inp_4549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4549 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4549 (by decide) v hb
def cl_4550 : CNF.NClause := [(35,false),(4,true),(63,false),(68,true),(73,false),(78,false),(83,false),(87,true)]
theorem inp_4550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4550 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4550 (by decide) v hb
def cl_4551 : CNF.NClause := [(35,false),(4,false),(63,true),(68,true),(73,false),(78,false),(83,false),(87,true)]
theorem inp_4551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4551 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4551 (by decide) v hb
def cl_4552 : CNF.NClause := [(35,false),(4,true),(63,true),(68,true),(73,false),(78,false),(83,false),(87,true)]
theorem inp_4552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4552 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4552 (by decide) v hb
def cl_4553 : CNF.NClause := [(35,false),(4,false),(63,false),(68,false),(73,true),(78,false),(83,false),(87,true)]
theorem inp_4553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4553 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4553 (by decide) v hb
def cl_4554 : CNF.NClause := [(35,false),(4,true),(63,false),(68,false),(73,true),(78,false),(83,false),(87,true)]
theorem inp_4554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4554 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4554 (by decide) v hb
def cl_4555 : CNF.NClause := [(35,false),(4,false),(63,true),(68,false),(73,true),(78,false),(83,false),(87,true)]
theorem inp_4555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4555 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4555 (by decide) v hb
def cl_4556 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,true),(78,false),(83,false),(87,true)]
theorem inp_4556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4556 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4556 (by decide) v hb
def cl_4557 : CNF.NClause := [(35,false),(4,false),(63,false),(68,true),(73,true),(78,false),(83,false),(87,true)]
theorem inp_4557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4557 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4557 (by decide) v hb
def cl_4558 : CNF.NClause := [(35,false),(4,true),(63,false),(68,true),(73,true),(78,false),(83,false),(87,true)]
theorem inp_4558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4558 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4558 (by decide) v hb
def cl_4559 : CNF.NClause := [(35,false),(4,false),(63,true),(68,true),(73,true),(78,false),(83,false),(87,true)]
theorem inp_4559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4559 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4559 (by decide) v hb
def cl_4560 : CNF.NClause := [(35,false),(4,true),(63,true),(68,true),(73,true),(78,false),(83,false),(87,true)]
theorem inp_4560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4560 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4560 (by decide) v hb
def cl_4561 : CNF.NClause := [(35,false),(4,false),(63,false),(68,false),(73,false),(78,true),(83,false),(87,true)]
theorem inp_4561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4561 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4561 (by decide) v hb
def cl_4562 : CNF.NClause := [(35,false),(4,true),(63,false),(68,false),(73,false),(78,true),(83,false),(87,true)]
theorem inp_4562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4562 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4562 (by decide) v hb
def cl_4563 : CNF.NClause := [(35,false),(4,false),(63,true),(68,false),(73,false),(78,true),(83,false),(87,true)]
theorem inp_4563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4563 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4563 (by decide) v hb
def cl_4564 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,false),(78,true),(83,false),(87,true)]
theorem inp_4564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4564 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4564 (by decide) v hb
def cl_4565 : CNF.NClause := [(35,false),(4,false),(63,false),(68,true),(73,false),(78,true),(83,false),(87,true)]
theorem inp_4565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4565 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4565 (by decide) v hb
def cl_4566 : CNF.NClause := [(35,false),(4,true),(63,false),(68,true),(73,false),(78,true),(83,false),(87,true)]
theorem inp_4566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4566 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4566 (by decide) v hb
def cl_4567 : CNF.NClause := [(35,false),(4,false),(63,true),(68,true),(73,false),(78,true),(83,false),(87,true)]
theorem inp_4567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4567 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4567 (by decide) v hb
def cl_4568 : CNF.NClause := [(35,false),(4,true),(63,true),(68,true),(73,false),(78,true),(83,false),(87,true)]
theorem inp_4568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4568 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4568 (by decide) v hb
def cl_4569 : CNF.NClause := [(35,false),(4,false),(63,false),(68,false),(73,true),(78,true),(83,false),(87,true)]
theorem inp_4569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4569 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4569 (by decide) v hb
def cl_4570 : CNF.NClause := [(35,false),(4,true),(63,false),(68,false),(73,true),(78,true),(83,false),(87,true)]
theorem inp_4570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4570 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4570 (by decide) v hb
def cl_4571 : CNF.NClause := [(35,false),(4,false),(63,true),(68,false),(73,true),(78,true),(83,false),(87,true)]
theorem inp_4571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4571 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4571 (by decide) v hb
def cl_4572 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,true),(78,true),(83,false),(87,true)]
theorem inp_4572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4572 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4572 (by decide) v hb
def cl_4573 : CNF.NClause := [(35,false),(4,false),(63,false),(68,true),(73,true),(78,true),(83,false),(87,true)]
theorem inp_4573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4573 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4573 (by decide) v hb
def cl_4574 : CNF.NClause := [(35,false),(4,true),(63,false),(68,true),(73,true),(78,true),(83,false),(87,true)]
theorem inp_4574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4574 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4574 (by decide) v hb
def cl_4575 : CNF.NClause := [(35,false),(4,false),(63,true),(68,true),(73,true),(78,true),(83,false),(87,true)]
theorem inp_4575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4575 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4575 (by decide) v hb
def cl_4576 : CNF.NClause := [(35,false),(4,true),(63,true),(68,true),(73,true),(78,true),(83,false),(87,true)]
theorem inp_4576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4576 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4576 (by decide) v hb
def cl_4577 : CNF.NClause := [(35,false),(4,false),(63,false),(68,false),(73,false),(78,false),(83,true),(87,true)]
theorem inp_4577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4577 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4577 (by decide) v hb
def cl_4578 : CNF.NClause := [(35,false),(4,true),(63,false),(68,false),(73,false),(78,false),(83,true),(87,true)]
theorem inp_4578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4578 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4578 (by decide) v hb
def cl_4579 : CNF.NClause := [(35,false),(4,false),(63,true),(68,false),(73,false),(78,false),(83,true),(87,true)]
theorem inp_4579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4579 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4579 (by decide) v hb
def cl_4580 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,false),(78,false),(83,true),(87,true)]
theorem inp_4580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4580 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4580 (by decide) v hb
def cl_4581 : CNF.NClause := [(35,false),(4,false),(63,false),(68,true),(73,false),(78,false),(83,true),(87,true)]
theorem inp_4581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4581 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4581 (by decide) v hb
def cl_4582 : CNF.NClause := [(35,false),(4,true),(63,false),(68,true),(73,false),(78,false),(83,true),(87,true)]
theorem inp_4582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4582 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4582 (by decide) v hb
def cl_4583 : CNF.NClause := [(35,false),(4,false),(63,true),(68,true),(73,false),(78,false),(83,true),(87,true)]
theorem inp_4583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4583 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4583 (by decide) v hb
end Percolation.NReplay
