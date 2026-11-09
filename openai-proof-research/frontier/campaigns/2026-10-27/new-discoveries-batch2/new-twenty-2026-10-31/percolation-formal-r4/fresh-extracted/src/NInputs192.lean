import NInputs191
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_12510 : CNF.NClause := [(871,true),(877,true),(878,true),(884,true),(890,true),(894,false)]
theorem inp_12510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12510 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 13) (closed_mem 24 13) cl_12510 (by decide) v hb
def cl_12512 : CNF.NClause := [(871,true),(877,true),(878,true),(884,false),(890,true),(894,true)]
theorem inp_12512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12512 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 13) (closed_mem 24 13) cl_12512 (by decide) v hb
def cl_12513 : CNF.NClause := [(871,true),(877,true),(878,false),(884,true),(890,true),(894,true)]
theorem inp_12513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12513 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 13) (closed_mem 24 13) cl_12513 (by decide) v hb
def cl_12514 : CNF.NClause := [(871,true),(877,false),(878,true),(884,true),(890,true),(894,true)]
theorem inp_12514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12514 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 13) (closed_mem 24 13) cl_12514 (by decide) v hb
def cl_12515 : CNF.NClause := [(871,false),(877,true),(878,true),(884,true),(890,true),(894,true)]
theorem inp_12515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12515 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 13) (closed_mem 24 13) cl_12515 (by decide) v hb
def cl_12517 : CNF.NClause := [(869,true),(876,true),(878,true),(885,true),(892,false),(895,true)]
theorem inp_12517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12517 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 14) (closed_mem 24 14) cl_12517 (by decide) v hb
def cl_12524 : CNF.NClause := [(883,true),(884,true),(885,true),(886,false),(887,true),(898,true)]
theorem inp_12524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12524 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 15) (closed_mem 24 15) cl_12524 (by decide) v hb
def cl_12525 : CNF.NClause := [(883,true),(884,true),(885,false),(886,true),(887,true),(898,true)]
theorem inp_12525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12525 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 15) (closed_mem 24 15) cl_12525 (by decide) v hb
def cl_12526 : CNF.NClause := [(883,true),(884,false),(885,true),(886,true),(887,true),(898,true)]
theorem inp_12526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12526 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 15) (closed_mem 24 15) cl_12526 (by decide) v hb
def cl_12527 : CNF.NClause := [(883,false),(884,true),(885,true),(886,true),(887,true),(898,true)]
theorem inp_12527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12527 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 15) (closed_mem 24 15) cl_12527 (by decide) v hb
def cl_12529 : CNF.NClause := [(872,true),(874,true),(881,true),(883,true),(890,false),(895,true)]
theorem inp_12529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12529 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 16) (closed_mem 24 16) cl_12529 (by decide) v hb
def cl_12530 : CNF.NClause := [(872,true),(874,true),(881,true),(883,false),(890,true),(895,true)]
theorem inp_12530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12530 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 16) (closed_mem 24 16) cl_12530 (by decide) v hb
def cl_12531 : CNF.NClause := [(872,true),(874,true),(881,false),(883,true),(890,true),(895,true)]
theorem inp_12531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12531 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 16) (closed_mem 24 16) cl_12531 (by decide) v hb
def cl_12532 : CNF.NClause := [(872,true),(874,false),(881,true),(883,true),(890,true),(895,true)]
theorem inp_12532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12532 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 16) (closed_mem 24 16) cl_12532 (by decide) v hb
def cl_12533 : CNF.NClause := [(872,false),(874,true),(881,true),(883,true),(890,true),(895,true)]
theorem inp_12533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12533 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 16) (closed_mem 24 16) cl_12533 (by decide) v hb
def cl_12534 : CNF.NClause := [(870,true),(876,true),(882,true),(883,true),(889,true),(894,false)]
theorem inp_12534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12534 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 17) (closed_mem 24 17) cl_12534 (by decide) v hb
def cl_12535 : CNF.NClause := [(870,true),(876,true),(882,true),(883,true),(889,false),(894,true)]
theorem inp_12535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12535 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 17) (closed_mem 24 17) cl_12535 (by decide) v hb
def cl_12536 : CNF.NClause := [(870,true),(876,true),(882,true),(883,false),(889,true),(894,true)]
theorem inp_12536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12536 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 17) (closed_mem 24 17) cl_12536 (by decide) v hb
def cl_12537 : CNF.NClause := [(870,true),(876,true),(882,false),(883,true),(889,true),(894,true)]
theorem inp_12537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12537 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 17) (closed_mem 24 17) cl_12537 (by decide) v hb
def cl_12538 : CNF.NClause := [(870,true),(876,false),(882,true),(883,true),(889,true),(894,true)]
theorem inp_12538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12538 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 17) (closed_mem 24 17) cl_12538 (by decide) v hb
def cl_12541 : CNF.NClause := [(871,true),(875,true),(879,true),(883,true),(892,false),(897,true)]
theorem inp_12541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12541 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 18) (closed_mem 24 18) cl_12541 (by decide) v hb
def cl_12548 : CNF.NClause := [(869,true),(877,true),(880,true),(883,false),(891,true),(896,true)]
theorem inp_12548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12548 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 19) (closed_mem 24 19) cl_12548 (by decide) v hb
def cl_12550 : CNF.NClause := [(869,true),(877,false),(880,true),(883,true),(891,true),(896,true)]
theorem inp_12550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12550 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 19) (closed_mem 24 19) cl_12550 (by decide) v hb
def cl_12551 : CNF.NClause := [(869,false),(877,true),(880,true),(883,true),(891,true),(896,true)]
theorem inp_12551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12551 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 19) (closed_mem 24 19) cl_12551 (by decide) v hb
def cl_12553 : CNF.NClause := [(873,true),(874,true),(875,true),(876,true),(877,false),(898,true)]
theorem inp_12553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12553 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 20) (closed_mem 24 20) cl_12553 (by decide) v hb
def cl_12554 : CNF.NClause := [(873,true),(874,true),(875,true),(876,false),(877,true),(898,true)]
theorem inp_12554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12554 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 20) (closed_mem 24 20) cl_12554 (by decide) v hb
def cl_12555 : CNF.NClause := [(873,true),(874,true),(875,false),(876,true),(877,true),(898,true)]
theorem inp_12555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12555 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 20) (closed_mem 24 20) cl_12555 (by decide) v hb
def cl_12556 : CNF.NClause := [(873,true),(874,false),(875,true),(876,true),(877,true),(898,true)]
theorem inp_12556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12556 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 20) (closed_mem 24 20) cl_12556 (by decide) v hb
def cl_12557 : CNF.NClause := [(873,false),(874,true),(875,true),(876,true),(877,true),(898,true)]
theorem inp_12557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12557 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 20) (closed_mem 24 20) cl_12557 (by decide) v hb
def cl_12559 : CNF.NClause := [(872,true),(873,true),(879,true),(885,true),(891,false),(894,true)]
theorem inp_12559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12559 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 21) (closed_mem 24 21) cl_12559 (by decide) v hb
def cl_12560 : CNF.NClause := [(872,true),(873,true),(879,true),(885,false),(891,true),(894,true)]
theorem inp_12560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12560 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 21) (closed_mem 24 21) cl_12560 (by decide) v hb
def cl_12561 : CNF.NClause := [(872,true),(873,true),(879,false),(885,true),(891,true),(894,true)]
theorem inp_12561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12561 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 21) (closed_mem 24 21) cl_12561 (by decide) v hb
def cl_12565 : CNF.NClause := [(870,true),(873,true),(881,true),(884,true),(892,false),(896,true)]
theorem inp_12565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12565 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 22) (closed_mem 24 22) cl_12565 (by decide) v hb
def cl_12570 : CNF.NClause := [(871,true),(873,true),(880,true),(887,true),(889,true),(895,false)]
theorem inp_12570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12570 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 23) (closed_mem 24 23) cl_12570 (by decide) v hb
def cl_12576 : CNF.NClause := [(869,true),(873,true),(882,true),(886,true),(890,true),(897,false)]
theorem inp_12576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12576 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 24) (closed_mem 24 24) cl_12576 (by decide) v hb
def cl_12577 : CNF.NClause := [(869,true),(873,true),(882,true),(886,true),(890,false),(897,true)]
theorem inp_12577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12577 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 24) (closed_mem 24 24) cl_12577 (by decide) v hb
def cl_12579 : CNF.NClause := [(869,true),(873,true),(882,false),(886,true),(890,true),(897,true)]
theorem inp_12579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12579 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 24) (closed_mem 24 24) cl_12579 (by decide) v hb
def cl_12580 : CNF.NClause := [(869,true),(873,false),(882,true),(886,true),(890,true),(897,true)]
theorem inp_12580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12580 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 24) (closed_mem 24 24) cl_12580 (by decide) v hb
def cl_12581 : CNF.NClause := [(869,false),(873,true),(882,true),(886,true),(890,true),(897,true)]
theorem inp_12581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12581 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 24) (closed_mem 24 24) cl_12581 (by decide) v hb
def cl_12583 : CNF.NClause := [(868,true),(869,true),(870,true),(871,true),(872,false),(898,true)]
theorem inp_12583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12583 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 25) (closed_mem 24 25) cl_12583 (by decide) v hb
def cl_12584 : CNF.NClause := [(868,true),(869,true),(870,true),(871,false),(872,true),(898,true)]
theorem inp_12584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12584 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 25) (closed_mem 24 25) cl_12584 (by decide) v hb
def cl_12585 : CNF.NClause := [(868,true),(869,true),(870,false),(871,true),(872,true),(898,true)]
theorem inp_12585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12585 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 25) (closed_mem 24 25) cl_12585 (by decide) v hb
def cl_12586 : CNF.NClause := [(868,true),(869,false),(870,true),(871,true),(872,true),(898,true)]
theorem inp_12586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12586 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 25) (closed_mem 24 25) cl_12586 (by decide) v hb
def cl_12589 : CNF.NClause := [(868,true),(877,true),(881,true),(885,true),(889,false),(897,true)]
theorem inp_12589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12589 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 26) (closed_mem 24 26) cl_12589 (by decide) v hb
def cl_12590 : CNF.NClause := [(868,true),(877,true),(881,true),(885,false),(889,true),(897,true)]
theorem inp_12590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12590 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 26) (closed_mem 24 26) cl_12590 (by decide) v hb
def cl_12592 : CNF.NClause := [(868,true),(877,false),(881,true),(885,true),(889,true),(897,true)]
theorem inp_12592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12592 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 26) (closed_mem 24 26) cl_12592 (by decide) v hb
def cl_12594 : CNF.NClause := [(868,true),(875,true),(882,true),(884,true),(891,true),(895,false)]
theorem inp_12594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12594 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 27) (closed_mem 24 27) cl_12594 (by decide) v hb
def cl_12596 : CNF.NClause := [(868,true),(875,true),(882,true),(884,false),(891,true),(895,true)]
theorem inp_12596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12596 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 27) (closed_mem 24 27) cl_12596 (by decide) v hb
def cl_12597 : CNF.NClause := [(868,true),(875,true),(882,false),(884,true),(891,true),(895,true)]
theorem inp_12597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12597 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 27) (closed_mem 24 27) cl_12597 (by decide) v hb
def cl_12600 : CNF.NClause := [(868,true),(876,true),(879,true),(887,true),(890,true),(896,false)]
theorem inp_12600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12600 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 28) (closed_mem 24 28) cl_12600 (by decide) v hb
end Percolation.NReplay
