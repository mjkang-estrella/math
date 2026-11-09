import NInputs094
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_5512 : CNF.NClause := [(43,false),(12,true),(64,true),(68,true),(72,false),(81,false),(85,false),(91,false)]
theorem inp_5512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5512 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5512 (by decide) v hb
def cl_5513 : CNF.NClause := [(43,false),(12,false),(64,false),(68,false),(72,true),(81,false),(85,false),(91,false)]
theorem inp_5513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5513 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5513 (by decide) v hb
def cl_5514 : CNF.NClause := [(43,false),(12,true),(64,false),(68,false),(72,true),(81,false),(85,false),(91,false)]
theorem inp_5514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5514 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5514 (by decide) v hb
def cl_5515 : CNF.NClause := [(43,false),(12,false),(64,true),(68,false),(72,true),(81,false),(85,false),(91,false)]
theorem inp_5515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5515 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5515 (by decide) v hb
def cl_5516 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(72,true),(81,false),(85,false),(91,false)]
theorem inp_5516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5516 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5516 (by decide) v hb
def cl_5517 : CNF.NClause := [(43,false),(12,false),(64,false),(68,true),(72,true),(81,false),(85,false),(91,false)]
theorem inp_5517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5517 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5517 (by decide) v hb
def cl_5518 : CNF.NClause := [(43,false),(12,true),(64,false),(68,true),(72,true),(81,false),(85,false),(91,false)]
theorem inp_5518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5518 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5518 (by decide) v hb
def cl_5519 : CNF.NClause := [(43,false),(12,false),(64,true),(68,true),(72,true),(81,false),(85,false),(91,false)]
theorem inp_5519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5519 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5519 (by decide) v hb
def cl_5520 : CNF.NClause := [(43,false),(12,true),(64,true),(68,true),(72,true),(81,false),(85,false),(91,false)]
theorem inp_5520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5520 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5520 (by decide) v hb
def cl_5521 : CNF.NClause := [(43,false),(12,false),(64,false),(68,false),(72,false),(81,true),(85,false),(91,false)]
theorem inp_5521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5521 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5521 (by decide) v hb
def cl_5522 : CNF.NClause := [(43,false),(12,true),(64,false),(68,false),(72,false),(81,true),(85,false),(91,false)]
theorem inp_5522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5522 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5522 (by decide) v hb
def cl_5523 : CNF.NClause := [(43,false),(12,false),(64,true),(68,false),(72,false),(81,true),(85,false),(91,false)]
theorem inp_5523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5523 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5523 (by decide) v hb
def cl_5524 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(72,false),(81,true),(85,false),(91,false)]
theorem inp_5524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5524 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5524 (by decide) v hb
def cl_5525 : CNF.NClause := [(43,false),(12,false),(64,false),(68,true),(72,false),(81,true),(85,false),(91,false)]
theorem inp_5525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5525 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5525 (by decide) v hb
def cl_5526 : CNF.NClause := [(43,false),(12,true),(64,false),(68,true),(72,false),(81,true),(85,false),(91,false)]
theorem inp_5526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5526 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5526 (by decide) v hb
def cl_5527 : CNF.NClause := [(43,false),(12,false),(64,true),(68,true),(72,false),(81,true),(85,false),(91,false)]
theorem inp_5527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5527 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5527 (by decide) v hb
def cl_5528 : CNF.NClause := [(43,false),(12,true),(64,true),(68,true),(72,false),(81,true),(85,false),(91,false)]
theorem inp_5528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5528 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5528 (by decide) v hb
def cl_5529 : CNF.NClause := [(43,false),(12,false),(64,false),(68,false),(72,true),(81,true),(85,false),(91,false)]
theorem inp_5529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5529 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5529 (by decide) v hb
def cl_5530 : CNF.NClause := [(43,false),(12,true),(64,false),(68,false),(72,true),(81,true),(85,false),(91,false)]
theorem inp_5530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5530 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5530 (by decide) v hb
def cl_5531 : CNF.NClause := [(43,false),(12,false),(64,true),(68,false),(72,true),(81,true),(85,false),(91,false)]
theorem inp_5531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5531 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5531 (by decide) v hb
def cl_5532 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(72,true),(81,true),(85,false),(91,false)]
theorem inp_5532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5532 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5532 (by decide) v hb
def cl_5533 : CNF.NClause := [(43,false),(12,false),(64,false),(68,true),(72,true),(81,true),(85,false),(91,false)]
theorem inp_5533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5533 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5533 (by decide) v hb
def cl_5534 : CNF.NClause := [(43,false),(12,true),(64,false),(68,true),(72,true),(81,true),(85,false),(91,false)]
theorem inp_5534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5534 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5534 (by decide) v hb
def cl_5535 : CNF.NClause := [(43,false),(12,false),(64,true),(68,true),(72,true),(81,true),(85,false),(91,false)]
theorem inp_5535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5535 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5535 (by decide) v hb
def cl_5536 : CNF.NClause := [(43,false),(12,true),(64,true),(68,true),(72,true),(81,true),(85,false),(91,false)]
theorem inp_5536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5536 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5536 (by decide) v hb
def cl_5537 : CNF.NClause := [(43,false),(12,false),(64,false),(68,false),(72,false),(81,false),(85,true),(91,false)]
theorem inp_5537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5537 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5537 (by decide) v hb
def cl_5538 : CNF.NClause := [(43,false),(12,true),(64,false),(68,false),(72,false),(81,false),(85,true),(91,false)]
theorem inp_5538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5538 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5538 (by decide) v hb
def cl_5539 : CNF.NClause := [(43,false),(12,false),(64,true),(68,false),(72,false),(81,false),(85,true),(91,false)]
theorem inp_5539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5539 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5539 (by decide) v hb
def cl_5540 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(72,false),(81,false),(85,true),(91,false)]
theorem inp_5540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5540 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5540 (by decide) v hb
def cl_5541 : CNF.NClause := [(43,false),(12,false),(64,false),(68,true),(72,false),(81,false),(85,true),(91,false)]
theorem inp_5541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5541 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5541 (by decide) v hb
def cl_5542 : CNF.NClause := [(43,false),(12,true),(64,false),(68,true),(72,false),(81,false),(85,true),(91,false)]
theorem inp_5542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5542 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5542 (by decide) v hb
def cl_5543 : CNF.NClause := [(43,false),(12,false),(64,true),(68,true),(72,false),(81,false),(85,true),(91,false)]
theorem inp_5543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5543 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5543 (by decide) v hb
def cl_5544 : CNF.NClause := [(43,false),(12,true),(64,true),(68,true),(72,false),(81,false),(85,true),(91,false)]
theorem inp_5544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5544 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5544 (by decide) v hb
def cl_5545 : CNF.NClause := [(43,false),(12,false),(64,false),(68,false),(72,true),(81,false),(85,true),(91,false)]
theorem inp_5545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5545 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5545 (by decide) v hb
def cl_5546 : CNF.NClause := [(43,false),(12,true),(64,false),(68,false),(72,true),(81,false),(85,true),(91,false)]
theorem inp_5546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5546 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5546 (by decide) v hb
def cl_5547 : CNF.NClause := [(43,false),(12,false),(64,true),(68,false),(72,true),(81,false),(85,true),(91,false)]
theorem inp_5547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5547 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5547 (by decide) v hb
def cl_5548 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(72,true),(81,false),(85,true),(91,false)]
theorem inp_5548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5548 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5548 (by decide) v hb
def cl_5549 : CNF.NClause := [(43,false),(12,false),(64,false),(68,true),(72,true),(81,false),(85,true),(91,false)]
theorem inp_5549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5549 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5549 (by decide) v hb
def cl_5550 : CNF.NClause := [(43,false),(12,true),(64,false),(68,true),(72,true),(81,false),(85,true),(91,false)]
theorem inp_5550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5550 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5550 (by decide) v hb
def cl_5551 : CNF.NClause := [(43,false),(12,false),(64,true),(68,true),(72,true),(81,false),(85,true),(91,false)]
theorem inp_5551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5551 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5551 (by decide) v hb
def cl_5552 : CNF.NClause := [(43,false),(12,true),(64,true),(68,true),(72,true),(81,false),(85,true),(91,false)]
theorem inp_5552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5552 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5552 (by decide) v hb
def cl_5553 : CNF.NClause := [(43,false),(12,false),(64,false),(68,false),(72,false),(81,true),(85,true),(91,false)]
theorem inp_5553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5553 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5553 (by decide) v hb
def cl_5554 : CNF.NClause := [(43,false),(12,true),(64,false),(68,false),(72,false),(81,true),(85,true),(91,false)]
theorem inp_5554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5554 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5554 (by decide) v hb
def cl_5555 : CNF.NClause := [(43,false),(12,false),(64,true),(68,false),(72,false),(81,true),(85,true),(91,false)]
theorem inp_5555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5555 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5555 (by decide) v hb
def cl_5556 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(72,false),(81,true),(85,true),(91,false)]
theorem inp_5556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5556 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5556 (by decide) v hb
def cl_5557 : CNF.NClause := [(43,false),(12,false),(64,false),(68,true),(72,false),(81,true),(85,true),(91,false)]
theorem inp_5557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5557 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5557 (by decide) v hb
def cl_5558 : CNF.NClause := [(43,false),(12,true),(64,false),(68,true),(72,false),(81,true),(85,true),(91,false)]
theorem inp_5558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5558 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5558 (by decide) v hb
def cl_5559 : CNF.NClause := [(43,false),(12,false),(64,true),(68,true),(72,false),(81,true),(85,true),(91,false)]
theorem inp_5559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5559 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5559 (by decide) v hb
def cl_5560 : CNF.NClause := [(43,false),(12,true),(64,true),(68,true),(72,false),(81,true),(85,true),(91,false)]
theorem inp_5560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5560 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5560 (by decide) v hb
def cl_5561 : CNF.NClause := [(43,false),(12,false),(64,false),(68,false),(72,true),(81,true),(85,true),(91,false)]
theorem inp_5561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5561 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5561 (by decide) v hb
end Percolation.NReplay
