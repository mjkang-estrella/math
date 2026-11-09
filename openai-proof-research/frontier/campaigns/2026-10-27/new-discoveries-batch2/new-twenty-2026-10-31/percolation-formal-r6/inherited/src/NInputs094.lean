import NInputs093
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_5455 : CNF.NClause := [(42,false),(11,false),(66,true),(69,true),(72,true),(80,false),(83,false),(90,true)]
theorem inp_5455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5455 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5455 (by decide) v hb
def cl_5456 : CNF.NClause := [(42,false),(11,true),(66,true),(69,true),(72,true),(80,false),(83,false),(90,true)]
theorem inp_5456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5456 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5456 (by decide) v hb
def cl_5457 : CNF.NClause := [(42,false),(11,false),(66,false),(69,false),(72,false),(80,true),(83,false),(90,true)]
theorem inp_5457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5457 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5457 (by decide) v hb
def cl_5458 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,false),(80,true),(83,false),(90,true)]
theorem inp_5458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5458 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5458 (by decide) v hb
def cl_5459 : CNF.NClause := [(42,false),(11,false),(66,true),(69,false),(72,false),(80,true),(83,false),(90,true)]
theorem inp_5459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5459 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5459 (by decide) v hb
def cl_5460 : CNF.NClause := [(42,false),(11,true),(66,true),(69,false),(72,false),(80,true),(83,false),(90,true)]
theorem inp_5460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5460 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5460 (by decide) v hb
def cl_5461 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(72,false),(80,true),(83,false),(90,true)]
theorem inp_5461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5461 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5461 (by decide) v hb
def cl_5462 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,false),(80,true),(83,false),(90,true)]
theorem inp_5462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5462 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5462 (by decide) v hb
def cl_5464 : CNF.NClause := [(42,false),(11,true),(66,true),(69,true),(72,false),(80,true),(83,false),(90,true)]
theorem inp_5464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5464 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5464 (by decide) v hb
def cl_5465 : CNF.NClause := [(42,false),(11,false),(66,false),(69,false),(72,true),(80,true),(83,false),(90,true)]
theorem inp_5465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5465 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5465 (by decide) v hb
def cl_5466 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,true),(80,true),(83,false),(90,true)]
theorem inp_5466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5466 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5466 (by decide) v hb
def cl_5467 : CNF.NClause := [(42,false),(11,false),(66,true),(69,false),(72,true),(80,true),(83,false),(90,true)]
theorem inp_5467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5467 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5467 (by decide) v hb
def cl_5468 : CNF.NClause := [(42,false),(11,true),(66,true),(69,false),(72,true),(80,true),(83,false),(90,true)]
theorem inp_5468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5468 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5468 (by decide) v hb
def cl_5469 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(72,true),(80,true),(83,false),(90,true)]
theorem inp_5469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5469 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5469 (by decide) v hb
def cl_5470 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,true),(80,true),(83,false),(90,true)]
theorem inp_5470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5470 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5470 (by decide) v hb
def cl_5472 : CNF.NClause := [(42,false),(11,true),(66,true),(69,true),(72,true),(80,true),(83,false),(90,true)]
theorem inp_5472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5472 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5472 (by decide) v hb
def cl_5473 : CNF.NClause := [(42,false),(11,false),(66,false),(69,false),(72,false),(80,false),(83,true),(90,true)]
theorem inp_5473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5473 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5473 (by decide) v hb
def cl_5474 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,false),(80,false),(83,true),(90,true)]
theorem inp_5474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5474 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5474 (by decide) v hb
def cl_5475 : CNF.NClause := [(42,false),(11,false),(66,true),(69,false),(72,false),(80,false),(83,true),(90,true)]
theorem inp_5475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5475 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5475 (by decide) v hb
def cl_5476 : CNF.NClause := [(42,false),(11,true),(66,true),(69,false),(72,false),(80,false),(83,true),(90,true)]
theorem inp_5476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5476 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5476 (by decide) v hb
def cl_5477 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(72,false),(80,false),(83,true),(90,true)]
theorem inp_5477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5477 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5477 (by decide) v hb
def cl_5478 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,false),(80,false),(83,true),(90,true)]
theorem inp_5478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5478 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5478 (by decide) v hb
def cl_5480 : CNF.NClause := [(42,false),(11,true),(66,true),(69,true),(72,false),(80,false),(83,true),(90,true)]
theorem inp_5480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5480 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5480 (by decide) v hb
def cl_5481 : CNF.NClause := [(42,false),(11,false),(66,false),(69,false),(72,true),(80,false),(83,true),(90,true)]
theorem inp_5481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5481 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5481 (by decide) v hb
def cl_5482 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,true),(80,false),(83,true),(90,true)]
theorem inp_5482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5482 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5482 (by decide) v hb
def cl_5483 : CNF.NClause := [(42,false),(11,false),(66,true),(69,false),(72,true),(80,false),(83,true),(90,true)]
theorem inp_5483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5483 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5483 (by decide) v hb
def cl_5484 : CNF.NClause := [(42,false),(11,true),(66,true),(69,false),(72,true),(80,false),(83,true),(90,true)]
theorem inp_5484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5484 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5484 (by decide) v hb
def cl_5485 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(72,true),(80,false),(83,true),(90,true)]
theorem inp_5485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5485 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5485 (by decide) v hb
def cl_5486 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,true),(80,false),(83,true),(90,true)]
theorem inp_5486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5486 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5486 (by decide) v hb
def cl_5487 : CNF.NClause := [(42,false),(11,false),(66,true),(69,true),(72,true),(80,false),(83,true),(90,true)]
theorem inp_5487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5487 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5487 (by decide) v hb
def cl_5488 : CNF.NClause := [(42,false),(11,true),(66,true),(69,true),(72,true),(80,false),(83,true),(90,true)]
theorem inp_5488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5488 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5488 (by decide) v hb
def cl_5489 : CNF.NClause := [(42,false),(11,false),(66,false),(69,false),(72,false),(80,true),(83,true),(90,true)]
theorem inp_5489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5489 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5489 (by decide) v hb
def cl_5490 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,false),(80,true),(83,true),(90,true)]
theorem inp_5490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5490 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5490 (by decide) v hb
def cl_5491 : CNF.NClause := [(42,false),(11,false),(66,true),(69,false),(72,false),(80,true),(83,true),(90,true)]
theorem inp_5491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5491 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5491 (by decide) v hb
def cl_5492 : CNF.NClause := [(42,false),(11,true),(66,true),(69,false),(72,false),(80,true),(83,true),(90,true)]
theorem inp_5492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5492 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5492 (by decide) v hb
def cl_5493 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(72,false),(80,true),(83,true),(90,true)]
theorem inp_5493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5493 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5493 (by decide) v hb
def cl_5494 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,false),(80,true),(83,true),(90,true)]
theorem inp_5494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5494 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5494 (by decide) v hb
def cl_5497 : CNF.NClause := [(42,false),(11,false),(66,false),(69,false),(72,true),(80,true),(83,true),(90,true)]
theorem inp_5497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5497 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5497 (by decide) v hb
def cl_5498 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,true),(80,true),(83,true),(90,true)]
theorem inp_5498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5498 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5498 (by decide) v hb
def cl_5500 : CNF.NClause := [(42,false),(11,true),(66,true),(69,false),(72,true),(80,true),(83,true),(90,true)]
theorem inp_5500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5500 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5500 (by decide) v hb
def cl_5501 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(72,true),(80,true),(83,true),(90,true)]
theorem inp_5501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5501 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5501 (by decide) v hb
def cl_5502 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,true),(80,true),(83,true),(90,true)]
theorem inp_5502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5502 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5502 (by decide) v hb
def cl_5504 : CNF.NClause := [(42,false),(11,true),(66,true),(69,true),(72,true),(80,true),(83,true),(90,true)]
theorem inp_5504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5504 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5504 (by decide) v hb
def cl_5505 : CNF.NClause := [(43,true),(12,false),(64,false),(68,false),(72,false),(81,false),(85,false),(91,false)]
theorem inp_5505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5505 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5505 (by decide) v hb
def cl_5506 : CNF.NClause := [(43,false),(12,true),(64,false),(68,false),(72,false),(81,false),(85,false),(91,false)]
theorem inp_5506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5506 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5506 (by decide) v hb
def cl_5507 : CNF.NClause := [(43,false),(12,false),(64,true),(68,false),(72,false),(81,false),(85,false),(91,false)]
theorem inp_5507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5507 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5507 (by decide) v hb
def cl_5508 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(72,false),(81,false),(85,false),(91,false)]
theorem inp_5508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5508 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5508 (by decide) v hb
def cl_5509 : CNF.NClause := [(43,false),(12,false),(64,false),(68,true),(72,false),(81,false),(85,false),(91,false)]
theorem inp_5509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5509 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5509 (by decide) v hb
def cl_5510 : CNF.NClause := [(43,false),(12,true),(64,false),(68,true),(72,false),(81,false),(85,false),(91,false)]
theorem inp_5510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5510 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5510 (by decide) v hb
def cl_5511 : CNF.NClause := [(43,false),(12,false),(64,true),(68,true),(72,false),(81,false),(85,false),(91,false)]
theorem inp_5511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5511 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) cl_5511 (by decide) v hb
end Percolation.NReplay
