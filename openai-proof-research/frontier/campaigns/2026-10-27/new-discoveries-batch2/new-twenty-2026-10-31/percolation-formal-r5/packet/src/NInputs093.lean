import NInputs092
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_5405 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(72,true),(80,true),(83,false),(90,false)]
theorem inp_5405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5405 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5405 (by decide) v hb
def cl_5406 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,true),(80,true),(83,false),(90,false)]
theorem inp_5406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5406 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5406 v hb
def cl_5407 : CNF.NClause := [(42,false),(11,false),(66,true),(69,true),(72,true),(80,true),(83,false),(90,false)]
theorem inp_5407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5407 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5407 (by decide) v hb
def cl_5408 : CNF.NClause := [(42,false),(11,true),(66,true),(69,true),(72,true),(80,true),(83,false),(90,false)]
theorem inp_5408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5408 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5408 (by decide) v hb
def cl_5409 : CNF.NClause := [(42,false),(11,false),(66,false),(69,false),(72,false),(80,false),(83,true),(90,false)]
theorem inp_5409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5409 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5409 v hb
def cl_5410 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,false),(80,false),(83,true),(90,false)]
theorem inp_5410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5410 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5410 v hb
def cl_5411 : CNF.NClause := [(42,false),(11,false),(66,true),(69,false),(72,false),(80,false),(83,true),(90,false)]
theorem inp_5411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5411 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5411 (by decide) v hb
def cl_5412 : CNF.NClause := [(42,false),(11,true),(66,true),(69,false),(72,false),(80,false),(83,true),(90,false)]
theorem inp_5412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5412 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5412 (by decide) v hb
def cl_5413 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(72,false),(80,false),(83,true),(90,false)]
theorem inp_5413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5413 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5413 v hb
def cl_5414 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,false),(80,false),(83,true),(90,false)]
theorem inp_5414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5414 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5414 v hb
def cl_5415 : CNF.NClause := [(42,false),(11,false),(66,true),(69,true),(72,false),(80,false),(83,true),(90,false)]
theorem inp_5415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5415 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5415 (by decide) v hb
def cl_5416 : CNF.NClause := [(42,false),(11,true),(66,true),(69,true),(72,false),(80,false),(83,true),(90,false)]
theorem inp_5416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5416 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5416 (by decide) v hb
def cl_5417 : CNF.NClause := [(42,false),(11,false),(66,false),(69,false),(72,true),(80,false),(83,true),(90,false)]
theorem inp_5417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5417 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5417 (by decide) v hb
def cl_5418 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,true),(80,false),(83,true),(90,false)]
theorem inp_5418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5418 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5418 v hb
def cl_5419 : CNF.NClause := [(42,false),(11,false),(66,true),(69,false),(72,true),(80,false),(83,true),(90,false)]
theorem inp_5419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5419 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5419 (by decide) v hb
def cl_5420 : CNF.NClause := [(42,false),(11,true),(66,true),(69,false),(72,true),(80,false),(83,true),(90,false)]
theorem inp_5420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5420 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5420 (by decide) v hb
def cl_5421 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(72,true),(80,false),(83,true),(90,false)]
theorem inp_5421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5421 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5421 (by decide) v hb
def cl_5422 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,true),(80,false),(83,true),(90,false)]
theorem inp_5422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5422 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5422 v hb
def cl_5423 : CNF.NClause := [(42,false),(11,false),(66,true),(69,true),(72,true),(80,false),(83,true),(90,false)]
theorem inp_5423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5423 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5423 (by decide) v hb
def cl_5424 : CNF.NClause := [(42,false),(11,true),(66,true),(69,true),(72,true),(80,false),(83,true),(90,false)]
theorem inp_5424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5424 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5424 (by decide) v hb
def cl_5425 : CNF.NClause := [(42,false),(11,false),(66,false),(69,false),(72,false),(80,true),(83,true),(90,false)]
theorem inp_5425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5425 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5425 (by decide) v hb
def cl_5426 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,false),(80,true),(83,true),(90,false)]
theorem inp_5426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5426 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5426 v hb
def cl_5427 : CNF.NClause := [(42,false),(11,false),(66,true),(69,false),(72,false),(80,true),(83,true),(90,false)]
theorem inp_5427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5427 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5427 (by decide) v hb
def cl_5428 : CNF.NClause := [(42,false),(11,true),(66,true),(69,false),(72,false),(80,true),(83,true),(90,false)]
theorem inp_5428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5428 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5428 (by decide) v hb
def cl_5429 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(72,false),(80,true),(83,true),(90,false)]
theorem inp_5429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5429 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5429 (by decide) v hb
def cl_5430 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,false),(80,true),(83,true),(90,false)]
theorem inp_5430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5430 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5430 v hb
def cl_5431 : CNF.NClause := [(42,false),(11,false),(66,true),(69,true),(72,false),(80,true),(83,true),(90,false)]
theorem inp_5431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5431 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5431 (by decide) v hb
def cl_5432 : CNF.NClause := [(42,false),(11,true),(66,true),(69,true),(72,false),(80,true),(83,true),(90,false)]
theorem inp_5432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5432 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5432 (by decide) v hb
def cl_5433 : CNF.NClause := [(42,false),(11,false),(66,false),(69,false),(72,true),(80,true),(83,true),(90,false)]
theorem inp_5433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5433 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5433 (by decide) v hb
def cl_5434 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,true),(80,true),(83,true),(90,false)]
theorem inp_5434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5434 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5434 v hb
def cl_5435 : CNF.NClause := [(42,false),(11,false),(66,true),(69,false),(72,true),(80,true),(83,true),(90,false)]
theorem inp_5435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5435 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5435 (by decide) v hb
def cl_5436 : CNF.NClause := [(42,false),(11,true),(66,true),(69,false),(72,true),(80,true),(83,true),(90,false)]
theorem inp_5436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5436 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5436 (by decide) v hb
def cl_5437 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(72,true),(80,true),(83,true),(90,false)]
theorem inp_5437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5437 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5437 (by decide) v hb
def cl_5438 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,true),(80,true),(83,true),(90,false)]
theorem inp_5438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5438 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5438 v hb
def cl_5439 : CNF.NClause := [(42,false),(11,false),(66,true),(69,true),(72,true),(80,true),(83,true),(90,false)]
theorem inp_5439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5439 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5439 (by decide) v hb
def cl_5440 : CNF.NClause := [(42,false),(11,true),(66,true),(69,true),(72,true),(80,true),(83,true),(90,false)]
theorem inp_5440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5440 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5440 (by decide) v hb
def cl_5441 : CNF.NClause := [(42,false),(11,false),(66,false),(69,false),(72,false),(80,false),(83,false),(90,true)]
theorem inp_5441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5441 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5441 (by decide) v hb
def cl_5442 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,false),(80,false),(83,false),(90,true)]
theorem inp_5442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5442 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5442 v hb
def cl_5443 : CNF.NClause := [(42,false),(11,false),(66,true),(69,false),(72,false),(80,false),(83,false),(90,true)]
theorem inp_5443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5443 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5443 (by decide) v hb
def cl_5444 : CNF.NClause := [(42,false),(11,true),(66,true),(69,false),(72,false),(80,false),(83,false),(90,true)]
theorem inp_5444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5444 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5444 (by decide) v hb
def cl_5445 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(72,false),(80,false),(83,false),(90,true)]
theorem inp_5445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5445 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5445 (by decide) v hb
def cl_5446 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,false),(80,false),(83,false),(90,true)]
theorem inp_5446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5446 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5446 (by decide) v hb
def cl_5447 : CNF.NClause := [(42,false),(11,false),(66,true),(69,true),(72,false),(80,false),(83,false),(90,true)]
theorem inp_5447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5447 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5447 (by decide) v hb
def cl_5448 : CNF.NClause := [(42,false),(11,true),(66,true),(69,true),(72,false),(80,false),(83,false),(90,true)]
theorem inp_5448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5448 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5448 (by decide) v hb
def cl_5449 : CNF.NClause := [(42,false),(11,false),(66,false),(69,false),(72,true),(80,false),(83,false),(90,true)]
theorem inp_5449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5449 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5449 (by decide) v hb
def cl_5450 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,true),(80,false),(83,false),(90,true)]
theorem inp_5450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5450 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5450 (by decide) v hb
def cl_5451 : CNF.NClause := [(42,false),(11,false),(66,true),(69,false),(72,true),(80,false),(83,false),(90,true)]
theorem inp_5451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5451 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5451 (by decide) v hb
def cl_5452 : CNF.NClause := [(42,false),(11,true),(66,true),(69,false),(72,true),(80,false),(83,false),(90,true)]
theorem inp_5452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5452 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5452 (by decide) v hb
def cl_5453 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(72,true),(80,false),(83,false),(90,true)]
theorem inp_5453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5453 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5453 (by decide) v hb
def cl_5454 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,true),(80,false),(83,false),(90,true)]
theorem inp_5454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5454 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5454 (by decide) v hb
end Percolation.NReplay
