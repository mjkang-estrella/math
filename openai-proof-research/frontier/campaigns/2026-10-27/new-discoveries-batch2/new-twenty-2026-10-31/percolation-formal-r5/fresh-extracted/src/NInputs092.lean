import NInputs091
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_5354 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,true),(75,false),(76,true),(92,true)]
theorem inp_5354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5354 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5354 (by decide) v hb
def cl_5355 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(74,true),(75,false),(76,true),(92,true)]
theorem inp_5355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5355 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5355 (by decide) v hb
def cl_5356 : CNF.NClause := [(41,false),(10,true),(72,true),(73,false),(74,true),(75,false),(76,true),(92,true)]
theorem inp_5356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5356 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5356 (by decide) v hb
def cl_5357 : CNF.NClause := [(41,false),(10,false),(72,false),(73,true),(74,true),(75,false),(76,true),(92,true)]
theorem inp_5357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5357 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5357 (by decide) v hb
def cl_5358 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,true),(75,false),(76,true),(92,true)]
theorem inp_5358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5358 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5358 (by decide) v hb
def cl_5359 : CNF.NClause := [(41,false),(10,false),(72,true),(73,true),(74,true),(75,false),(76,true),(92,true)]
theorem inp_5359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5359 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5359 (by decide) v hb
def cl_5360 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,true),(75,false),(76,true),(92,true)]
theorem inp_5360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5360 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5360 (by decide) v hb
def cl_5361 : CNF.NClause := [(41,false),(10,false),(72,false),(73,false),(74,false),(75,true),(76,true),(92,true)]
theorem inp_5361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5361 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5361 (by decide) v hb
def cl_5362 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,false),(75,true),(76,true),(92,true)]
theorem inp_5362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5362 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5362 (by decide) v hb
def cl_5363 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(74,false),(75,true),(76,true),(92,true)]
theorem inp_5363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5363 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5363 (by decide) v hb
def cl_5364 : CNF.NClause := [(41,false),(10,true),(72,true),(73,false),(74,false),(75,true),(76,true),(92,true)]
theorem inp_5364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5364 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5364 (by decide) v hb
def cl_5365 : CNF.NClause := [(41,false),(10,false),(72,false),(73,true),(74,false),(75,true),(76,true),(92,true)]
theorem inp_5365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5365 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5365 (by decide) v hb
def cl_5366 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,false),(75,true),(76,true),(92,true)]
theorem inp_5366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5366 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5366 (by decide) v hb
def cl_5367 : CNF.NClause := [(41,false),(10,false),(72,true),(73,true),(74,false),(75,true),(76,true),(92,true)]
theorem inp_5367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5367 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5367 (by decide) v hb
def cl_5368 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,false),(75,true),(76,true),(92,true)]
theorem inp_5368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5368 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5368 (by decide) v hb
def cl_5369 : CNF.NClause := [(41,false),(10,false),(72,false),(73,false),(74,true),(75,true),(76,true),(92,true)]
theorem inp_5369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5369 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5369 (by decide) v hb
def cl_5370 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,true),(75,true),(76,true),(92,true)]
theorem inp_5370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5370 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5370 (by decide) v hb
def cl_5371 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(74,true),(75,true),(76,true),(92,true)]
theorem inp_5371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5371 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5371 (by decide) v hb
def cl_5372 : CNF.NClause := [(41,false),(10,true),(72,true),(73,false),(74,true),(75,true),(76,true),(92,true)]
theorem inp_5372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5372 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5372 (by decide) v hb
def cl_5373 : CNF.NClause := [(41,false),(10,false),(72,false),(73,true),(74,true),(75,true),(76,true),(92,true)]
theorem inp_5373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5373 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5373 (by decide) v hb
def cl_5374 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,true),(75,true),(76,true),(92,true)]
theorem inp_5374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5374 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5374 (by decide) v hb
def cl_5376 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,true),(75,true),(76,true),(92,true)]
theorem inp_5376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5376 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5376 v hb
def cl_5377 : CNF.NClause := [(42,true),(11,false),(66,false),(69,false),(72,false),(80,false),(83,false),(90,false)]
theorem inp_5377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5377 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5377 (by decide) v hb
def cl_5378 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,false),(80,false),(83,false),(90,false)]
theorem inp_5378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5378 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5378 v hb
def cl_5379 : CNF.NClause := [(42,false),(11,false),(66,true),(69,false),(72,false),(80,false),(83,false),(90,false)]
theorem inp_5379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5379 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5379 (by decide) v hb
def cl_5380 : CNF.NClause := [(42,false),(11,true),(66,true),(69,false),(72,false),(80,false),(83,false),(90,false)]
theorem inp_5380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5380 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5380 (by decide) v hb
def cl_5381 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(72,false),(80,false),(83,false),(90,false)]
theorem inp_5381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5381 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5381 (by decide) v hb
def cl_5382 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,false),(80,false),(83,false),(90,false)]
theorem inp_5382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5382 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5382 v hb
def cl_5383 : CNF.NClause := [(42,false),(11,false),(66,true),(69,true),(72,false),(80,false),(83,false),(90,false)]
theorem inp_5383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5383 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5383 (by decide) v hb
def cl_5384 : CNF.NClause := [(42,false),(11,true),(66,true),(69,true),(72,false),(80,false),(83,false),(90,false)]
theorem inp_5384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5384 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5384 (by decide) v hb
def cl_5385 : CNF.NClause := [(42,false),(11,false),(66,false),(69,false),(72,true),(80,false),(83,false),(90,false)]
theorem inp_5385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5385 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5385 (by decide) v hb
def cl_5386 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,true),(80,false),(83,false),(90,false)]
theorem inp_5386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5386 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5386 v hb
def cl_5387 : CNF.NClause := [(42,false),(11,false),(66,true),(69,false),(72,true),(80,false),(83,false),(90,false)]
theorem inp_5387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5387 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5387 (by decide) v hb
def cl_5388 : CNF.NClause := [(42,false),(11,true),(66,true),(69,false),(72,true),(80,false),(83,false),(90,false)]
theorem inp_5388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5388 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5388 (by decide) v hb
def cl_5389 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(72,true),(80,false),(83,false),(90,false)]
theorem inp_5389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5389 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5389 (by decide) v hb
def cl_5390 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,true),(80,false),(83,false),(90,false)]
theorem inp_5390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5390 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5390 v hb
def cl_5391 : CNF.NClause := [(42,false),(11,false),(66,true),(69,true),(72,true),(80,false),(83,false),(90,false)]
theorem inp_5391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5391 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5391 (by decide) v hb
def cl_5392 : CNF.NClause := [(42,false),(11,true),(66,true),(69,true),(72,true),(80,false),(83,false),(90,false)]
theorem inp_5392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5392 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5392 (by decide) v hb
def cl_5393 : CNF.NClause := [(42,false),(11,false),(66,false),(69,false),(72,false),(80,true),(83,false),(90,false)]
theorem inp_5393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5393 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5393 v hb
def cl_5394 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,false),(80,true),(83,false),(90,false)]
theorem inp_5394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5394 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5394 v hb
def cl_5395 : CNF.NClause := [(42,false),(11,false),(66,true),(69,false),(72,false),(80,true),(83,false),(90,false)]
theorem inp_5395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5395 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5395 v hb
def cl_5396 : CNF.NClause := [(42,false),(11,true),(66,true),(69,false),(72,false),(80,true),(83,false),(90,false)]
theorem inp_5396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5396 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5396 (by decide) v hb
def cl_5397 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(72,false),(80,true),(83,false),(90,false)]
theorem inp_5397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5397 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5397 (by decide) v hb
def cl_5398 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,false),(80,true),(83,false),(90,false)]
theorem inp_5398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5398 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5398 v hb
def cl_5399 : CNF.NClause := [(42,false),(11,false),(66,true),(69,true),(72,false),(80,true),(83,false),(90,false)]
theorem inp_5399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5399 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5399 (by decide) v hb
def cl_5400 : CNF.NClause := [(42,false),(11,true),(66,true),(69,true),(72,false),(80,true),(83,false),(90,false)]
theorem inp_5400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5400 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5400 (by decide) v hb
def cl_5401 : CNF.NClause := [(42,false),(11,false),(66,false),(69,false),(72,true),(80,true),(83,false),(90,false)]
theorem inp_5401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5401 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5401 (by decide) v hb
def cl_5402 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,true),(80,true),(83,false),(90,false)]
theorem inp_5402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5402 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5402 v hb
def cl_5403 : CNF.NClause := [(42,false),(11,false),(66,true),(69,false),(72,true),(80,true),(83,false),(90,false)]
theorem inp_5403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5403 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5403 (by decide) v hb
def cl_5404 : CNF.NClause := [(42,false),(11,true),(66,true),(69,false),(72,true),(80,true),(83,false),(90,false)]
theorem inp_5404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5404 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5404 (by decide) v hb
end Percolation.NReplay
