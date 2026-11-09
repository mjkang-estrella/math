import NInputs128
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_7334 : CNF.NClause := [(57,false),(26,true),(62,false),(71,true),(75,false),(79,false),(83,true),(91,false)]
theorem inp_7334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7334 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7334 (by decide) v hb
def cl_7335 : CNF.NClause := [(57,false),(26,false),(62,true),(71,true),(75,false),(79,false),(83,true),(91,false)]
theorem inp_7335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7335 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7335 (by decide) v hb
def cl_7336 : CNF.NClause := [(57,false),(26,true),(62,true),(71,true),(75,false),(79,false),(83,true),(91,false)]
theorem inp_7336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7336 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7336 (by decide) v hb
def cl_7338 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,true),(79,false),(83,true),(91,false)]
theorem inp_7338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7338 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7338 v hb
def cl_7339 : CNF.NClause := [(57,false),(26,false),(62,true),(71,false),(75,true),(79,false),(83,true),(91,false)]
theorem inp_7339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7339 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7339 (by decide) v hb
def cl_7340 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,true),(79,false),(83,true),(91,false)]
theorem inp_7340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7340 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7340 v hb
def cl_7341 : CNF.NClause := [(57,false),(26,false),(62,false),(71,true),(75,true),(79,false),(83,true),(91,false)]
theorem inp_7341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7341 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7341 (by decide) v hb
def cl_7342 : CNF.NClause := [(57,false),(26,true),(62,false),(71,true),(75,true),(79,false),(83,true),(91,false)]
theorem inp_7342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7342 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7342 (by decide) v hb
def cl_7343 : CNF.NClause := [(57,false),(26,false),(62,true),(71,true),(75,true),(79,false),(83,true),(91,false)]
theorem inp_7343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7343 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7343 (by decide) v hb
def cl_7344 : CNF.NClause := [(57,false),(26,true),(62,true),(71,true),(75,true),(79,false),(83,true),(91,false)]
theorem inp_7344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7344 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7344 (by decide) v hb
def cl_7345 : CNF.NClause := [(57,false),(26,false),(62,false),(71,false),(75,false),(79,true),(83,true),(91,false)]
theorem inp_7345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7345 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7345 (by decide) v hb
def cl_7346 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,false),(79,true),(83,true),(91,false)]
theorem inp_7346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7346 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7346 (by decide) v hb
def cl_7347 : CNF.NClause := [(57,false),(26,false),(62,true),(71,false),(75,false),(79,true),(83,true),(91,false)]
theorem inp_7347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7347 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7347 (by decide) v hb
def cl_7348 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,false),(79,true),(83,true),(91,false)]
theorem inp_7348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7348 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7348 (by decide) v hb
def cl_7349 : CNF.NClause := [(57,false),(26,false),(62,false),(71,true),(75,false),(79,true),(83,true),(91,false)]
theorem inp_7349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7349 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7349 (by decide) v hb
def cl_7350 : CNF.NClause := [(57,false),(26,true),(62,false),(71,true),(75,false),(79,true),(83,true),(91,false)]
theorem inp_7350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7350 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7350 (by decide) v hb
def cl_7351 : CNF.NClause := [(57,false),(26,false),(62,true),(71,true),(75,false),(79,true),(83,true),(91,false)]
theorem inp_7351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7351 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7351 (by decide) v hb
def cl_7352 : CNF.NClause := [(57,false),(26,true),(62,true),(71,true),(75,false),(79,true),(83,true),(91,false)]
theorem inp_7352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7352 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7352 (by decide) v hb
def cl_7353 : CNF.NClause := [(57,false),(26,false),(62,false),(71,false),(75,true),(79,true),(83,true),(91,false)]
theorem inp_7353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7353 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7353 (by decide) v hb
def cl_7354 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,true),(79,true),(83,true),(91,false)]
theorem inp_7354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7354 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7354 (by decide) v hb
def cl_7355 : CNF.NClause := [(57,false),(26,false),(62,true),(71,false),(75,true),(79,true),(83,true),(91,false)]
theorem inp_7355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7355 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7355 (by decide) v hb
def cl_7356 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,true),(79,true),(83,true),(91,false)]
theorem inp_7356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7356 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7356 (by decide) v hb
def cl_7357 : CNF.NClause := [(57,false),(26,false),(62,false),(71,true),(75,true),(79,true),(83,true),(91,false)]
theorem inp_7357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7357 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7357 (by decide) v hb
def cl_7358 : CNF.NClause := [(57,false),(26,true),(62,false),(71,true),(75,true),(79,true),(83,true),(91,false)]
theorem inp_7358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7358 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7358 (by decide) v hb
def cl_7359 : CNF.NClause := [(57,false),(26,false),(62,true),(71,true),(75,true),(79,true),(83,true),(91,false)]
theorem inp_7359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7359 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7359 (by decide) v hb
def cl_7360 : CNF.NClause := [(57,false),(26,true),(62,true),(71,true),(75,true),(79,true),(83,true),(91,false)]
theorem inp_7360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7360 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7360 (by decide) v hb
def cl_7361 : CNF.NClause := [(57,false),(26,false),(62,false),(71,false),(75,false),(79,false),(83,false),(91,true)]
theorem inp_7361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7361 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7361 (by decide) v hb
def cl_7362 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,false),(79,false),(83,false),(91,true)]
theorem inp_7362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7362 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7362 (by decide) v hb
def cl_7363 : CNF.NClause := [(57,false),(26,false),(62,true),(71,false),(75,false),(79,false),(83,false),(91,true)]
theorem inp_7363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7363 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7363 (by decide) v hb
def cl_7364 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,false),(79,false),(83,false),(91,true)]
theorem inp_7364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7364 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7364 (by decide) v hb
def cl_7365 : CNF.NClause := [(57,false),(26,false),(62,false),(71,true),(75,false),(79,false),(83,false),(91,true)]
theorem inp_7365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7365 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7365 (by decide) v hb
def cl_7366 : CNF.NClause := [(57,false),(26,true),(62,false),(71,true),(75,false),(79,false),(83,false),(91,true)]
theorem inp_7366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7366 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7366 (by decide) v hb
def cl_7367 : CNF.NClause := [(57,false),(26,false),(62,true),(71,true),(75,false),(79,false),(83,false),(91,true)]
theorem inp_7367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7367 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7367 (by decide) v hb
def cl_7368 : CNF.NClause := [(57,false),(26,true),(62,true),(71,true),(75,false),(79,false),(83,false),(91,true)]
theorem inp_7368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7368 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7368 (by decide) v hb
def cl_7369 : CNF.NClause := [(57,false),(26,false),(62,false),(71,false),(75,true),(79,false),(83,false),(91,true)]
theorem inp_7369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7369 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7369 (by decide) v hb
def cl_7370 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,true),(79,false),(83,false),(91,true)]
theorem inp_7370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7370 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7370 (by decide) v hb
def cl_7371 : CNF.NClause := [(57,false),(26,false),(62,true),(71,false),(75,true),(79,false),(83,false),(91,true)]
theorem inp_7371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7371 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7371 (by decide) v hb
def cl_7372 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,true),(79,false),(83,false),(91,true)]
theorem inp_7372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7372 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7372 (by decide) v hb
def cl_7373 : CNF.NClause := [(57,false),(26,false),(62,false),(71,true),(75,true),(79,false),(83,false),(91,true)]
theorem inp_7373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7373 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7373 (by decide) v hb
def cl_7374 : CNF.NClause := [(57,false),(26,true),(62,false),(71,true),(75,true),(79,false),(83,false),(91,true)]
theorem inp_7374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7374 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7374 (by decide) v hb
def cl_7375 : CNF.NClause := [(57,false),(26,false),(62,true),(71,true),(75,true),(79,false),(83,false),(91,true)]
theorem inp_7375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7375 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7375 (by decide) v hb
def cl_7376 : CNF.NClause := [(57,false),(26,true),(62,true),(71,true),(75,true),(79,false),(83,false),(91,true)]
theorem inp_7376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7376 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7376 (by decide) v hb
def cl_7377 : CNF.NClause := [(57,false),(26,false),(62,false),(71,false),(75,false),(79,true),(83,false),(91,true)]
theorem inp_7377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7377 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7377 (by decide) v hb
def cl_7378 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,false),(79,true),(83,false),(91,true)]
theorem inp_7378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7378 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7378 (by decide) v hb
def cl_7379 : CNF.NClause := [(57,false),(26,false),(62,true),(71,false),(75,false),(79,true),(83,false),(91,true)]
theorem inp_7379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7379 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7379 (by decide) v hb
def cl_7380 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,false),(79,true),(83,false),(91,true)]
theorem inp_7380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7380 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7380 (by decide) v hb
def cl_7381 : CNF.NClause := [(57,false),(26,false),(62,false),(71,true),(75,false),(79,true),(83,false),(91,true)]
theorem inp_7381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7381 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7381 (by decide) v hb
def cl_7382 : CNF.NClause := [(57,false),(26,true),(62,false),(71,true),(75,false),(79,true),(83,false),(91,true)]
theorem inp_7382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7382 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7382 (by decide) v hb
def cl_7383 : CNF.NClause := [(57,false),(26,false),(62,true),(71,true),(75,false),(79,true),(83,false),(91,true)]
theorem inp_7383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7383 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7383 (by decide) v hb
def cl_7384 : CNF.NClause := [(57,false),(26,true),(62,true),(71,true),(75,false),(79,true),(83,false),(91,true)]
theorem inp_7384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7384 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7384 (by decide) v hb
end Percolation.NReplay
