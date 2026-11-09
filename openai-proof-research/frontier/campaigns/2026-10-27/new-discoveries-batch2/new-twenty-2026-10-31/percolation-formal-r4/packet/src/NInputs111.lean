import NInputs110
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_6334 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,true),(77,true),(86,true),(91,false)]
theorem inp_6334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6334 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6334 (by decide) v hb
def cl_6335 : CNF.NClause := [(49,false),(18,false),(65,true),(69,true),(73,true),(77,true),(86,true),(91,false)]
theorem inp_6335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6335 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6335 (by decide) v hb
def cl_6336 : CNF.NClause := [(49,false),(18,true),(65,true),(69,true),(73,true),(77,true),(86,true),(91,false)]
theorem inp_6336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6336 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6336 (by decide) v hb
def cl_6337 : CNF.NClause := [(49,false),(18,false),(65,false),(69,false),(73,false),(77,false),(86,false),(91,true)]
theorem inp_6337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6337 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6337 (by decide) v hb
def cl_6338 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,false),(77,false),(86,false),(91,true)]
theorem inp_6338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6338 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6338 (by decide) v hb
def cl_6339 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(73,false),(77,false),(86,false),(91,true)]
theorem inp_6339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6339 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6339 (by decide) v hb
def cl_6340 : CNF.NClause := [(49,false),(18,true),(65,true),(69,false),(73,false),(77,false),(86,false),(91,true)]
theorem inp_6340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6340 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6340 (by decide) v hb
def cl_6341 : CNF.NClause := [(49,false),(18,false),(65,false),(69,true),(73,false),(77,false),(86,false),(91,true)]
theorem inp_6341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6341 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6341 (by decide) v hb
def cl_6342 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,false),(77,false),(86,false),(91,true)]
theorem inp_6342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6342 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6342 (by decide) v hb
def cl_6343 : CNF.NClause := [(49,false),(18,false),(65,true),(69,true),(73,false),(77,false),(86,false),(91,true)]
theorem inp_6343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6343 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6343 (by decide) v hb
def cl_6344 : CNF.NClause := [(49,false),(18,true),(65,true),(69,true),(73,false),(77,false),(86,false),(91,true)]
theorem inp_6344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6344 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6344 (by decide) v hb
def cl_6345 : CNF.NClause := [(49,false),(18,false),(65,false),(69,false),(73,true),(77,false),(86,false),(91,true)]
theorem inp_6345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6345 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6345 (by decide) v hb
def cl_6346 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,true),(77,false),(86,false),(91,true)]
theorem inp_6346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6346 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6346 (by decide) v hb
def cl_6347 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(73,true),(77,false),(86,false),(91,true)]
theorem inp_6347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6347 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6347 (by decide) v hb
def cl_6348 : CNF.NClause := [(49,false),(18,true),(65,true),(69,false),(73,true),(77,false),(86,false),(91,true)]
theorem inp_6348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6348 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6348 (by decide) v hb
def cl_6350 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,true),(77,false),(86,false),(91,true)]
theorem inp_6350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6350 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6350 (by decide) v hb
def cl_6351 : CNF.NClause := [(49,false),(18,false),(65,true),(69,true),(73,true),(77,false),(86,false),(91,true)]
theorem inp_6351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6351 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6351 (by decide) v hb
def cl_6352 : CNF.NClause := [(49,false),(18,true),(65,true),(69,true),(73,true),(77,false),(86,false),(91,true)]
theorem inp_6352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6352 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6352 (by decide) v hb
def cl_6353 : CNF.NClause := [(49,false),(18,false),(65,false),(69,false),(73,false),(77,true),(86,false),(91,true)]
theorem inp_6353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6353 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6353 (by decide) v hb
def cl_6354 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,false),(77,true),(86,false),(91,true)]
theorem inp_6354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6354 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6354 (by decide) v hb
def cl_6355 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(73,false),(77,true),(86,false),(91,true)]
theorem inp_6355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6355 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6355 (by decide) v hb
def cl_6356 : CNF.NClause := [(49,false),(18,true),(65,true),(69,false),(73,false),(77,true),(86,false),(91,true)]
theorem inp_6356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6356 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6356 (by decide) v hb
def cl_6357 : CNF.NClause := [(49,false),(18,false),(65,false),(69,true),(73,false),(77,true),(86,false),(91,true)]
theorem inp_6357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6357 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6357 (by decide) v hb
def cl_6358 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,false),(77,true),(86,false),(91,true)]
theorem inp_6358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6358 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6358 (by decide) v hb
def cl_6359 : CNF.NClause := [(49,false),(18,false),(65,true),(69,true),(73,false),(77,true),(86,false),(91,true)]
theorem inp_6359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6359 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6359 (by decide) v hb
def cl_6360 : CNF.NClause := [(49,false),(18,true),(65,true),(69,true),(73,false),(77,true),(86,false),(91,true)]
theorem inp_6360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6360 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6360 (by decide) v hb
def cl_6361 : CNF.NClause := [(49,false),(18,false),(65,false),(69,false),(73,true),(77,true),(86,false),(91,true)]
theorem inp_6361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6361 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6361 (by decide) v hb
def cl_6362 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,true),(77,true),(86,false),(91,true)]
theorem inp_6362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6362 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6362 v hb
def cl_6363 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(73,true),(77,true),(86,false),(91,true)]
theorem inp_6363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6363 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6363 (by decide) v hb
def cl_6364 : CNF.NClause := [(49,false),(18,true),(65,true),(69,false),(73,true),(77,true),(86,false),(91,true)]
theorem inp_6364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6364 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6364 (by decide) v hb
def cl_6365 : CNF.NClause := [(49,false),(18,false),(65,false),(69,true),(73,true),(77,true),(86,false),(91,true)]
theorem inp_6365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6365 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6365 (by decide) v hb
def cl_6366 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,true),(77,true),(86,false),(91,true)]
theorem inp_6366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6366 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6366 v hb
def cl_6367 : CNF.NClause := [(49,false),(18,false),(65,true),(69,true),(73,true),(77,true),(86,false),(91,true)]
theorem inp_6367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6367 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6367 (by decide) v hb
def cl_6368 : CNF.NClause := [(49,false),(18,true),(65,true),(69,true),(73,true),(77,true),(86,false),(91,true)]
theorem inp_6368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6368 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6368 (by decide) v hb
def cl_6369 : CNF.NClause := [(49,false),(18,false),(65,false),(69,false),(73,false),(77,false),(86,true),(91,true)]
theorem inp_6369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6369 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6369 (by decide) v hb
def cl_6370 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,false),(77,false),(86,true),(91,true)]
theorem inp_6370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6370 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6370 (by decide) v hb
def cl_6371 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(73,false),(77,false),(86,true),(91,true)]
theorem inp_6371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6371 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6371 (by decide) v hb
def cl_6372 : CNF.NClause := [(49,false),(18,true),(65,true),(69,false),(73,false),(77,false),(86,true),(91,true)]
theorem inp_6372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6372 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6372 (by decide) v hb
def cl_6373 : CNF.NClause := [(49,false),(18,false),(65,false),(69,true),(73,false),(77,false),(86,true),(91,true)]
theorem inp_6373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6373 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6373 (by decide) v hb
def cl_6374 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,false),(77,false),(86,true),(91,true)]
theorem inp_6374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6374 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6374 (by decide) v hb
def cl_6375 : CNF.NClause := [(49,false),(18,false),(65,true),(69,true),(73,false),(77,false),(86,true),(91,true)]
theorem inp_6375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6375 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6375 (by decide) v hb
def cl_6376 : CNF.NClause := [(49,false),(18,true),(65,true),(69,true),(73,false),(77,false),(86,true),(91,true)]
theorem inp_6376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6376 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6376 (by decide) v hb
def cl_6377 : CNF.NClause := [(49,false),(18,false),(65,false),(69,false),(73,true),(77,false),(86,true),(91,true)]
theorem inp_6377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6377 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6377 (by decide) v hb
def cl_6378 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,true),(77,false),(86,true),(91,true)]
theorem inp_6378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6378 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6378 (by decide) v hb
def cl_6379 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(73,true),(77,false),(86,true),(91,true)]
theorem inp_6379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6379 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6379 (by decide) v hb
def cl_6380 : CNF.NClause := [(49,false),(18,true),(65,true),(69,false),(73,true),(77,false),(86,true),(91,true)]
theorem inp_6380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6380 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6380 (by decide) v hb
def cl_6381 : CNF.NClause := [(49,false),(18,false),(65,false),(69,true),(73,true),(77,false),(86,true),(91,true)]
theorem inp_6381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6381 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6381 (by decide) v hb
def cl_6382 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,true),(77,false),(86,true),(91,true)]
theorem inp_6382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6382 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6382 (by decide) v hb
def cl_6383 : CNF.NClause := [(49,false),(18,false),(65,true),(69,true),(73,true),(77,false),(86,true),(91,true)]
theorem inp_6383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6383 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6383 (by decide) v hb
def cl_6384 : CNF.NClause := [(49,false),(18,true),(65,true),(69,true),(73,true),(77,false),(86,true),(91,true)]
theorem inp_6384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6384 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6384 (by decide) v hb
end Percolation.NReplay
