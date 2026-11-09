import NInputs002
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_360 : CNF.NClause := [(67,true),(20,true),(21,true),(22,true),(23,false),(24,false),(30,true)]
theorem inp_360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_360 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_360 v hb
def cl_361 : CNF.NClause := [(67,true),(20,false),(21,false),(22,false),(23,true),(24,false),(30,true)]
theorem inp_361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_361 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) cl_361 (by decide) v hb
def cl_362 : CNF.NClause := [(67,true),(20,true),(21,false),(22,false),(23,true),(24,false),(30,true)]
theorem inp_362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_362 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_362 v hb
def cl_363 : CNF.NClause := [(67,true),(20,false),(21,true),(22,false),(23,true),(24,false),(30,true)]
theorem inp_363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_363 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_363 v hb
def cl_364 : CNF.NClause := [(67,true),(20,true),(21,true),(22,false),(23,true),(24,false),(30,true)]
theorem inp_364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_364 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_364 v hb
def cl_365 : CNF.NClause := [(67,true),(20,false),(21,false),(22,true),(23,true),(24,false),(30,true)]
theorem inp_365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_365 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) cl_365 (by decide) v hb
def cl_366 : CNF.NClause := [(67,true),(20,true),(21,false),(22,true),(23,true),(24,false),(30,true)]
theorem inp_366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_366 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_366 v hb
def cl_367 : CNF.NClause := [(67,true),(20,false),(21,true),(22,true),(23,true),(24,false),(30,true)]
theorem inp_367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_367 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_367 v hb
def cl_368 : CNF.NClause := [(67,false),(20,true),(21,true),(22,true),(23,true),(24,false),(30,true)]
theorem inp_368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_368 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) cl_368 (by decide) v hb
def cl_369 : CNF.NClause := [(67,true),(20,false),(21,false),(22,false),(23,false),(24,true),(30,true)]
theorem inp_369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_369 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_369 v hb
def cl_370 : CNF.NClause := [(67,true),(20,true),(21,false),(22,false),(23,false),(24,true),(30,true)]
theorem inp_370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_370 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) cl_370 (by decide) v hb
def cl_371 : CNF.NClause := [(67,true),(20,false),(21,true),(22,false),(23,false),(24,true),(30,true)]
theorem inp_371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_371 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_371 v hb
def cl_372 : CNF.NClause := [(67,true),(20,true),(21,true),(22,false),(23,false),(24,true),(30,true)]
theorem inp_372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_372 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_372 v hb
def cl_373 : CNF.NClause := [(67,true),(20,false),(21,false),(22,true),(23,false),(24,true),(30,true)]
theorem inp_373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_373 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_373 v hb
def cl_374 : CNF.NClause := [(67,true),(20,true),(21,false),(22,true),(23,false),(24,true),(30,true)]
theorem inp_374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_374 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) cl_374 (by decide) v hb
def cl_375 : CNF.NClause := [(67,true),(20,false),(21,true),(22,true),(23,false),(24,true),(30,true)]
theorem inp_375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_375 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_375 v hb
def cl_376 : CNF.NClause := [(67,false),(20,true),(21,true),(22,true),(23,false),(24,true),(30,true)]
theorem inp_376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_376 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) cl_376 (by decide) v hb
def cl_377 : CNF.NClause := [(67,true),(20,false),(21,false),(22,false),(23,true),(24,true),(30,true)]
theorem inp_377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_377 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) cl_377 (by decide) v hb
def cl_378 : CNF.NClause := [(67,true),(20,true),(21,false),(22,false),(23,true),(24,true),(30,true)]
theorem inp_378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_378 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) cl_378 (by decide) v hb
def cl_379 : CNF.NClause := [(67,true),(20,false),(21,true),(22,false),(23,true),(24,true),(30,true)]
theorem inp_379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_379 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_379 v hb
def cl_380 : CNF.NClause := [(67,false),(20,true),(21,true),(22,false),(23,true),(24,true),(30,true)]
theorem inp_380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_380 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) cl_380 (by decide) v hb
def cl_381 : CNF.NClause := [(67,true),(20,false),(21,false),(22,true),(23,true),(24,true),(30,true)]
theorem inp_381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_381 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) cl_381 (by decide) v hb
def cl_382 : CNF.NClause := [(67,false),(20,true),(21,false),(22,true),(23,true),(24,true),(30,true)]
theorem inp_382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_382 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) cl_382 (by decide) v hb
def cl_383 : CNF.NClause := [(67,false),(20,false),(21,true),(22,true),(23,true),(24,true),(30,true)]
theorem inp_383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_383 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) cl_383 (by decide) v hb
def cl_385 : CNF.NClause := [(68,true),(4,false),(8,false),(12,false),(16,false),(20,false),(29,false)]
theorem inp_385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_385 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_385 v hb
def cl_386 : CNF.NClause := [(68,true),(4,true),(8,false),(12,false),(16,false),(20,false),(29,false)]
theorem inp_386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_386 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_386 v hb
def cl_387 : CNF.NClause := [(68,true),(4,false),(8,true),(12,false),(16,false),(20,false),(29,false)]
theorem inp_387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_387 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_387 v hb
def cl_388 : CNF.NClause := [(68,true),(4,true),(8,true),(12,false),(16,false),(20,false),(29,false)]
theorem inp_388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_388 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_388 v hb
def cl_389 : CNF.NClause := [(68,true),(4,false),(8,false),(12,true),(16,false),(20,false),(29,false)]
theorem inp_389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_389 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_389 v hb
def cl_390 : CNF.NClause := [(68,true),(4,true),(8,false),(12,true),(16,false),(20,false),(29,false)]
theorem inp_390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_390 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_390 v hb
def cl_391 : CNF.NClause := [(68,true),(4,false),(8,true),(12,true),(16,false),(20,false),(29,false)]
theorem inp_391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_391 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_391 v hb
def cl_392 : CNF.NClause := [(68,true),(4,true),(8,true),(12,true),(16,false),(20,false),(29,false)]
theorem inp_392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_392 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_392 v hb
def cl_393 : CNF.NClause := [(68,true),(4,false),(8,false),(12,false),(16,true),(20,false),(29,false)]
theorem inp_393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_393 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_393 (by decide) v hb
def cl_394 : CNF.NClause := [(68,true),(4,true),(8,false),(12,false),(16,true),(20,false),(29,false)]
theorem inp_394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_394 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_394 (by decide) v hb
def cl_395 : CNF.NClause := [(68,true),(4,false),(8,true),(12,false),(16,true),(20,false),(29,false)]
theorem inp_395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_395 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_395 v hb
def cl_396 : CNF.NClause := [(68,true),(4,true),(8,true),(12,false),(16,true),(20,false),(29,false)]
theorem inp_396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_396 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_396 v hb
def cl_397 : CNF.NClause := [(68,true),(4,false),(8,false),(12,true),(16,true),(20,false),(29,false)]
theorem inp_397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_397 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_397 (by decide) v hb
def cl_398 : CNF.NClause := [(68,true),(4,true),(8,false),(12,true),(16,true),(20,false),(29,false)]
theorem inp_398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_398 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_398 (by decide) v hb
def cl_399 : CNF.NClause := [(68,true),(4,false),(8,true),(12,true),(16,true),(20,false),(29,false)]
theorem inp_399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_399 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_399 v hb
def cl_400 : CNF.NClause := [(68,true),(4,true),(8,true),(12,true),(16,true),(20,false),(29,false)]
theorem inp_400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_400 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_400 v hb
def cl_401 : CNF.NClause := [(68,true),(4,false),(8,false),(12,false),(16,false),(20,true),(29,false)]
theorem inp_401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_401 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_401 (by decide) v hb
def cl_402 : CNF.NClause := [(68,true),(4,true),(8,false),(12,false),(16,false),(20,true),(29,false)]
theorem inp_402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_402 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_402 (by decide) v hb
def cl_403 : CNF.NClause := [(68,true),(4,false),(8,true),(12,false),(16,false),(20,true),(29,false)]
theorem inp_403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_403 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_403 v hb
def cl_404 : CNF.NClause := [(68,true),(4,true),(8,true),(12,false),(16,false),(20,true),(29,false)]
theorem inp_404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_404 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_404 v hb
def cl_405 : CNF.NClause := [(68,true),(4,false),(8,false),(12,true),(16,false),(20,true),(29,false)]
theorem inp_405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_405 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_405 (by decide) v hb
def cl_406 : CNF.NClause := [(68,true),(4,true),(8,false),(12,true),(16,false),(20,true),(29,false)]
theorem inp_406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_406 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_406 (by decide) v hb
def cl_407 : CNF.NClause := [(68,true),(4,false),(8,true),(12,true),(16,false),(20,true),(29,false)]
theorem inp_407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_407 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_407 v hb
def cl_408 : CNF.NClause := [(68,true),(4,true),(8,true),(12,true),(16,false),(20,true),(29,false)]
theorem inp_408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_408 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_408 v hb
def cl_409 : CNF.NClause := [(68,true),(4,false),(8,false),(12,false),(16,true),(20,true),(29,false)]
theorem inp_409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_409 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_409 (by decide) v hb
def cl_410 : CNF.NClause := [(68,true),(4,true),(8,false),(12,false),(16,true),(20,true),(29,false)]
theorem inp_410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_410 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_410 (by decide) v hb
end Percolation.NReplay
