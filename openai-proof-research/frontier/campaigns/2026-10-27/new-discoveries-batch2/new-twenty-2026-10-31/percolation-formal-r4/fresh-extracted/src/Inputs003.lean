import Inputs002
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_289 : CNF.NClause := [(66,true),(1,false),(6,false),(11,false),(16,false),(21,false),(25,true)]
theorem inp_289 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_289 := by
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_289 (by decide) v h
def cl_291 : CNF.NClause := [(66,true),(1,false),(6,true),(11,false),(16,false),(21,false),(25,true)]
theorem inp_291 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_291 := by
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_291 (by decide) v h
def cl_293 : CNF.NClause := [(66,true),(1,false),(6,false),(11,true),(16,false),(21,false),(25,true)]
theorem inp_293 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_293 := by
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_293 (by decide) v h
def cl_299 : CNF.NClause := [(66,true),(1,false),(6,true),(11,false),(16,true),(21,false),(25,true)]
theorem inp_299 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_299 := by
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_299 (by decide) v h
def cl_301 : CNF.NClause := [(66,true),(1,false),(6,false),(11,true),(16,true),(21,false),(25,true)]
theorem inp_301 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_301 := by
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_301 (by decide) v h
def cl_306 : CNF.NClause := [(66,true),(1,true),(6,false),(11,false),(16,false),(21,true),(25,true)]
theorem inp_306 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_306 := by
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_306 (by decide) v h
def cl_307 : CNF.NClause := [(66,true),(1,false),(6,true),(11,false),(16,false),(21,true),(25,true)]
theorem inp_307 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_307 := by
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_307 (by decide) v h
def cl_309 : CNF.NClause := [(66,true),(1,false),(6,false),(11,true),(16,false),(21,true),(25,true)]
theorem inp_309 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_309 := by
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_309 (by decide) v h
def cl_313 : CNF.NClause := [(66,true),(1,false),(6,false),(11,false),(16,true),(21,true),(25,true)]
theorem inp_313 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_313 := by
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_313 (by decide) v h
def cl_314 : CNF.NClause := [(66,true),(1,true),(6,false),(11,false),(16,true),(21,true),(25,true)]
theorem inp_314 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_314 := by
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_314 (by decide) v h
def cl_315 : CNF.NClause := [(66,true),(1,false),(6,true),(11,false),(16,true),(21,true),(25,true)]
theorem inp_315 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_315 := by
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_315 (by decide) v h
def cl_317 : CNF.NClause := [(66,true),(1,false),(6,false),(11,true),(16,true),(21,true),(25,true)]
theorem inp_317 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_317 := by
  exact input_gate (activationGate5 SatVar.a (.i 4) 4) (activationA_mem 4) cl_317 (by decide) v h
def cl_321 : CNF.NClause := [(67,true),(20,false),(21,false),(22,false),(23,false),(24,false),(30,false)]
theorem inp_321 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_321 := by
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) cl_321 (by decide) v h
def cl_353 : CNF.NClause := [(67,true),(20,false),(21,false),(22,false),(23,false),(24,false),(30,true)]
theorem inp_353 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_353 := by
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) cl_353 (by decide) v h
def cl_354 : CNF.NClause := [(67,true),(20,true),(21,false),(22,false),(23,false),(24,false),(30,true)]
theorem inp_354 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_354 := by
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) cl_354 (by decide) v h
def cl_355 : CNF.NClause := [(67,true),(20,false),(21,true),(22,false),(23,false),(24,false),(30,true)]
theorem inp_355 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_355 := by
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) cl_355 (by decide) v h
def cl_356 : CNF.NClause := [(67,true),(20,true),(21,true),(22,false),(23,false),(24,false),(30,true)]
theorem inp_356 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_356 := by
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) cl_356 (by decide) v h
def cl_358 : CNF.NClause := [(67,true),(20,true),(21,false),(22,true),(23,false),(24,false),(30,true)]
theorem inp_358 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_358 := by
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) cl_358 (by decide) v h
def cl_359 : CNF.NClause := [(67,true),(20,false),(21,true),(22,true),(23,false),(24,false),(30,true)]
theorem inp_359 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_359 := by
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) cl_359 (by decide) v h
def cl_360 : CNF.NClause := [(67,true),(20,true),(21,true),(22,true),(23,false),(24,false),(30,true)]
theorem inp_360 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_360 := by
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) cl_360 (by decide) v h
def cl_362 : CNF.NClause := [(67,true),(20,true),(21,false),(22,false),(23,true),(24,false),(30,true)]
theorem inp_362 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_362 := by
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) cl_362 (by decide) v h
def cl_363 : CNF.NClause := [(67,true),(20,false),(21,true),(22,false),(23,true),(24,false),(30,true)]
theorem inp_363 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_363 := by
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) cl_363 (by decide) v h
def cl_364 : CNF.NClause := [(67,true),(20,true),(21,true),(22,false),(23,true),(24,false),(30,true)]
theorem inp_364 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_364 := by
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) cl_364 (by decide) v h
def cl_366 : CNF.NClause := [(67,true),(20,true),(21,false),(22,true),(23,true),(24,false),(30,true)]
theorem inp_366 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_366 := by
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) cl_366 (by decide) v h
def cl_367 : CNF.NClause := [(67,true),(20,false),(21,true),(22,true),(23,true),(24,false),(30,true)]
theorem inp_367 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_367 := by
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) cl_367 (by decide) v h
def cl_369 : CNF.NClause := [(67,true),(20,false),(21,false),(22,false),(23,false),(24,true),(30,true)]
theorem inp_369 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_369 := by
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) cl_369 (by decide) v h
def cl_371 : CNF.NClause := [(67,true),(20,false),(21,true),(22,false),(23,false),(24,true),(30,true)]
theorem inp_371 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_371 := by
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) cl_371 (by decide) v h
def cl_372 : CNF.NClause := [(67,true),(20,true),(21,true),(22,false),(23,false),(24,true),(30,true)]
theorem inp_372 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_372 := by
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) cl_372 (by decide) v h
def cl_373 : CNF.NClause := [(67,true),(20,false),(21,false),(22,true),(23,false),(24,true),(30,true)]
theorem inp_373 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_373 := by
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) cl_373 (by decide) v h
def cl_375 : CNF.NClause := [(67,true),(20,false),(21,true),(22,true),(23,false),(24,true),(30,true)]
theorem inp_375 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_375 := by
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) cl_375 (by decide) v h
def cl_379 : CNF.NClause := [(67,true),(20,false),(21,true),(22,false),(23,true),(24,true),(30,true)]
theorem inp_379 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_379 := by
  exact input_gate (activationGate5 SatVar.a (.i 5) 5) (activationA_mem 5) cl_379 (by decide) v h
def cl_385 : CNF.NClause := [(68,true),(4,false),(8,false),(12,false),(16,false),(20,false),(29,false)]
theorem inp_385 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_385 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_385 (by decide) v h
def cl_386 : CNF.NClause := [(68,true),(4,true),(8,false),(12,false),(16,false),(20,false),(29,false)]
theorem inp_386 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_386 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_386 (by decide) v h
def cl_387 : CNF.NClause := [(68,true),(4,false),(8,true),(12,false),(16,false),(20,false),(29,false)]
theorem inp_387 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_387 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_387 (by decide) v h
def cl_388 : CNF.NClause := [(68,true),(4,true),(8,true),(12,false),(16,false),(20,false),(29,false)]
theorem inp_388 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_388 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_388 (by decide) v h
def cl_389 : CNF.NClause := [(68,true),(4,false),(8,false),(12,true),(16,false),(20,false),(29,false)]
theorem inp_389 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_389 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_389 (by decide) v h
def cl_390 : CNF.NClause := [(68,true),(4,true),(8,false),(12,true),(16,false),(20,false),(29,false)]
theorem inp_390 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_390 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_390 (by decide) v h
def cl_391 : CNF.NClause := [(68,true),(4,false),(8,true),(12,true),(16,false),(20,false),(29,false)]
theorem inp_391 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_391 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_391 (by decide) v h
def cl_392 : CNF.NClause := [(68,true),(4,true),(8,true),(12,true),(16,false),(20,false),(29,false)]
theorem inp_392 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_392 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_392 (by decide) v h
def cl_395 : CNF.NClause := [(68,true),(4,false),(8,true),(12,false),(16,true),(20,false),(29,false)]
theorem inp_395 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_395 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_395 (by decide) v h
def cl_396 : CNF.NClause := [(68,true),(4,true),(8,true),(12,false),(16,true),(20,false),(29,false)]
theorem inp_396 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_396 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_396 (by decide) v h
def cl_399 : CNF.NClause := [(68,true),(4,false),(8,true),(12,true),(16,true),(20,false),(29,false)]
theorem inp_399 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_399 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_399 (by decide) v h
def cl_400 : CNF.NClause := [(68,true),(4,true),(8,true),(12,true),(16,true),(20,false),(29,false)]
theorem inp_400 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_400 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_400 (by decide) v h
def cl_403 : CNF.NClause := [(68,true),(4,false),(8,true),(12,false),(16,false),(20,true),(29,false)]
theorem inp_403 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_403 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_403 (by decide) v h
def cl_404 : CNF.NClause := [(68,true),(4,true),(8,true),(12,false),(16,false),(20,true),(29,false)]
theorem inp_404 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_404 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_404 (by decide) v h
def cl_407 : CNF.NClause := [(68,true),(4,false),(8,true),(12,true),(16,false),(20,true),(29,false)]
theorem inp_407 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_407 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_407 (by decide) v h
def cl_408 : CNF.NClause := [(68,true),(4,true),(8,true),(12,true),(16,false),(20,true),(29,false)]
theorem inp_408 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_408 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_408 (by decide) v h
def cl_411 : CNF.NClause := [(68,true),(4,false),(8,true),(12,false),(16,true),(20,true),(29,false)]
theorem inp_411 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_411 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_411 (by decide) v h
def cl_412 : CNF.NClause := [(68,true),(4,true),(8,true),(12,false),(16,true),(20,true),(29,false)]
theorem inp_412 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_412 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_412 (by decide) v h
def cl_415 : CNF.NClause := [(68,true),(4,false),(8,true),(12,true),(16,true),(20,true),(29,false)]
theorem inp_415 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_415 := by
  exact input_gate (activationGate5 SatVar.a (.i 6) 6) (activationA_mem 6) cl_415 (by decide) v h
end Percolation.Replay
