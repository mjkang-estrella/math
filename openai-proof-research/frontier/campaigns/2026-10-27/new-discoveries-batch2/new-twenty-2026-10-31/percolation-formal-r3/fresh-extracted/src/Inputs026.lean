import Inputs025
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_2379 : CNF.NClause := [(99,true),(35,false),(39,true),(43,false),(47,true),(51,false),(60,false)]
theorem inp_2379 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2379 := by
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2379 (by decide) v h
def cl_2383 : CNF.NClause := [(99,true),(35,false),(39,true),(43,true),(47,true),(51,false),(60,false)]
theorem inp_2383 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2383 := by
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2383 (by decide) v h
def cl_2393 : CNF.NClause := [(99,true),(35,false),(39,false),(43,false),(47,true),(51,true),(60,false)]
theorem inp_2393 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2393 := by
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2393 (by decide) v h
def cl_2395 : CNF.NClause := [(99,true),(35,false),(39,true),(43,false),(47,true),(51,true),(60,false)]
theorem inp_2395 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2395 := by
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2395 (by decide) v h
def cl_2399 : CNF.NClause := [(99,true),(35,false),(39,true),(43,true),(47,true),(51,true),(60,false)]
theorem inp_2399 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2399 := by
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2399 (by decide) v h
def cl_2401 : CNF.NClause := [(99,true),(35,false),(39,false),(43,false),(47,false),(51,false),(60,true)]
theorem inp_2401 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2401 := by
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2401 (by decide) v h
def cl_2402 : CNF.NClause := [(99,true),(35,true),(39,false),(43,false),(47,false),(51,false),(60,true)]
theorem inp_2402 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2402 := by
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2402 (by decide) v h
def cl_2407 : CNF.NClause := [(99,true),(35,false),(39,true),(43,true),(47,false),(51,false),(60,true)]
theorem inp_2407 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2407 := by
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2407 (by decide) v h
def cl_2409 : CNF.NClause := [(99,true),(35,false),(39,false),(43,false),(47,true),(51,false),(60,true)]
theorem inp_2409 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2409 := by
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2409 (by decide) v h
def cl_2411 : CNF.NClause := [(99,true),(35,false),(39,true),(43,false),(47,true),(51,false),(60,true)]
theorem inp_2411 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2411 := by
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2411 (by decide) v h
def cl_2415 : CNF.NClause := [(99,true),(35,false),(39,true),(43,true),(47,true),(51,false),(60,true)]
theorem inp_2415 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2415 := by
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2415 (by decide) v h
def cl_2425 : CNF.NClause := [(99,true),(35,false),(39,false),(43,false),(47,true),(51,true),(60,true)]
theorem inp_2425 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2425 := by
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2425 (by decide) v h
def cl_2427 : CNF.NClause := [(99,true),(35,false),(39,true),(43,false),(47,true),(51,true),(60,true)]
theorem inp_2427 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2427 := by
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) cl_2427 (by decide) v h
def cl_2433 : CNF.NClause := [(100,true),(33,false),(40,false),(42,false),(49,false),(51,false),(58,false)]
theorem inp_2433 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2433 := by
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2433 (by decide) v h
def cl_2435 : CNF.NClause := [(100,true),(33,false),(40,true),(42,false),(49,false),(51,false),(58,false)]
theorem inp_2435 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2435 := by
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2435 (by decide) v h
def cl_2437 : CNF.NClause := [(100,true),(33,false),(40,false),(42,true),(49,false),(51,false),(58,false)]
theorem inp_2437 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2437 := by
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2437 (by decide) v h
def cl_2440 : CNF.NClause := [(100,true),(33,true),(40,true),(42,true),(49,false),(51,false),(58,false)]
theorem inp_2440 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2440 := by
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2440 (by decide) v h
def cl_2449 : CNF.NClause := [(100,true),(33,false),(40,false),(42,false),(49,false),(51,true),(58,false)]
theorem inp_2449 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2449 := by
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2449 (by decide) v h
def cl_2453 : CNF.NClause := [(100,true),(33,false),(40,false),(42,true),(49,false),(51,true),(58,false)]
theorem inp_2453 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2453 := by
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2453 (by decide) v h
def cl_2467 : CNF.NClause := [(100,true),(33,false),(40,true),(42,false),(49,false),(51,false),(58,true)]
theorem inp_2467 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2467 := by
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2467 (by decide) v h
def cl_2468 : CNF.NClause := [(100,true),(33,true),(40,true),(42,false),(49,false),(51,false),(58,true)]
theorem inp_2468 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2468 := by
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2468 (by decide) v h
def cl_2471 : CNF.NClause := [(100,true),(33,false),(40,true),(42,true),(49,false),(51,false),(58,true)]
theorem inp_2471 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2471 := by
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2471 (by decide) v h
def cl_2472 : CNF.NClause := [(100,true),(33,true),(40,true),(42,true),(49,false),(51,false),(58,true)]
theorem inp_2472 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2472 := by
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2472 (by decide) v h
def cl_2475 : CNF.NClause := [(100,true),(33,false),(40,true),(42,false),(49,true),(51,false),(58,true)]
theorem inp_2475 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2475 := by
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2475 (by decide) v h
def cl_2481 : CNF.NClause := [(100,true),(33,false),(40,false),(42,false),(49,false),(51,true),(58,true)]
theorem inp_2481 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2481 := by
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2481 (by decide) v h
def cl_2483 : CNF.NClause := [(100,true),(33,false),(40,true),(42,false),(49,false),(51,true),(58,true)]
theorem inp_2483 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2483 := by
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2483 (by decide) v h
def cl_2484 : CNF.NClause := [(100,true),(33,true),(40,true),(42,false),(49,false),(51,true),(58,true)]
theorem inp_2484 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2484 := by
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2484 (by decide) v h
def cl_2485 : CNF.NClause := [(100,true),(33,false),(40,false),(42,true),(49,false),(51,true),(58,true)]
theorem inp_2485 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2485 := by
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2485 (by decide) v h
def cl_2487 : CNF.NClause := [(100,true),(33,false),(40,true),(42,true),(49,false),(51,true),(58,true)]
theorem inp_2487 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2487 := by
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2487 (by decide) v h
def cl_2489 : CNF.NClause := [(100,true),(33,false),(40,false),(42,false),(49,true),(51,true),(58,true)]
theorem inp_2489 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2489 := by
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2489 (by decide) v h
def cl_2491 : CNF.NClause := [(100,true),(33,false),(40,true),(42,false),(49,true),(51,true),(58,true)]
theorem inp_2491 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2491 := by
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) cl_2491 (by decide) v h
def cl_2497 : CNF.NClause := [(101,true),(34,false),(37,false),(45,false),(48,false),(51,false),(59,false)]
theorem inp_2497 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2497 := by
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2497 (by decide) v h
def cl_2499 : CNF.NClause := [(101,true),(34,false),(37,true),(45,false),(48,false),(51,false),(59,false)]
theorem inp_2499 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2499 := by
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2499 (by decide) v h
def cl_2508 : CNF.NClause := [(101,true),(34,true),(37,true),(45,false),(48,true),(51,false),(59,false)]
theorem inp_2508 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2508 := by
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2508 (by decide) v h
def cl_2515 : CNF.NClause := [(101,true),(34,false),(37,true),(45,false),(48,false),(51,true),(59,false)]
theorem inp_2515 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2515 := by
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2515 (by decide) v h
def cl_2516 : CNF.NClause := [(101,true),(34,true),(37,true),(45,false),(48,false),(51,true),(59,false)]
theorem inp_2516 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2516 := by
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2516 (by decide) v h
def cl_2531 : CNF.NClause := [(101,true),(34,false),(37,true),(45,false),(48,false),(51,false),(59,true)]
theorem inp_2531 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2531 := by
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2531 (by decide) v h
def cl_2532 : CNF.NClause := [(101,true),(34,true),(37,true),(45,false),(48,false),(51,false),(59,true)]
theorem inp_2532 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2532 := by
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2532 (by decide) v h
def cl_2540 : CNF.NClause := [(101,true),(34,true),(37,true),(45,false),(48,true),(51,false),(59,true)]
theorem inp_2540 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2540 := by
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2540 (by decide) v h
def cl_2547 : CNF.NClause := [(101,true),(34,false),(37,true),(45,false),(48,false),(51,true),(59,true)]
theorem inp_2547 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2547 := by
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2547 (by decide) v h
def cl_2548 : CNF.NClause := [(101,true),(34,true),(37,true),(45,false),(48,false),(51,true),(59,true)]
theorem inp_2548 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2548 := by
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) cl_2548 (by decide) v h
def cl_2563 : CNF.NClause := [(102,true),(32,false),(38,true),(44,false),(50,false),(51,false),(57,false)]
theorem inp_2563 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2563 := by
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2563 (by decide) v h
def cl_2564 : CNF.NClause := [(102,true),(32,true),(38,true),(44,false),(50,false),(51,false),(57,false)]
theorem inp_2564 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2564 := by
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2564 (by decide) v h
def cl_2579 : CNF.NClause := [(102,true),(32,false),(38,true),(44,false),(50,false),(51,true),(57,false)]
theorem inp_2579 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2579 := by
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2579 (by decide) v h
def cl_2595 : CNF.NClause := [(102,true),(32,false),(38,true),(44,false),(50,false),(51,false),(57,true)]
theorem inp_2595 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2595 := by
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2595 (by decide) v h
def cl_2599 : CNF.NClause := [(102,true),(32,false),(38,true),(44,true),(50,false),(51,false),(57,true)]
theorem inp_2599 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2599 := by
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2599 (by decide) v h
def cl_2603 : CNF.NClause := [(102,true),(32,false),(38,true),(44,false),(50,true),(51,false),(57,true)]
theorem inp_2603 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2603 := by
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2603 (by decide) v h
def cl_2611 : CNF.NClause := [(102,true),(32,false),(38,true),(44,false),(50,false),(51,true),(57,true)]
theorem inp_2611 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2611 := by
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2611 (by decide) v h
def cl_2615 : CNF.NClause := [(102,true),(32,false),(38,true),(44,true),(50,false),(51,true),(57,true)]
theorem inp_2615 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2615 := by
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2615 (by decide) v h
def cl_2619 : CNF.NClause := [(102,true),(32,false),(38,true),(44,false),(50,true),(51,true),(57,true)]
theorem inp_2619 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2619 := by
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) cl_2619 (by decide) v h
end Percolation.Replay
