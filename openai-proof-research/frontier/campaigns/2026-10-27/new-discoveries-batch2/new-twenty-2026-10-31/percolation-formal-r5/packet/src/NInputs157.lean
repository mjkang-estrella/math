import NInputs156
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_9393 : CNF.NClause := [(346,true),(347,true),(348,false),(349,true),(350,true),(371,true)]
theorem inp_9393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9393 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9393 v hb
def cl_9397 : CNF.NClause := [(345,true),(346,true),(352,true),(358,true),(364,false),(367,true)]
theorem inp_9397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9397 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 21) (closed_mem 7 21) cl_9397 (by decide) v hb
def cl_9399 : CNF.NClause := [(345,true),(346,true),(352,false),(358,true),(364,true),(367,true)]
theorem inp_9399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9399 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 21) (closed_mem 7 21) cl_9399 (by decide) v hb
def cl_9400 : CNF.NClause := [(345,true),(346,false),(352,true),(358,true),(364,true),(367,true)]
theorem inp_9400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9400 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 21) (closed_mem 7 21) cl_9400 (by decide) v hb
def cl_9402 : CNF.NClause := [(343,true),(346,true),(354,true),(357,true),(365,true),(369,false)]
theorem inp_9402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9402 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 22) (closed_mem 7 22) cl_9402 (by decide) v hb
def cl_9404 : CNF.NClause := [(343,true),(346,true),(354,true),(357,false),(365,true),(369,true)]
theorem inp_9404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9404 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 22) (closed_mem 7 22) cl_9404 (by decide) v hb
def cl_9405 : CNF.NClause := [(343,true),(346,true),(354,false),(357,true),(365,true),(369,true)]
theorem inp_9405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9405 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 22) (closed_mem 7 22) cl_9405 (by decide) v hb
def cl_9406 : CNF.NClause := [(343,true),(346,false),(354,true),(357,true),(365,true),(369,true)]
theorem inp_9406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9406 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 22) (closed_mem 7 22) cl_9406 (by decide) v hb
def cl_9407 : CNF.NClause := [(343,false),(346,true),(354,true),(357,true),(365,true),(369,true)]
theorem inp_9407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9407 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 22) (closed_mem 7 22) cl_9407 (by decide) v hb
def cl_9408 : CNF.NClause := [(344,true),(346,true),(353,true),(360,true),(362,true),(368,false)]
theorem inp_9408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9408 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 23) (closed_mem 7 23) cl_9408 (by decide) v hb
def cl_9409 : CNF.NClause := [(344,true),(346,true),(353,true),(360,true),(362,false),(368,true)]
theorem inp_9409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9409 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 23) (closed_mem 7 23) cl_9409 (by decide) v hb
def cl_9410 : CNF.NClause := [(344,true),(346,true),(353,true),(360,false),(362,true),(368,true)]
theorem inp_9410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9410 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 23) (closed_mem 7 23) cl_9410 (by decide) v hb
def cl_9411 : CNF.NClause := [(344,true),(346,true),(353,false),(360,true),(362,true),(368,true)]
theorem inp_9411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9411 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9411 v hb
def cl_9412 : CNF.NClause := [(344,true),(346,false),(353,true),(360,true),(362,true),(368,true)]
theorem inp_9412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9412 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 23) (closed_mem 7 23) cl_9412 (by decide) v hb
def cl_9413 : CNF.NClause := [(344,false),(346,true),(353,true),(360,true),(362,true),(368,true)]
theorem inp_9413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9413 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 23) (closed_mem 7 23) cl_9413 (by decide) v hb
def cl_9415 : CNF.NClause := [(342,true),(346,true),(355,true),(359,true),(363,false),(370,true)]
theorem inp_9415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9415 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 24) (closed_mem 7 24) cl_9415 (by decide) v hb
def cl_9417 : CNF.NClause := [(342,true),(346,true),(355,false),(359,true),(363,true),(370,true)]
theorem inp_9417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9417 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9417 v hb
def cl_9418 : CNF.NClause := [(342,true),(346,false),(355,true),(359,true),(363,true),(370,true)]
theorem inp_9418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9418 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 24) (closed_mem 7 24) cl_9418 (by decide) v hb
def cl_9419 : CNF.NClause := [(342,false),(346,true),(355,true),(359,true),(363,true),(370,true)]
theorem inp_9419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9419 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 24) (closed_mem 7 24) cl_9419 (by decide) v hb
def cl_9421 : CNF.NClause := [(341,true),(342,true),(343,true),(344,true),(345,false),(371,true)]
theorem inp_9421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9421 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 25) (closed_mem 7 25) cl_9421 (by decide) v hb
def cl_9422 : CNF.NClause := [(341,true),(342,true),(343,true),(344,false),(345,true),(371,true)]
theorem inp_9422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9422 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 25) (closed_mem 7 25) cl_9422 (by decide) v hb
def cl_9423 : CNF.NClause := [(341,true),(342,true),(343,false),(344,true),(345,true),(371,true)]
theorem inp_9423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9423 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 25) (closed_mem 7 25) cl_9423 (by decide) v hb
def cl_9424 : CNF.NClause := [(341,true),(342,false),(343,true),(344,true),(345,true),(371,true)]
theorem inp_9424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9424 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 25) (closed_mem 7 25) cl_9424 (by decide) v hb
def cl_9426 : CNF.NClause := [(341,true),(350,true),(354,true),(358,true),(362,true),(370,false)]
theorem inp_9426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9426 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 26) (closed_mem 7 26) cl_9426 (by decide) v hb
def cl_9427 : CNF.NClause := [(341,true),(350,true),(354,true),(358,true),(362,false),(370,true)]
theorem inp_9427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9427 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 26) (closed_mem 7 26) cl_9427 (by decide) v hb
def cl_9428 : CNF.NClause := [(341,true),(350,true),(354,true),(358,false),(362,true),(370,true)]
theorem inp_9428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9428 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 26) (closed_mem 7 26) cl_9428 (by decide) v hb
def cl_9429 : CNF.NClause := [(341,true),(350,true),(354,false),(358,true),(362,true),(370,true)]
theorem inp_9429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9429 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 26) (closed_mem 7 26) cl_9429 (by decide) v hb
def cl_9430 : CNF.NClause := [(341,true),(350,false),(354,true),(358,true),(362,true),(370,true)]
theorem inp_9430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9430 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 26) (closed_mem 7 26) cl_9430 (by decide) v hb
def cl_9436 : CNF.NClause := [(341,true),(348,false),(355,true),(357,true),(364,true),(368,true)]
theorem inp_9436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9436 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9436 v hb
def cl_9438 : CNF.NClause := [(341,true),(349,true),(352,true),(360,true),(363,true),(369,false)]
theorem inp_9438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9438 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9438 v hb
def cl_9439 : CNF.NClause := [(341,true),(349,true),(352,true),(360,true),(363,false),(369,true)]
theorem inp_9439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9439 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 28) (closed_mem 7 28) cl_9439 (by decide) v hb
def cl_9441 : CNF.NClause := [(341,true),(349,true),(352,false),(360,true),(363,true),(369,true)]
theorem inp_9441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9441 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 28) (closed_mem 7 28) cl_9441 (by decide) v hb
def cl_9442 : CNF.NClause := [(341,true),(349,false),(352,true),(360,true),(363,true),(369,true)]
theorem inp_9442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9442 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 28) (closed_mem 7 28) cl_9442 (by decide) v hb
def cl_9444 : CNF.NClause := [(341,true),(347,true),(353,true),(359,true),(365,true),(367,false)]
theorem inp_9444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9444 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 29) (closed_mem 7 29) cl_9444 (by decide) v hb
def cl_9445 : CNF.NClause := [(341,true),(347,true),(353,true),(359,true),(365,false),(367,true)]
theorem inp_9445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9445 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 29) (closed_mem 7 29) cl_9445 (by decide) v hb
def cl_9446 : CNF.NClause := [(341,true),(347,true),(353,true),(359,false),(365,true),(367,true)]
theorem inp_9446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9446 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 29) (closed_mem 7 29) cl_9446 (by decide) v hb
def cl_9447 : CNF.NClause := [(341,true),(347,true),(353,false),(359,true),(365,true),(367,true)]
theorem inp_9447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9447 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 29) (closed_mem 7 29) cl_9447 (by decide) v hb
def cl_9448 : CNF.NClause := [(341,true),(347,false),(353,true),(359,true),(365,true),(367,true)]
theorem inp_9448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9448 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 29) (closed_mem 7 29) cl_9448 (by decide) v hb
def cl_9451 : CNF.NClause := [(341,true),(346,true),(351,true),(356,true),(361,false),(366,true)]
theorem inp_9451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9451 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 30) (closed_mem 7 30) cl_9451 (by decide) v hb
def cl_9452 : CNF.NClause := [(341,true),(346,true),(351,true),(356,false),(361,true),(366,true)]
theorem inp_9452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9452 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 30) (closed_mem 7 30) cl_9452 (by decide) v hb
def cl_9453 : CNF.NClause := [(341,true),(346,true),(351,false),(356,true),(361,true),(366,true)]
theorem inp_9453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9453 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 30) (closed_mem 7 30) cl_9453 (by decide) v hb
def cl_9454 : CNF.NClause := [(341,true),(346,false),(351,true),(356,true),(361,true),(366,true)]
theorem inp_9454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9454 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 30) (closed_mem 7 30) cl_9454 (by decide) v hb
def cl_9457 : CNF.NClause := [(397,true),(398,true),(399,true),(400,true),(401,false),(402,true)]
theorem inp_9457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9457 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9457 v hb
def cl_9458 : CNF.NClause := [(397,true),(398,true),(399,true),(400,false),(401,true),(402,true)]
theorem inp_9458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9458 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 0) (closed_mem 8 0) cl_9458 (by decide) v hb
def cl_9459 : CNF.NClause := [(397,true),(398,true),(399,false),(400,true),(401,true),(402,true)]
theorem inp_9459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9459 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 0) (closed_mem 8 0) cl_9459 (by decide) v hb
def cl_9460 : CNF.NClause := [(397,true),(398,false),(399,true),(400,true),(401,true),(402,true)]
theorem inp_9460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9460 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 0) (closed_mem 8 0) cl_9460 (by decide) v hb
def cl_9463 : CNF.NClause := [(376,true),(381,true),(386,true),(391,true),(396,false),(397,true)]
theorem inp_9463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9463 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 1) (closed_mem 8 1) cl_9463 (by decide) v hb
def cl_9464 : CNF.NClause := [(376,true),(381,true),(386,true),(391,false),(396,true),(397,true)]
theorem inp_9464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9464 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 1) (closed_mem 8 1) cl_9464 (by decide) v hb
def cl_9465 : CNF.NClause := [(376,true),(381,true),(386,false),(391,true),(396,true),(397,true)]
theorem inp_9465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9465 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 1) (closed_mem 8 1) cl_9465 (by decide) v hb
def cl_9467 : CNF.NClause := [(376,false),(381,true),(386,true),(391,true),(396,true),(397,true)]
theorem inp_9467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9467 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 1) (closed_mem 8 1) cl_9467 (by decide) v hb
end Percolation.NReplay
