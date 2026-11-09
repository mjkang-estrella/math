import NInputs190
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_12421 : CNF.NClause := [(837,true),(843,true),(849,true),(855,true),(861,false),(863,true)]
theorem inp_12421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12421 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 29) (closed_mem 23 29) cl_12421 (by decide) v hb
def cl_12422 : CNF.NClause := [(837,true),(843,true),(849,true),(855,false),(861,true),(863,true)]
theorem inp_12422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12422 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 29) (closed_mem 23 29) cl_12422 (by decide) v hb
def cl_12423 : CNF.NClause := [(837,true),(843,true),(849,false),(855,true),(861,true),(863,true)]
theorem inp_12423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12423 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 29) (closed_mem 23 29) cl_12423 (by decide) v hb
def cl_12424 : CNF.NClause := [(837,true),(843,false),(849,true),(855,true),(861,true),(863,true)]
theorem inp_12424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12424 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 29) (closed_mem 23 29) cl_12424 (by decide) v hb
def cl_12427 : CNF.NClause := [(837,true),(842,true),(847,true),(852,true),(857,false),(862,true)]
theorem inp_12427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12427 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 30) (closed_mem 23 30) cl_12427 (by decide) v hb
def cl_12428 : CNF.NClause := [(837,true),(842,true),(847,true),(852,false),(857,true),(862,true)]
theorem inp_12428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12428 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 30) (closed_mem 23 30) cl_12428 (by decide) v hb
def cl_12429 : CNF.NClause := [(837,true),(842,true),(847,false),(852,true),(857,true),(862,true)]
theorem inp_12429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12429 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 30) (closed_mem 23 30) cl_12429 (by decide) v hb
def cl_12430 : CNF.NClause := [(837,true),(842,false),(847,true),(852,true),(857,true),(862,true)]
theorem inp_12430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12430 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 30) (closed_mem 23 30) cl_12430 (by decide) v hb
def cl_12433 : CNF.NClause := [(893,true),(894,true),(895,true),(896,true),(897,false),(898,true)]
theorem inp_12433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12433 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 0) (closed_mem 24 0) cl_12433 (by decide) v hb
def cl_12434 : CNF.NClause := [(893,true),(894,true),(895,true),(896,false),(897,true),(898,true)]
theorem inp_12434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12434 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 0) (closed_mem 24 0) cl_12434 (by decide) v hb
def cl_12435 : CNF.NClause := [(893,true),(894,true),(895,false),(896,true),(897,true),(898,true)]
theorem inp_12435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12435 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 0) (closed_mem 24 0) cl_12435 (by decide) v hb
def cl_12436 : CNF.NClause := [(893,true),(894,false),(895,true),(896,true),(897,true),(898,true)]
theorem inp_12436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12436 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 0) (closed_mem 24 0) cl_12436 (by decide) v hb
def cl_12439 : CNF.NClause := [(872,true),(877,true),(882,true),(887,true),(892,false),(893,true)]
theorem inp_12439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12439 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 1) (closed_mem 24 1) cl_12439 (by decide) v hb
def cl_12445 : CNF.NClause := [(870,true),(875,true),(880,true),(885,true),(890,false),(893,true)]
theorem inp_12445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12445 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 2) (closed_mem 24 2) cl_12445 (by decide) v hb
def cl_12446 : CNF.NClause := [(870,true),(875,true),(880,true),(885,false),(890,true),(893,true)]
theorem inp_12446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12446 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 2) (closed_mem 24 2) cl_12446 (by decide) v hb
def cl_12449 : CNF.NClause := [(870,false),(875,true),(880,true),(885,true),(890,true),(893,true)]
theorem inp_12449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12449 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 2) (closed_mem 24 2) cl_12449 (by decide) v hb
def cl_12451 : CNF.NClause := [(871,true),(876,true),(881,true),(886,true),(891,false),(893,true)]
theorem inp_12451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12451 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 3) (closed_mem 24 3) cl_12451 (by decide) v hb
def cl_12452 : CNF.NClause := [(871,true),(876,true),(881,true),(886,false),(891,true),(893,true)]
theorem inp_12452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12452 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 3) (closed_mem 24 3) cl_12452 (by decide) v hb
def cl_12454 : CNF.NClause := [(871,true),(876,false),(881,true),(886,true),(891,true),(893,true)]
theorem inp_12454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12454 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 3) (closed_mem 24 3) cl_12454 (by decide) v hb
def cl_12455 : CNF.NClause := [(871,false),(876,true),(881,true),(886,true),(891,true),(893,true)]
theorem inp_12455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12455 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 3) (closed_mem 24 3) cl_12455 (by decide) v hb
def cl_12457 : CNF.NClause := [(869,true),(874,true),(879,true),(884,true),(889,false),(893,true)]
theorem inp_12457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12457 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 4) (closed_mem 24 4) cl_12457 (by decide) v hb
def cl_12458 : CNF.NClause := [(869,true),(874,true),(879,true),(884,false),(889,true),(893,true)]
theorem inp_12458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12458 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 4) (closed_mem 24 4) cl_12458 (by decide) v hb
def cl_12459 : CNF.NClause := [(869,true),(874,true),(879,false),(884,true),(889,true),(893,true)]
theorem inp_12459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12459 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 4) (closed_mem 24 4) cl_12459 (by decide) v hb
def cl_12460 : CNF.NClause := [(869,true),(874,false),(879,true),(884,true),(889,true),(893,true)]
theorem inp_12460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12460 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 4) (closed_mem 24 4) cl_12460 (by decide) v hb
def cl_12461 : CNF.NClause := [(869,false),(874,true),(879,true),(884,true),(889,true),(893,true)]
theorem inp_12461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12461 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 4) (closed_mem 24 4) cl_12461 (by decide) v hb
def cl_12463 : CNF.NClause := [(888,true),(889,true),(890,true),(891,true),(892,false),(898,true)]
theorem inp_12463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12463 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 5) (closed_mem 24 5) cl_12463 (by decide) v hb
def cl_12470 : CNF.NClause := [(872,true),(876,true),(880,true),(884,false),(888,true),(897,true)]
theorem inp_12470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12470 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 6) (closed_mem 24 6) cl_12470 (by decide) v hb
def cl_12471 : CNF.NClause := [(872,true),(876,true),(880,false),(884,true),(888,true),(897,true)]
theorem inp_12471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12471 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 6) (closed_mem 24 6) cl_12471 (by decide) v hb
def cl_12473 : CNF.NClause := [(872,false),(876,true),(880,true),(884,true),(888,true),(897,true)]
theorem inp_12473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12473 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 6) (closed_mem 24 6) cl_12473 (by decide) v hb
def cl_12477 : CNF.NClause := [(870,true),(877,true),(879,false),(886,true),(888,true),(895,true)]
theorem inp_12477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12477 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 7) (closed_mem 24 7) cl_12477 (by decide) v hb
def cl_12479 : CNF.NClause := [(870,false),(877,true),(879,true),(886,true),(888,true),(895,true)]
theorem inp_12479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12479 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 7) (closed_mem 24 7) cl_12479 (by decide) v hb
def cl_12480 : CNF.NClause := [(871,true),(874,true),(882,true),(885,true),(888,true),(896,false)]
theorem inp_12480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12480 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 8) (closed_mem 24 8) cl_12480 (by decide) v hb
def cl_12483 : CNF.NClause := [(871,true),(874,true),(882,false),(885,true),(888,true),(896,true)]
theorem inp_12483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12483 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 8) (closed_mem 24 8) cl_12483 (by decide) v hb
def cl_12484 : CNF.NClause := [(871,true),(874,false),(882,true),(885,true),(888,true),(896,true)]
theorem inp_12484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12484 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 8) (closed_mem 24 8) cl_12484 (by decide) v hb
def cl_12485 : CNF.NClause := [(871,false),(874,true),(882,true),(885,true),(888,true),(896,true)]
theorem inp_12485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12485 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 8) (closed_mem 24 8) cl_12485 (by decide) v hb
def cl_12486 : CNF.NClause := [(869,true),(875,true),(881,true),(887,true),(888,true),(894,false)]
theorem inp_12486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12486 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 9) (closed_mem 24 9) cl_12486 (by decide) v hb
def cl_12487 : CNF.NClause := [(869,true),(875,true),(881,true),(887,true),(888,false),(894,true)]
theorem inp_12487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12487 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 9) (closed_mem 24 9) cl_12487 (by decide) v hb
def cl_12488 : CNF.NClause := [(869,true),(875,true),(881,true),(887,false),(888,true),(894,true)]
theorem inp_12488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12488 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 9) (closed_mem 24 9) cl_12488 (by decide) v hb
def cl_12489 : CNF.NClause := [(869,true),(875,true),(881,false),(887,true),(888,true),(894,true)]
theorem inp_12489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12489 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 9) (closed_mem 24 9) cl_12489 (by decide) v hb
def cl_12491 : CNF.NClause := [(869,false),(875,true),(881,true),(887,true),(888,true),(894,true)]
theorem inp_12491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12491 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 9) (closed_mem 24 9) cl_12491 (by decide) v hb
def cl_12493 : CNF.NClause := [(878,true),(879,true),(880,true),(881,true),(882,false),(898,true)]
theorem inp_12493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12493 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 10) (closed_mem 24 10) cl_12493 (by decide) v hb
def cl_12495 : CNF.NClause := [(878,true),(879,true),(880,false),(881,true),(882,true),(898,true)]
theorem inp_12495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12495 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 10) (closed_mem 24 10) cl_12495 (by decide) v hb
def cl_12496 : CNF.NClause := [(878,true),(879,false),(880,true),(881,true),(882,true),(898,true)]
theorem inp_12496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12496 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 10) (closed_mem 24 10) cl_12496 (by decide) v hb
def cl_12497 : CNF.NClause := [(878,false),(879,true),(880,true),(881,true),(882,true),(898,true)]
theorem inp_12497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12497 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 10) (closed_mem 24 10) cl_12497 (by decide) v hb
def cl_12498 : CNF.NClause := [(872,true),(875,true),(878,true),(886,true),(889,true),(896,false)]
theorem inp_12498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12498 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 11) (closed_mem 24 11) cl_12498 (by decide) v hb
def cl_12502 : CNF.NClause := [(872,true),(875,false),(878,true),(886,true),(889,true),(896,true)]
theorem inp_12502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12502 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 11) (closed_mem 24 11) cl_12502 (by decide) v hb
def cl_12503 : CNF.NClause := [(872,false),(875,true),(878,true),(886,true),(889,true),(896,true)]
theorem inp_12503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12503 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 11) (closed_mem 24 11) cl_12503 (by decide) v hb
def cl_12504 : CNF.NClause := [(870,true),(874,true),(878,true),(887,true),(891,true),(897,false)]
theorem inp_12504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12504 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 12) (closed_mem 24 12) cl_12504 (by decide) v hb
def cl_12505 : CNF.NClause := [(870,true),(874,true),(878,true),(887,true),(891,false),(897,true)]
theorem inp_12505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12505 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 12) (closed_mem 24 12) cl_12505 (by decide) v hb
def cl_12506 : CNF.NClause := [(870,true),(874,true),(878,true),(887,false),(891,true),(897,true)]
theorem inp_12506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12506 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 24 12) (closed_mem 24 12) cl_12506 (by decide) v hb
end Percolation.NReplay
