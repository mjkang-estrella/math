import NInputs155
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_9314 : CNF.NClause := [(343,true),(350,true),(352,true),(359,false),(361,true),(368,true)]
theorem inp_9314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9314 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 7) (closed_mem 7 7) cl_9314 (by decide) v hb
def cl_9315 : CNF.NClause := [(343,true),(350,true),(352,false),(359,true),(361,true),(368,true)]
theorem inp_9315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9315 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 7) (closed_mem 7 7) cl_9315 (by decide) v hb
def cl_9316 : CNF.NClause := [(343,true),(350,false),(352,true),(359,true),(361,true),(368,true)]
theorem inp_9316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9316 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 7) (closed_mem 7 7) cl_9316 (by decide) v hb
def cl_9317 : CNF.NClause := [(343,false),(350,true),(352,true),(359,true),(361,true),(368,true)]
theorem inp_9317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9317 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 7) (closed_mem 7 7) cl_9317 (by decide) v hb
def cl_9318 : CNF.NClause := [(344,true),(347,true),(355,true),(358,true),(361,true),(369,false)]
theorem inp_9318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9318 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 8) (closed_mem 7 8) cl_9318 (by decide) v hb
def cl_9319 : CNF.NClause := [(344,true),(347,true),(355,true),(358,true),(361,false),(369,true)]
theorem inp_9319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9319 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 8) (closed_mem 7 8) cl_9319 (by decide) v hb
def cl_9320 : CNF.NClause := [(344,true),(347,true),(355,true),(358,false),(361,true),(369,true)]
theorem inp_9320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9320 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 8) (closed_mem 7 8) cl_9320 (by decide) v hb
def cl_9322 : CNF.NClause := [(344,true),(347,false),(355,true),(358,true),(361,true),(369,true)]
theorem inp_9322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9322 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9322 v hb
def cl_9323 : CNF.NClause := [(344,false),(347,true),(355,true),(358,true),(361,true),(369,true)]
theorem inp_9323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9323 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 8) (closed_mem 7 8) cl_9323 (by decide) v hb
def cl_9328 : CNF.NClause := [(342,true),(348,false),(354,true),(360,true),(361,true),(367,true)]
theorem inp_9328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9328 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9328 v hb
def cl_9331 : CNF.NClause := [(351,true),(352,true),(353,true),(354,true),(355,false),(371,true)]
theorem inp_9331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9331 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 10) (closed_mem 7 10) cl_9331 (by decide) v hb
def cl_9332 : CNF.NClause := [(351,true),(352,true),(353,true),(354,false),(355,true),(371,true)]
theorem inp_9332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9332 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 10) (closed_mem 7 10) cl_9332 (by decide) v hb
def cl_9333 : CNF.NClause := [(351,true),(352,true),(353,false),(354,true),(355,true),(371,true)]
theorem inp_9333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9333 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 10) (closed_mem 7 10) cl_9333 (by decide) v hb
def cl_9334 : CNF.NClause := [(351,true),(352,false),(353,true),(354,true),(355,true),(371,true)]
theorem inp_9334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9334 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 10) (closed_mem 7 10) cl_9334 (by decide) v hb
def cl_9335 : CNF.NClause := [(351,false),(352,true),(353,true),(354,true),(355,true),(371,true)]
theorem inp_9335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9335 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 10) (closed_mem 7 10) cl_9335 (by decide) v hb
def cl_9340 : CNF.NClause := [(345,true),(348,false),(351,true),(359,true),(362,true),(369,true)]
theorem inp_9340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9340 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9340 v hb
def cl_9342 : CNF.NClause := [(343,true),(347,true),(351,true),(360,true),(364,true),(370,false)]
theorem inp_9342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9342 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 12) (closed_mem 7 12) cl_9342 (by decide) v hb
def cl_9343 : CNF.NClause := [(343,true),(347,true),(351,true),(360,true),(364,false),(370,true)]
theorem inp_9343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9343 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 12) (closed_mem 7 12) cl_9343 (by decide) v hb
def cl_9345 : CNF.NClause := [(343,true),(347,true),(351,false),(360,true),(364,true),(370,true)]
theorem inp_9345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9345 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 12) (closed_mem 7 12) cl_9345 (by decide) v hb
def cl_9346 : CNF.NClause := [(343,true),(347,false),(351,true),(360,true),(364,true),(370,true)]
theorem inp_9346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9346 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 12) (closed_mem 7 12) cl_9346 (by decide) v hb
def cl_9347 : CNF.NClause := [(343,false),(347,true),(351,true),(360,true),(364,true),(370,true)]
theorem inp_9347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9347 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 12) (closed_mem 7 12) cl_9347 (by decide) v hb
def cl_9349 : CNF.NClause := [(344,true),(350,true),(351,true),(357,true),(363,false),(367,true)]
theorem inp_9349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9349 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 13) (closed_mem 7 13) cl_9349 (by decide) v hb
def cl_9350 : CNF.NClause := [(344,true),(350,true),(351,true),(357,false),(363,true),(367,true)]
theorem inp_9350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9350 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 13) (closed_mem 7 13) cl_9350 (by decide) v hb
def cl_9351 : CNF.NClause := [(344,true),(350,true),(351,false),(357,true),(363,true),(367,true)]
theorem inp_9351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9351 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 13) (closed_mem 7 13) cl_9351 (by decide) v hb
def cl_9352 : CNF.NClause := [(344,true),(350,false),(351,true),(357,true),(363,true),(367,true)]
theorem inp_9352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9352 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 13) (closed_mem 7 13) cl_9352 (by decide) v hb
def cl_9353 : CNF.NClause := [(344,false),(350,true),(351,true),(357,true),(363,true),(367,true)]
theorem inp_9353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9353 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 13) (closed_mem 7 13) cl_9353 (by decide) v hb
def cl_9355 : CNF.NClause := [(342,true),(349,true),(351,true),(358,true),(365,false),(368,true)]
theorem inp_9355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9355 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 14) (closed_mem 7 14) cl_9355 (by decide) v hb
def cl_9357 : CNF.NClause := [(342,true),(349,true),(351,false),(358,true),(365,true),(368,true)]
theorem inp_9357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9357 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 14) (closed_mem 7 14) cl_9357 (by decide) v hb
def cl_9358 : CNF.NClause := [(342,true),(349,false),(351,true),(358,true),(365,true),(368,true)]
theorem inp_9358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9358 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 14) (closed_mem 7 14) cl_9358 (by decide) v hb
def cl_9359 : CNF.NClause := [(342,false),(349,true),(351,true),(358,true),(365,true),(368,true)]
theorem inp_9359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9359 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9359 v hb
def cl_9361 : CNF.NClause := [(356,true),(357,true),(358,true),(359,true),(360,false),(371,true)]
theorem inp_9361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9361 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 15) (closed_mem 7 15) cl_9361 (by decide) v hb
def cl_9362 : CNF.NClause := [(356,true),(357,true),(358,true),(359,false),(360,true),(371,true)]
theorem inp_9362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9362 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9362 v hb
def cl_9363 : CNF.NClause := [(356,true),(357,true),(358,false),(359,true),(360,true),(371,true)]
theorem inp_9363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9363 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 15) (closed_mem 7 15) cl_9363 (by decide) v hb
def cl_9364 : CNF.NClause := [(356,true),(357,false),(358,true),(359,true),(360,true),(371,true)]
theorem inp_9364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9364 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 15) (closed_mem 7 15) cl_9364 (by decide) v hb
def cl_9365 : CNF.NClause := [(356,false),(357,true),(358,true),(359,true),(360,true),(371,true)]
theorem inp_9365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9365 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 15) (closed_mem 7 15) cl_9365 (by decide) v hb
def cl_9368 : CNF.NClause := [(345,true),(347,true),(354,true),(356,false),(363,true),(368,true)]
theorem inp_9368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9368 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 16) (closed_mem 7 16) cl_9368 (by decide) v hb
def cl_9369 : CNF.NClause := [(345,true),(347,true),(354,false),(356,true),(363,true),(368,true)]
theorem inp_9369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9369 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 16) (closed_mem 7 16) cl_9369 (by decide) v hb
def cl_9370 : CNF.NClause := [(345,true),(347,false),(354,true),(356,true),(363,true),(368,true)]
theorem inp_9370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9370 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 16) (closed_mem 7 16) cl_9370 (by decide) v hb
def cl_9371 : CNF.NClause := [(345,false),(347,true),(354,true),(356,true),(363,true),(368,true)]
theorem inp_9371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9371 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 16) (closed_mem 7 16) cl_9371 (by decide) v hb
def cl_9373 : CNF.NClause := [(343,true),(349,true),(355,true),(356,true),(362,false),(367,true)]
theorem inp_9373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9373 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 17) (closed_mem 7 17) cl_9373 (by decide) v hb
def cl_9374 : CNF.NClause := [(343,true),(349,true),(355,true),(356,false),(362,true),(367,true)]
theorem inp_9374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9374 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 17) (closed_mem 7 17) cl_9374 (by decide) v hb
def cl_9375 : CNF.NClause := [(343,true),(349,true),(355,false),(356,true),(362,true),(367,true)]
theorem inp_9375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9375 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 17) (closed_mem 7 17) cl_9375 (by decide) v hb
def cl_9376 : CNF.NClause := [(343,true),(349,false),(355,true),(356,true),(362,true),(367,true)]
theorem inp_9376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9376 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 17) (closed_mem 7 17) cl_9376 (by decide) v hb
def cl_9377 : CNF.NClause := [(343,false),(349,true),(355,true),(356,true),(362,true),(367,true)]
theorem inp_9377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9377 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 17) (closed_mem 7 17) cl_9377 (by decide) v hb
def cl_9382 : CNF.NClause := [(344,true),(348,false),(352,true),(356,true),(365,true),(370,true)]
theorem inp_9382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9382 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 18) (closed_mem 7 18) cl_9382 (by decide) v hb
def cl_9384 : CNF.NClause := [(342,true),(350,true),(353,true),(356,true),(364,true),(369,false)]
theorem inp_9384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9384 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9384 v hb
def cl_9386 : CNF.NClause := [(342,true),(350,true),(353,true),(356,false),(364,true),(369,true)]
theorem inp_9386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9386 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 19) (closed_mem 7 19) cl_9386 (by decide) v hb
def cl_9387 : CNF.NClause := [(342,true),(350,true),(353,false),(356,true),(364,true),(369,true)]
theorem inp_9387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9387 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 19) (closed_mem 7 19) cl_9387 (by decide) v hb
def cl_9388 : CNF.NClause := [(342,true),(350,false),(353,true),(356,true),(364,true),(369,true)]
theorem inp_9388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9388 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 19) (closed_mem 7 19) cl_9388 (by decide) v hb
def cl_9389 : CNF.NClause := [(342,false),(350,true),(353,true),(356,true),(364,true),(369,true)]
theorem inp_9389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9389 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 19) (closed_mem 7 19) cl_9389 (by decide) v hb
end Percolation.NReplay
