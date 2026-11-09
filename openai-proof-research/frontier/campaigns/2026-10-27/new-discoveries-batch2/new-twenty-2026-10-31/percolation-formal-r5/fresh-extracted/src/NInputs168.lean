import NInputs167
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_10332 : CNF.NClause := [(498,true),(501,true),(509,true),(512,true),(520,true),(524,false)]
theorem inp_10332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10332 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 22) (closed_mem 12 22) cl_10332 (by decide) v hb
def cl_10333 : CNF.NClause := [(498,true),(501,true),(509,true),(512,true),(520,false),(524,true)]
theorem inp_10333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10333 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 22) (closed_mem 12 22) cl_10333 (by decide) v hb
def cl_10334 : CNF.NClause := [(498,true),(501,true),(509,true),(512,false),(520,true),(524,true)]
theorem inp_10334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10334 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 22) (closed_mem 12 22) cl_10334 (by decide) v hb
def cl_10335 : CNF.NClause := [(498,true),(501,true),(509,false),(512,true),(520,true),(524,true)]
theorem inp_10335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10335 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 22) (closed_mem 12 22) cl_10335 (by decide) v hb
def cl_10336 : CNF.NClause := [(498,true),(501,false),(509,true),(512,true),(520,true),(524,true)]
theorem inp_10336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10336 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 22) (closed_mem 12 22) cl_10336 (by decide) v hb
def cl_10337 : CNF.NClause := [(498,false),(501,true),(509,true),(512,true),(520,true),(524,true)]
theorem inp_10337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10337 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 22) (closed_mem 12 22) cl_10337 (by decide) v hb
def cl_10341 : CNF.NClause := [(499,true),(501,true),(508,false),(515,true),(517,true),(523,true)]
theorem inp_10341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10341 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 23) (closed_mem 12 23) cl_10341 (by decide) v hb
def cl_10344 : CNF.NClause := [(497,true),(501,true),(510,true),(514,true),(518,true),(525,false)]
theorem inp_10344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10344 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 24) (closed_mem 12 24) cl_10344 (by decide) v hb
def cl_10345 : CNF.NClause := [(497,true),(501,true),(510,true),(514,true),(518,false),(525,true)]
theorem inp_10345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10345 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 24) (closed_mem 12 24) cl_10345 (by decide) v hb
def cl_10346 : CNF.NClause := [(497,true),(501,true),(510,true),(514,false),(518,true),(525,true)]
theorem inp_10346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10346 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 24) (closed_mem 12 24) cl_10346 (by decide) v hb
def cl_10347 : CNF.NClause := [(497,true),(501,true),(510,false),(514,true),(518,true),(525,true)]
theorem inp_10347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10347 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 24) (closed_mem 12 24) cl_10347 (by decide) v hb
def cl_10349 : CNF.NClause := [(497,false),(501,true),(510,true),(514,true),(518,true),(525,true)]
theorem inp_10349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10349 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 24) (closed_mem 12 24) cl_10349 (by decide) v hb
def cl_10351 : CNF.NClause := [(496,true),(497,true),(498,true),(499,true),(500,false),(526,true)]
theorem inp_10351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10351 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 25) (closed_mem 12 25) cl_10351 (by decide) v hb
def cl_10352 : CNF.NClause := [(496,true),(497,true),(498,true),(499,false),(500,true),(526,true)]
theorem inp_10352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10352 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 25) (closed_mem 12 25) cl_10352 (by decide) v hb
def cl_10353 : CNF.NClause := [(496,true),(497,true),(498,false),(499,true),(500,true),(526,true)]
theorem inp_10353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10353 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 25) (closed_mem 12 25) cl_10353 (by decide) v hb
def cl_10354 : CNF.NClause := [(496,true),(497,false),(498,true),(499,true),(500,true),(526,true)]
theorem inp_10354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10354 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 25) (closed_mem 12 25) cl_10354 (by decide) v hb
def cl_10356 : CNF.NClause := [(496,true),(505,true),(509,true),(513,true),(517,true),(525,false)]
theorem inp_10356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10356 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 26) (closed_mem 12 26) cl_10356 (by decide) v hb
def cl_10357 : CNF.NClause := [(496,true),(505,true),(509,true),(513,true),(517,false),(525,true)]
theorem inp_10357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10357 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 26) (closed_mem 12 26) cl_10357 (by decide) v hb
def cl_10358 : CNF.NClause := [(496,true),(505,true),(509,true),(513,false),(517,true),(525,true)]
theorem inp_10358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10358 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 26) (closed_mem 12 26) cl_10358 (by decide) v hb
def cl_10359 : CNF.NClause := [(496,true),(505,true),(509,false),(513,true),(517,true),(525,true)]
theorem inp_10359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10359 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 26) (closed_mem 12 26) cl_10359 (by decide) v hb
def cl_10360 : CNF.NClause := [(496,true),(505,false),(509,true),(513,true),(517,true),(525,true)]
theorem inp_10360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10360 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 26) (closed_mem 12 26) cl_10360 (by decide) v hb
def cl_10362 : CNF.NClause := [(496,true),(503,true),(510,true),(512,true),(519,true),(523,false)]
theorem inp_10362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10362 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 27) (closed_mem 12 27) cl_10362 (by decide) v hb
def cl_10363 : CNF.NClause := [(496,true),(503,true),(510,true),(512,true),(519,false),(523,true)]
theorem inp_10363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10363 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 27) (closed_mem 12 27) cl_10363 (by decide) v hb
def cl_10364 : CNF.NClause := [(496,true),(503,true),(510,true),(512,false),(519,true),(523,true)]
theorem inp_10364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10364 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 27) (closed_mem 12 27) cl_10364 (by decide) v hb
def cl_10365 : CNF.NClause := [(496,true),(503,true),(510,false),(512,true),(519,true),(523,true)]
theorem inp_10365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10365 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 27) (closed_mem 12 27) cl_10365 (by decide) v hb
def cl_10366 : CNF.NClause := [(496,true),(503,false),(510,true),(512,true),(519,true),(523,true)]
theorem inp_10366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10366 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 27) (closed_mem 12 27) cl_10366 (by decide) v hb
def cl_10368 : CNF.NClause := [(496,true),(504,true),(507,true),(515,true),(518,true),(524,false)]
theorem inp_10368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10368 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 28) (closed_mem 12 28) cl_10368 (by decide) v hb
def cl_10369 : CNF.NClause := [(496,true),(504,true),(507,true),(515,true),(518,false),(524,true)]
theorem inp_10369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10369 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 28) (closed_mem 12 28) cl_10369 (by decide) v hb
def cl_10370 : CNF.NClause := [(496,true),(504,true),(507,true),(515,false),(518,true),(524,true)]
theorem inp_10370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10370 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 28) (closed_mem 12 28) cl_10370 (by decide) v hb
def cl_10371 : CNF.NClause := [(496,true),(504,true),(507,false),(515,true),(518,true),(524,true)]
theorem inp_10371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10371 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 28) (closed_mem 12 28) cl_10371 (by decide) v hb
def cl_10372 : CNF.NClause := [(496,true),(504,false),(507,true),(515,true),(518,true),(524,true)]
theorem inp_10372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10372 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 28) (closed_mem 12 28) cl_10372 (by decide) v hb
def cl_10377 : CNF.NClause := [(496,true),(502,true),(508,false),(514,true),(520,true),(522,true)]
theorem inp_10377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10377 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 29) (closed_mem 12 29) cl_10377 (by decide) v hb
def cl_10381 : CNF.NClause := [(496,true),(501,true),(506,true),(511,true),(516,false),(521,true)]
theorem inp_10381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10381 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 30) (closed_mem 12 30) cl_10381 (by decide) v hb
def cl_10382 : CNF.NClause := [(496,true),(501,true),(506,true),(511,false),(516,true),(521,true)]
theorem inp_10382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10382 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 30) (closed_mem 12 30) cl_10382 (by decide) v hb
def cl_10383 : CNF.NClause := [(496,true),(501,true),(506,false),(511,true),(516,true),(521,true)]
theorem inp_10383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10383 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 30) (closed_mem 12 30) cl_10383 (by decide) v hb
def cl_10384 : CNF.NClause := [(496,true),(501,false),(506,true),(511,true),(516,true),(521,true)]
theorem inp_10384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10384 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 30) (closed_mem 12 30) cl_10384 (by decide) v hb
def cl_10387 : CNF.NClause := [(552,true),(553,true),(554,true),(555,true),(556,false),(557,true)]
theorem inp_10387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10387 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 0) (closed_mem 13 0) cl_10387 (by decide) v hb
def cl_10389 : CNF.NClause := [(552,true),(553,true),(554,false),(555,true),(556,true),(557,true)]
theorem inp_10389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10389 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 0) (closed_mem 13 0) cl_10389 (by decide) v hb
def cl_10390 : CNF.NClause := [(552,true),(553,false),(554,true),(555,true),(556,true),(557,true)]
theorem inp_10390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10390 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 0) (closed_mem 13 0) cl_10390 (by decide) v hb
def cl_10393 : CNF.NClause := [(531,true),(536,true),(541,true),(546,true),(551,false),(552,true)]
theorem inp_10393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10393 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 1) (closed_mem 13 1) cl_10393 (by decide) v hb
def cl_10394 : CNF.NClause := [(531,true),(536,true),(541,true),(546,false),(551,true),(552,true)]
theorem inp_10394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10394 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 1) (closed_mem 13 1) cl_10394 (by decide) v hb
def cl_10395 : CNF.NClause := [(531,true),(536,true),(541,false),(546,true),(551,true),(552,true)]
theorem inp_10395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10395 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 1) (closed_mem 13 1) cl_10395 (by decide) v hb
def cl_10396 : CNF.NClause := [(531,true),(536,false),(541,true),(546,true),(551,true),(552,true)]
theorem inp_10396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10396 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 1) (closed_mem 13 1) cl_10396 (by decide) v hb
def cl_10397 : CNF.NClause := [(531,false),(536,true),(541,true),(546,true),(551,true),(552,true)]
theorem inp_10397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10397 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 1) (closed_mem 13 1) cl_10397 (by decide) v hb
def cl_10399 : CNF.NClause := [(529,true),(534,true),(539,true),(544,true),(549,false),(552,true)]
theorem inp_10399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10399 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 2) (closed_mem 13 2) cl_10399 (by decide) v hb
def cl_10400 : CNF.NClause := [(529,true),(534,true),(539,true),(544,false),(549,true),(552,true)]
theorem inp_10400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10400 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 2) (closed_mem 13 2) cl_10400 (by decide) v hb
def cl_10402 : CNF.NClause := [(529,true),(534,false),(539,true),(544,true),(549,true),(552,true)]
theorem inp_10402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10402 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 2) (closed_mem 13 2) cl_10402 (by decide) v hb
def cl_10403 : CNF.NClause := [(529,false),(534,true),(539,true),(544,true),(549,true),(552,true)]
theorem inp_10403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10403 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 2) (closed_mem 13 2) cl_10403 (by decide) v hb
def cl_10407 : CNF.NClause := [(530,true),(535,true),(540,false),(545,true),(550,true),(552,true)]
theorem inp_10407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10407 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 3) (closed_mem 13 3) cl_10407 (by decide) v hb
def cl_10411 : CNF.NClause := [(528,true),(533,true),(538,true),(543,true),(548,false),(552,true)]
theorem inp_10411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10411 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 4) (closed_mem 13 4) cl_10411 (by decide) v hb
end Percolation.NReplay
