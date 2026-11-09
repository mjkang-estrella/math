import NInputs179
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_11415 : CNF.NClause := [(686,true),(688,true),(695,false),(697,true),(704,true),(709,true)]
theorem inp_11415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11415 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 16) (closed_mem 18 16) cl_11415 (by decide) v hb
def cl_11416 : CNF.NClause := [(686,true),(688,false),(695,true),(697,true),(704,true),(709,true)]
theorem inp_11416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11416 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 16) (closed_mem 18 16) cl_11416 (by decide) v hb
def cl_11417 : CNF.NClause := [(686,false),(688,true),(695,true),(697,true),(704,true),(709,true)]
theorem inp_11417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11417 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 16) (closed_mem 18 16) cl_11417 (by decide) v hb
def cl_11418 : CNF.NClause := [(684,true),(690,true),(696,true),(697,true),(703,true),(708,false)]
theorem inp_11418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11418 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 17) (closed_mem 18 17) cl_11418 (by decide) v hb
def cl_11419 : CNF.NClause := [(684,true),(690,true),(696,true),(697,true),(703,false),(708,true)]
theorem inp_11419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11419 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 17) (closed_mem 18 17) cl_11419 (by decide) v hb
def cl_11422 : CNF.NClause := [(684,true),(690,false),(696,true),(697,true),(703,true),(708,true)]
theorem inp_11422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11422 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 17) (closed_mem 18 17) cl_11422 (by decide) v hb
def cl_11424 : CNF.NClause := [(685,true),(689,true),(693,true),(697,true),(706,true),(711,false)]
theorem inp_11424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11424 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 18) (closed_mem 18 18) cl_11424 (by decide) v hb
def cl_11425 : CNF.NClause := [(685,true),(689,true),(693,true),(697,true),(706,false),(711,true)]
theorem inp_11425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11425 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 18) (closed_mem 18 18) cl_11425 (by decide) v hb
def cl_11427 : CNF.NClause := [(685,true),(689,true),(693,false),(697,true),(706,true),(711,true)]
theorem inp_11427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11427 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 18) (closed_mem 18 18) cl_11427 (by decide) v hb
def cl_11428 : CNF.NClause := [(685,true),(689,false),(693,true),(697,true),(706,true),(711,true)]
theorem inp_11428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11428 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 18) (closed_mem 18 18) cl_11428 (by decide) v hb
def cl_11429 : CNF.NClause := [(685,false),(689,true),(693,true),(697,true),(706,true),(711,true)]
theorem inp_11429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11429 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 18) (closed_mem 18 18) cl_11429 (by decide) v hb
def cl_11430 : CNF.NClause := [(683,true),(691,true),(694,true),(697,true),(705,true),(710,false)]
theorem inp_11430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11430 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 19) (closed_mem 18 19) cl_11430 (by decide) v hb
def cl_11431 : CNF.NClause := [(683,true),(691,true),(694,true),(697,true),(705,false),(710,true)]
theorem inp_11431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11431 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 19) (closed_mem 18 19) cl_11431 (by decide) v hb
def cl_11432 : CNF.NClause := [(683,true),(691,true),(694,true),(697,false),(705,true),(710,true)]
theorem inp_11432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11432 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 19) (closed_mem 18 19) cl_11432 (by decide) v hb
def cl_11433 : CNF.NClause := [(683,true),(691,true),(694,false),(697,true),(705,true),(710,true)]
theorem inp_11433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11433 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 19) (closed_mem 18 19) cl_11433 (by decide) v hb
def cl_11435 : CNF.NClause := [(683,false),(691,true),(694,true),(697,true),(705,true),(710,true)]
theorem inp_11435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11435 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 19) (closed_mem 18 19) cl_11435 (by decide) v hb
def cl_11437 : CNF.NClause := [(687,true),(688,true),(689,true),(690,true),(691,false),(712,true)]
theorem inp_11437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11437 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 20) (closed_mem 18 20) cl_11437 (by decide) v hb
def cl_11438 : CNF.NClause := [(687,true),(688,true),(689,true),(690,false),(691,true),(712,true)]
theorem inp_11438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11438 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 20) (closed_mem 18 20) cl_11438 (by decide) v hb
def cl_11439 : CNF.NClause := [(687,true),(688,true),(689,false),(690,true),(691,true),(712,true)]
theorem inp_11439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11439 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 20) (closed_mem 18 20) cl_11439 (by decide) v hb
def cl_11440 : CNF.NClause := [(687,true),(688,false),(689,true),(690,true),(691,true),(712,true)]
theorem inp_11440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11440 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 20) (closed_mem 18 20) cl_11440 (by decide) v hb
def cl_11441 : CNF.NClause := [(687,false),(688,true),(689,true),(690,true),(691,true),(712,true)]
theorem inp_11441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11441 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 20) (closed_mem 18 20) cl_11441 (by decide) v hb
def cl_11442 : CNF.NClause := [(686,true),(687,true),(693,true),(699,true),(705,true),(708,false)]
theorem inp_11442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11442 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 21) (closed_mem 18 21) cl_11442 (by decide) v hb
def cl_11443 : CNF.NClause := [(686,true),(687,true),(693,true),(699,true),(705,false),(708,true)]
theorem inp_11443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11443 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 21) (closed_mem 18 21) cl_11443 (by decide) v hb
def cl_11446 : CNF.NClause := [(686,true),(687,false),(693,true),(699,true),(705,true),(708,true)]
theorem inp_11446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11446 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 21) (closed_mem 18 21) cl_11446 (by decide) v hb
def cl_11448 : CNF.NClause := [(684,true),(687,true),(695,true),(698,true),(706,true),(710,false)]
theorem inp_11448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11448 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 22) (closed_mem 18 22) cl_11448 (by decide) v hb
def cl_11449 : CNF.NClause := [(684,true),(687,true),(695,true),(698,true),(706,false),(710,true)]
theorem inp_11449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11449 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 22) (closed_mem 18 22) cl_11449 (by decide) v hb
def cl_11451 : CNF.NClause := [(684,true),(687,true),(695,false),(698,true),(706,true),(710,true)]
theorem inp_11451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11451 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 22) (closed_mem 18 22) cl_11451 (by decide) v hb
def cl_11452 : CNF.NClause := [(684,true),(687,false),(695,true),(698,true),(706,true),(710,true)]
theorem inp_11452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11452 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 22) (closed_mem 18 22) cl_11452 (by decide) v hb
def cl_11454 : CNF.NClause := [(685,true),(687,true),(694,true),(701,true),(703,true),(709,false)]
theorem inp_11454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11454 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 23) (closed_mem 18 23) cl_11454 (by decide) v hb
def cl_11455 : CNF.NClause := [(685,true),(687,true),(694,true),(701,true),(703,false),(709,true)]
theorem inp_11455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11455 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 23) (closed_mem 18 23) cl_11455 (by decide) v hb
def cl_11457 : CNF.NClause := [(685,true),(687,true),(694,false),(701,true),(703,true),(709,true)]
theorem inp_11457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11457 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 23) (closed_mem 18 23) cl_11457 (by decide) v hb
def cl_11458 : CNF.NClause := [(685,true),(687,false),(694,true),(701,true),(703,true),(709,true)]
theorem inp_11458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11458 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 23) (closed_mem 18 23) cl_11458 (by decide) v hb
def cl_11459 : CNF.NClause := [(685,false),(687,true),(694,true),(701,true),(703,true),(709,true)]
theorem inp_11459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11459 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 23) (closed_mem 18 23) cl_11459 (by decide) v hb
def cl_11462 : CNF.NClause := [(683,true),(687,true),(696,true),(700,false),(704,true),(711,true)]
theorem inp_11462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11462 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 24) (closed_mem 18 24) cl_11462 (by decide) v hb
def cl_11467 : CNF.NClause := [(682,true),(683,true),(684,true),(685,true),(686,false),(712,true)]
theorem inp_11467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11467 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 25) (closed_mem 18 25) cl_11467 (by decide) v hb
def cl_11468 : CNF.NClause := [(682,true),(683,true),(684,true),(685,false),(686,true),(712,true)]
theorem inp_11468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11468 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 25) (closed_mem 18 25) cl_11468 (by decide) v hb
def cl_11469 : CNF.NClause := [(682,true),(683,true),(684,false),(685,true),(686,true),(712,true)]
theorem inp_11469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11469 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 25) (closed_mem 18 25) cl_11469 (by decide) v hb
def cl_11470 : CNF.NClause := [(682,true),(683,false),(684,true),(685,true),(686,true),(712,true)]
theorem inp_11470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11470 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 25) (closed_mem 18 25) cl_11470 (by decide) v hb
def cl_11472 : CNF.NClause := [(682,true),(691,true),(695,true),(699,true),(703,true),(711,false)]
theorem inp_11472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11472 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 26) (closed_mem 18 26) cl_11472 (by decide) v hb
def cl_11473 : CNF.NClause := [(682,true),(691,true),(695,true),(699,true),(703,false),(711,true)]
theorem inp_11473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11473 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 26) (closed_mem 18 26) cl_11473 (by decide) v hb
def cl_11474 : CNF.NClause := [(682,true),(691,true),(695,true),(699,false),(703,true),(711,true)]
theorem inp_11474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11474 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 26) (closed_mem 18 26) cl_11474 (by decide) v hb
def cl_11475 : CNF.NClause := [(682,true),(691,true),(695,false),(699,true),(703,true),(711,true)]
theorem inp_11475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11475 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 26) (closed_mem 18 26) cl_11475 (by decide) v hb
def cl_11476 : CNF.NClause := [(682,true),(691,false),(695,true),(699,true),(703,true),(711,true)]
theorem inp_11476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11476 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_11476 v hb
def cl_11478 : CNF.NClause := [(682,true),(689,true),(696,true),(698,true),(705,true),(709,false)]
theorem inp_11478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11478 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 27) (closed_mem 18 27) cl_11478 (by decide) v hb
def cl_11479 : CNF.NClause := [(682,true),(689,true),(696,true),(698,true),(705,false),(709,true)]
theorem inp_11479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11479 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 27) (closed_mem 18 27) cl_11479 (by decide) v hb
def cl_11480 : CNF.NClause := [(682,true),(689,true),(696,true),(698,false),(705,true),(709,true)]
theorem inp_11480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11480 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 27) (closed_mem 18 27) cl_11480 (by decide) v hb
def cl_11481 : CNF.NClause := [(682,true),(689,true),(696,false),(698,true),(705,true),(709,true)]
theorem inp_11481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11481 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 27) (closed_mem 18 27) cl_11481 (by decide) v hb
def cl_11482 : CNF.NClause := [(682,true),(689,false),(696,true),(698,true),(705,true),(709,true)]
theorem inp_11482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11482 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 27) (closed_mem 18 27) cl_11482 (by decide) v hb
def cl_11484 : CNF.NClause := [(682,true),(690,true),(693,true),(701,true),(704,true),(710,false)]
theorem inp_11484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11484 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 28) (closed_mem 18 28) cl_11484 (by decide) v hb
def cl_11485 : CNF.NClause := [(682,true),(690,true),(693,true),(701,true),(704,false),(710,true)]
theorem inp_11485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11485 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 18 28) (closed_mem 18 28) cl_11485 (by decide) v hb
end Percolation.NReplay
