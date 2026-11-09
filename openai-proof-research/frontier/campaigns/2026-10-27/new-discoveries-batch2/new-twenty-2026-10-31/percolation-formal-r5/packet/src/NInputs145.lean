import NInputs144
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_8395 : CNF.NClause := [(187,true),(193,true),(199,true),(205,true),(206,false),(212,true)]
theorem inp_8395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8395 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 9) (closed_mem 2 9) cl_8395 (by decide) v hb
def cl_8397 : CNF.NClause := [(187,true),(193,true),(199,false),(205,true),(206,true),(212,true)]
theorem inp_8397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8397 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 9) (closed_mem 2 9) cl_8397 (by decide) v hb
def cl_8398 : CNF.NClause := [(187,true),(193,false),(199,true),(205,true),(206,true),(212,true)]
theorem inp_8398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8398 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 9) (closed_mem 2 9) cl_8398 (by decide) v hb
def cl_8401 : CNF.NClause := [(196,true),(197,true),(198,true),(199,true),(200,false),(216,true)]
theorem inp_8401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8401 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 10) (closed_mem 2 10) cl_8401 (by decide) v hb
def cl_8402 : CNF.NClause := [(196,true),(197,true),(198,true),(199,false),(200,true),(216,true)]
theorem inp_8402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8402 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 10) (closed_mem 2 10) cl_8402 (by decide) v hb
def cl_8403 : CNF.NClause := [(196,true),(197,true),(198,false),(199,true),(200,true),(216,true)]
theorem inp_8403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8403 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 10) (closed_mem 2 10) cl_8403 (by decide) v hb
def cl_8404 : CNF.NClause := [(196,true),(197,false),(198,true),(199,true),(200,true),(216,true)]
theorem inp_8404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8404 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 10) (closed_mem 2 10) cl_8404 (by decide) v hb
def cl_8405 : CNF.NClause := [(196,false),(197,true),(198,true),(199,true),(200,true),(216,true)]
theorem inp_8405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8405 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 10) (closed_mem 2 10) cl_8405 (by decide) v hb
def cl_8406 : CNF.NClause := [(190,true),(193,true),(196,true),(204,true),(207,true),(214,false)]
theorem inp_8406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8406 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 11) (closed_mem 2 11) cl_8406 (by decide) v hb
def cl_8407 : CNF.NClause := [(190,true),(193,true),(196,true),(204,true),(207,false),(214,true)]
theorem inp_8407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8407 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 11) (closed_mem 2 11) cl_8407 (by decide) v hb
def cl_8408 : CNF.NClause := [(190,true),(193,true),(196,true),(204,false),(207,true),(214,true)]
theorem inp_8408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8408 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 11) (closed_mem 2 11) cl_8408 (by decide) v hb
def cl_8411 : CNF.NClause := [(190,false),(193,true),(196,true),(204,true),(207,true),(214,true)]
theorem inp_8411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8411 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 11) (closed_mem 2 11) cl_8411 (by decide) v hb
def cl_8417 : CNF.NClause := [(188,false),(192,true),(196,true),(205,true),(209,true),(215,true)]
theorem inp_8417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8417 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 12) (closed_mem 2 12) cl_8417 (by decide) v hb
def cl_8420 : CNF.NClause := [(189,true),(195,true),(196,true),(202,false),(208,true),(212,true)]
theorem inp_8420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8420 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 13) (closed_mem 2 13) cl_8420 (by decide) v hb
def cl_8423 : CNF.NClause := [(189,false),(195,true),(196,true),(202,true),(208,true),(212,true)]
theorem inp_8423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8423 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 13) (closed_mem 2 13) cl_8423 (by decide) v hb
def cl_8424 : CNF.NClause := [(187,true),(194,true),(196,true),(203,true),(210,true),(213,false)]
theorem inp_8424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8424 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 14) (closed_mem 2 14) cl_8424 (by decide) v hb
def cl_8426 : CNF.NClause := [(187,true),(194,true),(196,true),(203,false),(210,true),(213,true)]
theorem inp_8426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8426 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 14) (closed_mem 2 14) cl_8426 (by decide) v hb
def cl_8427 : CNF.NClause := [(187,true),(194,true),(196,false),(203,true),(210,true),(213,true)]
theorem inp_8427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8427 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 14) (closed_mem 2 14) cl_8427 (by decide) v hb
def cl_8428 : CNF.NClause := [(187,true),(194,false),(196,true),(203,true),(210,true),(213,true)]
theorem inp_8428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8428 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 14) (closed_mem 2 14) cl_8428 (by decide) v hb
def cl_8431 : CNF.NClause := [(201,true),(202,true),(203,true),(204,true),(205,false),(216,true)]
theorem inp_8431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8431 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 15) (closed_mem 2 15) cl_8431 (by decide) v hb
def cl_8433 : CNF.NClause := [(201,true),(202,true),(203,false),(204,true),(205,true),(216,true)]
theorem inp_8433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8433 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 15) (closed_mem 2 15) cl_8433 (by decide) v hb
def cl_8435 : CNF.NClause := [(201,false),(202,true),(203,true),(204,true),(205,true),(216,true)]
theorem inp_8435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8435 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 15) (closed_mem 2 15) cl_8435 (by decide) v hb
def cl_8438 : CNF.NClause := [(190,true),(192,true),(199,true),(201,false),(208,true),(213,true)]
theorem inp_8438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8438 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 16) (closed_mem 2 16) cl_8438 (by decide) v hb
def cl_8439 : CNF.NClause := [(190,true),(192,true),(199,false),(201,true),(208,true),(213,true)]
theorem inp_8439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8439 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 16) (closed_mem 2 16) cl_8439 (by decide) v hb
def cl_8447 : CNF.NClause := [(188,false),(194,true),(200,true),(201,true),(207,true),(212,true)]
theorem inp_8447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8447 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 17) (closed_mem 2 17) cl_8447 (by decide) v hb
def cl_8448 : CNF.NClause := [(189,true),(193,true),(197,true),(201,true),(210,true),(215,false)]
theorem inp_8448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8448 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 18) (closed_mem 2 18) cl_8448 (by decide) v hb
def cl_8453 : CNF.NClause := [(189,false),(193,true),(197,true),(201,true),(210,true),(215,true)]
theorem inp_8453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8453 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 18) (closed_mem 2 18) cl_8453 (by decide) v hb
def cl_8454 : CNF.NClause := [(187,true),(195,true),(198,true),(201,true),(209,true),(214,false)]
theorem inp_8454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8454 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 19) (closed_mem 2 19) cl_8454 (by decide) v hb
def cl_8455 : CNF.NClause := [(187,true),(195,true),(198,true),(201,true),(209,false),(214,true)]
theorem inp_8455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8455 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 19) (closed_mem 2 19) cl_8455 (by decide) v hb
def cl_8459 : CNF.NClause := [(187,false),(195,true),(198,true),(201,true),(209,true),(214,true)]
theorem inp_8459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8459 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 19) (closed_mem 2 19) cl_8459 (by decide) v hb
def cl_8461 : CNF.NClause := [(191,true),(192,true),(193,true),(194,true),(195,false),(216,true)]
theorem inp_8461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8461 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 20) (closed_mem 2 20) cl_8461 (by decide) v hb
def cl_8462 : CNF.NClause := [(191,true),(192,true),(193,true),(194,false),(195,true),(216,true)]
theorem inp_8462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8462 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 20) (closed_mem 2 20) cl_8462 (by decide) v hb
def cl_8463 : CNF.NClause := [(191,true),(192,true),(193,false),(194,true),(195,true),(216,true)]
theorem inp_8463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8463 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 20) (closed_mem 2 20) cl_8463 (by decide) v hb
def cl_8465 : CNF.NClause := [(191,false),(192,true),(193,true),(194,true),(195,true),(216,true)]
theorem inp_8465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8465 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 20) (closed_mem 2 20) cl_8465 (by decide) v hb
def cl_8467 : CNF.NClause := [(190,true),(191,true),(197,true),(203,true),(209,false),(212,true)]
theorem inp_8467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8467 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 21) (closed_mem 2 21) cl_8467 (by decide) v hb
def cl_8477 : CNF.NClause := [(188,false),(191,true),(199,true),(202,true),(210,true),(214,true)]
theorem inp_8477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8477 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 22) (closed_mem 2 22) cl_8477 (by decide) v hb
def cl_8479 : CNF.NClause := [(189,true),(191,true),(198,true),(205,true),(207,false),(213,true)]
theorem inp_8479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8479 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 23) (closed_mem 2 23) cl_8479 (by decide) v hb
def cl_8480 : CNF.NClause := [(189,true),(191,true),(198,true),(205,false),(207,true),(213,true)]
theorem inp_8480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8480 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 23) (closed_mem 2 23) cl_8480 (by decide) v hb
def cl_8483 : CNF.NClause := [(189,false),(191,true),(198,true),(205,true),(207,true),(213,true)]
theorem inp_8483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8483 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 23) (closed_mem 2 23) cl_8483 (by decide) v hb
def cl_8484 : CNF.NClause := [(187,true),(191,true),(200,true),(204,true),(208,true),(215,false)]
theorem inp_8484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8484 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 24) (closed_mem 2 24) cl_8484 (by decide) v hb
def cl_8485 : CNF.NClause := [(187,true),(191,true),(200,true),(204,true),(208,false),(215,true)]
theorem inp_8485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8485 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 24) (closed_mem 2 24) cl_8485 (by decide) v hb
def cl_8493 : CNF.NClause := [(186,true),(187,true),(188,false),(189,true),(190,true),(216,true)]
theorem inp_8493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8493 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 25) (closed_mem 2 25) cl_8493 (by decide) v hb
def cl_8496 : CNF.NClause := [(186,true),(195,true),(199,true),(203,true),(207,true),(215,false)]
theorem inp_8496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8496 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 26) (closed_mem 2 26) cl_8496 (by decide) v hb
def cl_8497 : CNF.NClause := [(186,true),(195,true),(199,true),(203,true),(207,false),(215,true)]
theorem inp_8497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8497 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 26) (closed_mem 2 26) cl_8497 (by decide) v hb
def cl_8498 : CNF.NClause := [(186,true),(195,true),(199,true),(203,false),(207,true),(215,true)]
theorem inp_8498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8498 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 26) (closed_mem 2 26) cl_8498 (by decide) v hb
def cl_8499 : CNF.NClause := [(186,true),(195,true),(199,false),(203,true),(207,true),(215,true)]
theorem inp_8499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8499 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 26) (closed_mem 2 26) cl_8499 (by decide) v hb
def cl_8502 : CNF.NClause := [(186,true),(193,true),(200,true),(202,true),(209,true),(213,false)]
theorem inp_8502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8502 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 27) (closed_mem 2 27) cl_8502 (by decide) v hb
def cl_8503 : CNF.NClause := [(186,true),(193,true),(200,true),(202,true),(209,false),(213,true)]
theorem inp_8503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8503 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 27) (closed_mem 2 27) cl_8503 (by decide) v hb
def cl_8504 : CNF.NClause := [(186,true),(193,true),(200,true),(202,false),(209,true),(213,true)]
theorem inp_8504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8504 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 27) (closed_mem 2 27) cl_8504 (by decide) v hb
def cl_8506 : CNF.NClause := [(186,true),(193,false),(200,true),(202,true),(209,true),(213,true)]
theorem inp_8506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8506 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 27) (closed_mem 2 27) cl_8506 (by decide) v hb
end Percolation.NReplay
