import NInputs143
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_8283 : CNF.NClause := [(159,true),(160,true),(166,false),(172,true),(178,true),(181,true)]
theorem inp_8283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8283 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 21) (closed_mem 1 21) cl_8283 (by decide) v hb
def cl_8286 : CNF.NClause := [(157,true),(160,true),(168,true),(171,true),(179,true),(183,false)]
theorem inp_8286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8286 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 22) (closed_mem 1 22) cl_8286 (by decide) v hb
def cl_8290 : CNF.NClause := [(157,true),(160,false),(168,true),(171,true),(179,true),(183,true)]
theorem inp_8290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8290 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 22) (closed_mem 1 22) cl_8290 (by decide) v hb
def cl_8291 : CNF.NClause := [(157,false),(160,true),(168,true),(171,true),(179,true),(183,true)]
theorem inp_8291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8291 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 22) (closed_mem 1 22) cl_8291 (by decide) v hb
def cl_8296 : CNF.NClause := [(158,true),(160,false),(167,true),(174,true),(176,true),(182,true)]
theorem inp_8296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8296 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 23) (closed_mem 1 23) cl_8296 (by decide) v hb
def cl_8303 : CNF.NClause := [(156,false),(160,true),(169,true),(173,true),(177,true),(184,true)]
theorem inp_8303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8303 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 24) (closed_mem 1 24) cl_8303 (by decide) v hb
def cl_8308 : CNF.NClause := [(155,true),(156,false),(157,true),(158,true),(159,true),(185,true)]
theorem inp_8308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8308 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 25) (closed_mem 1 25) cl_8308 (by decide) v hb
def cl_8310 : CNF.NClause := [(155,true),(164,true),(168,true),(172,true),(176,true),(184,false)]
theorem inp_8310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8310 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 26) (closed_mem 1 26) cl_8310 (by decide) v hb
def cl_8311 : CNF.NClause := [(155,true),(164,true),(168,true),(172,true),(176,false),(184,true)]
theorem inp_8311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8311 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 26) (closed_mem 1 26) cl_8311 (by decide) v hb
def cl_8313 : CNF.NClause := [(155,true),(164,true),(168,false),(172,true),(176,true),(184,true)]
theorem inp_8313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8313 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 26) (closed_mem 1 26) cl_8313 (by decide) v hb
def cl_8314 : CNF.NClause := [(155,true),(164,false),(168,true),(172,true),(176,true),(184,true)]
theorem inp_8314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8314 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 26) (closed_mem 1 26) cl_8314 (by decide) v hb
def cl_8316 : CNF.NClause := [(155,true),(162,true),(169,true),(171,true),(178,true),(182,false)]
theorem inp_8316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8316 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 27) (closed_mem 1 27) cl_8316 (by decide) v hb
def cl_8317 : CNF.NClause := [(155,true),(162,true),(169,true),(171,true),(178,false),(182,true)]
theorem inp_8317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8317 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 27) (closed_mem 1 27) cl_8317 (by decide) v hb
def cl_8319 : CNF.NClause := [(155,true),(162,true),(169,false),(171,true),(178,true),(182,true)]
theorem inp_8319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8319 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 27) (closed_mem 1 27) cl_8319 (by decide) v hb
def cl_8320 : CNF.NClause := [(155,true),(162,false),(169,true),(171,true),(178,true),(182,true)]
theorem inp_8320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8320 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 27) (closed_mem 1 27) cl_8320 (by decide) v hb
def cl_8322 : CNF.NClause := [(155,true),(163,true),(166,true),(174,true),(177,true),(183,false)]
theorem inp_8322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8322 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 28) (closed_mem 1 28) cl_8322 (by decide) v hb
def cl_8323 : CNF.NClause := [(155,true),(163,true),(166,true),(174,true),(177,false),(183,true)]
theorem inp_8323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8323 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 28) (closed_mem 1 28) cl_8323 (by decide) v hb
def cl_8325 : CNF.NClause := [(155,true),(163,true),(166,false),(174,true),(177,true),(183,true)]
theorem inp_8325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8325 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 28) (closed_mem 1 28) cl_8325 (by decide) v hb
def cl_8326 : CNF.NClause := [(155,true),(163,false),(166,true),(174,true),(177,true),(183,true)]
theorem inp_8326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8326 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 28) (closed_mem 1 28) cl_8326 (by decide) v hb
def cl_8328 : CNF.NClause := [(155,true),(161,true),(167,true),(173,true),(179,true),(181,false)]
theorem inp_8328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8328 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 29) (closed_mem 1 29) cl_8328 (by decide) v hb
def cl_8329 : CNF.NClause := [(155,true),(161,true),(167,true),(173,true),(179,false),(181,true)]
theorem inp_8329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8329 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 29) (closed_mem 1 29) cl_8329 (by decide) v hb
def cl_8330 : CNF.NClause := [(155,true),(161,true),(167,true),(173,false),(179,true),(181,true)]
theorem inp_8330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8330 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 29) (closed_mem 1 29) cl_8330 (by decide) v hb
def cl_8331 : CNF.NClause := [(155,true),(161,true),(167,false),(173,true),(179,true),(181,true)]
theorem inp_8331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8331 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 29) (closed_mem 1 29) cl_8331 (by decide) v hb
def cl_8332 : CNF.NClause := [(155,true),(161,false),(167,true),(173,true),(179,true),(181,true)]
theorem inp_8332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8332 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 29) (closed_mem 1 29) cl_8332 (by decide) v hb
def cl_8335 : CNF.NClause := [(155,true),(160,true),(165,true),(170,true),(175,false),(180,true)]
theorem inp_8335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8335 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 30) (closed_mem 1 30) cl_8335 (by decide) v hb
def cl_8336 : CNF.NClause := [(155,true),(160,true),(165,true),(170,false),(175,true),(180,true)]
theorem inp_8336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8336 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 30) (closed_mem 1 30) cl_8336 (by decide) v hb
def cl_8337 : CNF.NClause := [(155,true),(160,true),(165,false),(170,true),(175,true),(180,true)]
theorem inp_8337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8337 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 30) (closed_mem 1 30) cl_8337 (by decide) v hb
def cl_8341 : CNF.NClause := [(211,true),(212,true),(213,true),(214,true),(215,false),(216,true)]
theorem inp_8341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8341 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 0) (closed_mem 2 0) cl_8341 (by decide) v hb
def cl_8342 : CNF.NClause := [(211,true),(212,true),(213,true),(214,false),(215,true),(216,true)]
theorem inp_8342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8342 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 0) (closed_mem 2 0) cl_8342 (by decide) v hb
def cl_8343 : CNF.NClause := [(211,true),(212,true),(213,false),(214,true),(215,true),(216,true)]
theorem inp_8343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8343 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 0) (closed_mem 2 0) cl_8343 (by decide) v hb
def cl_8347 : CNF.NClause := [(190,true),(195,true),(200,true),(205,true),(210,false),(211,true)]
theorem inp_8347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8347 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 1) (closed_mem 2 1) cl_8347 (by decide) v hb
def cl_8349 : CNF.NClause := [(190,true),(195,true),(200,false),(205,true),(210,true),(211,true)]
theorem inp_8349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8349 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 1) (closed_mem 2 1) cl_8349 (by decide) v hb
def cl_8351 : CNF.NClause := [(190,false),(195,true),(200,true),(205,true),(210,true),(211,true)]
theorem inp_8351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8351 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 1) (closed_mem 2 1) cl_8351 (by decide) v hb
def cl_8357 : CNF.NClause := [(188,false),(193,true),(198,true),(203,true),(208,true),(211,true)]
theorem inp_8357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8357 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 2) (closed_mem 2 2) cl_8357 (by decide) v hb
def cl_8359 : CNF.NClause := [(189,true),(194,true),(199,true),(204,true),(209,false),(211,true)]
theorem inp_8359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8359 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 3) (closed_mem 2 3) cl_8359 (by decide) v hb
def cl_8363 : CNF.NClause := [(189,false),(194,true),(199,true),(204,true),(209,true),(211,true)]
theorem inp_8363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8363 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 3) (closed_mem 2 3) cl_8363 (by decide) v hb
def cl_8365 : CNF.NClause := [(187,true),(192,true),(197,true),(202,true),(207,false),(211,true)]
theorem inp_8365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8365 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 4) (closed_mem 2 4) cl_8365 (by decide) v hb
def cl_8366 : CNF.NClause := [(187,true),(192,true),(197,true),(202,false),(207,true),(211,true)]
theorem inp_8366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8366 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 4) (closed_mem 2 4) cl_8366 (by decide) v hb
def cl_8368 : CNF.NClause := [(187,true),(192,false),(197,true),(202,true),(207,true),(211,true)]
theorem inp_8368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8368 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 4) (closed_mem 2 4) cl_8368 (by decide) v hb
def cl_8369 : CNF.NClause := [(187,false),(192,true),(197,true),(202,true),(207,true),(211,true)]
theorem inp_8369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8369 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 4) (closed_mem 2 4) cl_8369 (by decide) v hb
def cl_8371 : CNF.NClause := [(206,true),(207,true),(208,true),(209,true),(210,false),(216,true)]
theorem inp_8371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8371 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 5) (closed_mem 2 5) cl_8371 (by decide) v hb
def cl_8373 : CNF.NClause := [(206,true),(207,true),(208,false),(209,true),(210,true),(216,true)]
theorem inp_8373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8373 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 5) (closed_mem 2 5) cl_8373 (by decide) v hb
def cl_8374 : CNF.NClause := [(206,true),(207,false),(208,true),(209,true),(210,true),(216,true)]
theorem inp_8374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8374 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 5) (closed_mem 2 5) cl_8374 (by decide) v hb
def cl_8375 : CNF.NClause := [(206,false),(207,true),(208,true),(209,true),(210,true),(216,true)]
theorem inp_8375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8375 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 5) (closed_mem 2 5) cl_8375 (by decide) v hb
def cl_8378 : CNF.NClause := [(190,true),(194,true),(198,true),(202,false),(206,true),(215,true)]
theorem inp_8378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8378 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 6) (closed_mem 2 6) cl_8378 (by decide) v hb
def cl_8379 : CNF.NClause := [(190,true),(194,true),(198,false),(202,true),(206,true),(215,true)]
theorem inp_8379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8379 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 6) (closed_mem 2 6) cl_8379 (by decide) v hb
def cl_8380 : CNF.NClause := [(190,true),(194,false),(198,true),(202,true),(206,true),(215,true)]
theorem inp_8380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8380 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 6) (closed_mem 2 6) cl_8380 (by decide) v hb
def cl_8387 : CNF.NClause := [(188,false),(195,true),(197,true),(204,true),(206,true),(213,true)]
theorem inp_8387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8387 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 7) (closed_mem 2 7) cl_8387 (by decide) v hb
def cl_8388 : CNF.NClause := [(189,true),(192,true),(200,true),(203,true),(206,true),(214,false)]
theorem inp_8388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8388 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 8) (closed_mem 2 8) cl_8388 (by decide) v hb
def cl_8390 : CNF.NClause := [(189,true),(192,true),(200,true),(203,false),(206,true),(214,true)]
theorem inp_8390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8390 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 8) (closed_mem 2 8) cl_8390 (by decide) v hb
end Percolation.NReplay
