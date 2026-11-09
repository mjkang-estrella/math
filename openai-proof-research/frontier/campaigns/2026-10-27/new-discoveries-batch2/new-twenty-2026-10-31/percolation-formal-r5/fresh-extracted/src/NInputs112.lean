import NInputs111
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_6385 : CNF.NClause := [(49,false),(18,false),(65,false),(69,false),(73,false),(77,true),(86,true),(91,true)]
theorem inp_6385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6385 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6385 (by decide) v hb
def cl_6386 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,false),(77,true),(86,true),(91,true)]
theorem inp_6386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6386 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6386 (by decide) v hb
def cl_6387 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(73,false),(77,true),(86,true),(91,true)]
theorem inp_6387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6387 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6387 (by decide) v hb
def cl_6388 : CNF.NClause := [(49,false),(18,true),(65,true),(69,false),(73,false),(77,true),(86,true),(91,true)]
theorem inp_6388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6388 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6388 (by decide) v hb
def cl_6389 : CNF.NClause := [(49,false),(18,false),(65,false),(69,true),(73,false),(77,true),(86,true),(91,true)]
theorem inp_6389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6389 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6389 (by decide) v hb
def cl_6390 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,false),(77,true),(86,true),(91,true)]
theorem inp_6390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6390 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6390 (by decide) v hb
def cl_6391 : CNF.NClause := [(49,false),(18,false),(65,true),(69,true),(73,false),(77,true),(86,true),(91,true)]
theorem inp_6391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6391 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6391 (by decide) v hb
def cl_6392 : CNF.NClause := [(49,false),(18,true),(65,true),(69,true),(73,false),(77,true),(86,true),(91,true)]
theorem inp_6392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6392 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6392 (by decide) v hb
def cl_6394 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,true),(77,true),(86,true),(91,true)]
theorem inp_6394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6394 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6394 (by decide) v hb
def cl_6396 : CNF.NClause := [(49,false),(18,true),(65,true),(69,false),(73,true),(77,true),(86,true),(91,true)]
theorem inp_6396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6396 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6396 (by decide) v hb
def cl_6397 : CNF.NClause := [(49,false),(18,false),(65,false),(69,true),(73,true),(77,true),(86,true),(91,true)]
theorem inp_6397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6397 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6397 (by decide) v hb
def cl_6398 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,true),(77,true),(86,true),(91,true)]
theorem inp_6398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6398 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6398 (by decide) v hb
def cl_6399 : CNF.NClause := [(49,false),(18,false),(65,true),(69,true),(73,true),(77,true),(86,true),(91,true)]
theorem inp_6399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6399 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6399 (by decide) v hb
def cl_6400 : CNF.NClause := [(49,false),(18,true),(65,true),(69,true),(73,true),(77,true),(86,true),(91,true)]
theorem inp_6400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6400 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6400 (by decide) v hb
def cl_6401 : CNF.NClause := [(50,true),(19,false),(63,false),(71,false),(74,false),(77,false),(85,false),(90,false)]
theorem inp_6401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6401 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6401 (by decide) v hb
def cl_6402 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,false),(77,false),(85,false),(90,false)]
theorem inp_6402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6402 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6402 (by decide) v hb
def cl_6403 : CNF.NClause := [(50,false),(19,false),(63,true),(71,false),(74,false),(77,false),(85,false),(90,false)]
theorem inp_6403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6403 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6403 (by decide) v hb
def cl_6404 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,false),(77,false),(85,false),(90,false)]
theorem inp_6404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6404 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6404 (by decide) v hb
def cl_6405 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(74,false),(77,false),(85,false),(90,false)]
theorem inp_6405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6405 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6405 (by decide) v hb
def cl_6406 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,false),(77,false),(85,false),(90,false)]
theorem inp_6406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6406 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6406 (by decide) v hb
def cl_6407 : CNF.NClause := [(50,false),(19,false),(63,true),(71,true),(74,false),(77,false),(85,false),(90,false)]
theorem inp_6407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6407 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6407 (by decide) v hb
def cl_6408 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,false),(77,false),(85,false),(90,false)]
theorem inp_6408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6408 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6408 (by decide) v hb
def cl_6409 : CNF.NClause := [(50,false),(19,false),(63,false),(71,false),(74,true),(77,false),(85,false),(90,false)]
theorem inp_6409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6409 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6409 (by decide) v hb
def cl_6410 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,true),(77,false),(85,false),(90,false)]
theorem inp_6410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6410 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6410 (by decide) v hb
def cl_6411 : CNF.NClause := [(50,false),(19,false),(63,true),(71,false),(74,true),(77,false),(85,false),(90,false)]
theorem inp_6411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6411 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6411 (by decide) v hb
def cl_6412 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,true),(77,false),(85,false),(90,false)]
theorem inp_6412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6412 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6412 (by decide) v hb
def cl_6413 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(74,true),(77,false),(85,false),(90,false)]
theorem inp_6413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6413 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6413 (by decide) v hb
def cl_6414 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,true),(77,false),(85,false),(90,false)]
theorem inp_6414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6414 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6414 (by decide) v hb
def cl_6415 : CNF.NClause := [(50,false),(19,false),(63,true),(71,true),(74,true),(77,false),(85,false),(90,false)]
theorem inp_6415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6415 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6415 (by decide) v hb
def cl_6416 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,true),(77,false),(85,false),(90,false)]
theorem inp_6416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6416 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6416 (by decide) v hb
def cl_6417 : CNF.NClause := [(50,false),(19,false),(63,false),(71,false),(74,false),(77,true),(85,false),(90,false)]
theorem inp_6417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6417 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6417 (by decide) v hb
def cl_6418 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,false),(77,true),(85,false),(90,false)]
theorem inp_6418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6418 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6418 (by decide) v hb
def cl_6419 : CNF.NClause := [(50,false),(19,false),(63,true),(71,false),(74,false),(77,true),(85,false),(90,false)]
theorem inp_6419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6419 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6419 (by decide) v hb
def cl_6420 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,false),(77,true),(85,false),(90,false)]
theorem inp_6420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6420 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6420 (by decide) v hb
def cl_6421 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(74,false),(77,true),(85,false),(90,false)]
theorem inp_6421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6421 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6421 (by decide) v hb
def cl_6422 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,false),(77,true),(85,false),(90,false)]
theorem inp_6422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6422 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6422 (by decide) v hb
def cl_6423 : CNF.NClause := [(50,false),(19,false),(63,true),(71,true),(74,false),(77,true),(85,false),(90,false)]
theorem inp_6423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6423 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6423 (by decide) v hb
def cl_6424 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,false),(77,true),(85,false),(90,false)]
theorem inp_6424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6424 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6424 (by decide) v hb
def cl_6425 : CNF.NClause := [(50,false),(19,false),(63,false),(71,false),(74,true),(77,true),(85,false),(90,false)]
theorem inp_6425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6425 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6425 (by decide) v hb
def cl_6426 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,true),(77,true),(85,false),(90,false)]
theorem inp_6426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6426 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6426 (by decide) v hb
def cl_6427 : CNF.NClause := [(50,false),(19,false),(63,true),(71,false),(74,true),(77,true),(85,false),(90,false)]
theorem inp_6427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6427 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6427 (by decide) v hb
def cl_6428 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,true),(77,true),(85,false),(90,false)]
theorem inp_6428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6428 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6428 (by decide) v hb
def cl_6429 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(74,true),(77,true),(85,false),(90,false)]
theorem inp_6429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6429 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6429 (by decide) v hb
def cl_6430 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,true),(77,true),(85,false),(90,false)]
theorem inp_6430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6430 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6430 (by decide) v hb
def cl_6431 : CNF.NClause := [(50,false),(19,false),(63,true),(71,true),(74,true),(77,true),(85,false),(90,false)]
theorem inp_6431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6431 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6431 (by decide) v hb
def cl_6432 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,true),(77,true),(85,false),(90,false)]
theorem inp_6432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6432 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6432 (by decide) v hb
def cl_6433 : CNF.NClause := [(50,false),(19,false),(63,false),(71,false),(74,false),(77,false),(85,true),(90,false)]
theorem inp_6433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6433 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6433 (by decide) v hb
def cl_6434 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,false),(77,false),(85,true),(90,false)]
theorem inp_6434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6434 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6434 v hb
def cl_6435 : CNF.NClause := [(50,false),(19,false),(63,true),(71,false),(74,false),(77,false),(85,true),(90,false)]
theorem inp_6435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6435 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6435 (by decide) v hb
def cl_6436 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,false),(77,false),(85,true),(90,false)]
theorem inp_6436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6436 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6436 v hb
end Percolation.NReplay
