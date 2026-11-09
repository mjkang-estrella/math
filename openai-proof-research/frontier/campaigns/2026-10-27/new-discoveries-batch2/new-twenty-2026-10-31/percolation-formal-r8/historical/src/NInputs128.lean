import NInputs127
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_7270 : CNF.NClause := [(56,false),(25,true),(62,false),(63,true),(64,false),(65,false),(66,true),(92,true)]
theorem inp_7270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7270 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7270 (by decide) v hb
def cl_7272 : CNF.NClause := [(56,false),(25,true),(62,true),(63,true),(64,false),(65,false),(66,true),(92,true)]
theorem inp_7272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7272 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7272 (by decide) v hb
def cl_7274 : CNF.NClause := [(56,false),(25,true),(62,false),(63,false),(64,true),(65,false),(66,true),(92,true)]
theorem inp_7274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7274 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7274 (by decide) v hb
def cl_7276 : CNF.NClause := [(56,false),(25,true),(62,true),(63,false),(64,true),(65,false),(66,true),(92,true)]
theorem inp_7276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7276 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7276 (by decide) v hb
def cl_7278 : CNF.NClause := [(56,false),(25,true),(62,false),(63,true),(64,true),(65,false),(66,true),(92,true)]
theorem inp_7278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7278 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7278 (by decide) v hb
def cl_7280 : CNF.NClause := [(56,false),(25,true),(62,true),(63,true),(64,true),(65,false),(66,true),(92,true)]
theorem inp_7280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7280 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7280 (by decide) v hb
def cl_7282 : CNF.NClause := [(56,false),(25,true),(62,false),(63,false),(64,false),(65,true),(66,true),(92,true)]
theorem inp_7282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7282 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7282 (by decide) v hb
def cl_7284 : CNF.NClause := [(56,false),(25,true),(62,true),(63,false),(64,false),(65,true),(66,true),(92,true)]
theorem inp_7284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7284 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7284 (by decide) v hb
def cl_7286 : CNF.NClause := [(56,false),(25,true),(62,false),(63,true),(64,false),(65,true),(66,true),(92,true)]
theorem inp_7286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7286 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7286 (by decide) v hb
def cl_7288 : CNF.NClause := [(56,false),(25,true),(62,true),(63,true),(64,false),(65,true),(66,true),(92,true)]
theorem inp_7288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7288 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7288 (by decide) v hb
def cl_7290 : CNF.NClause := [(56,false),(25,true),(62,false),(63,false),(64,true),(65,true),(66,true),(92,true)]
theorem inp_7290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7290 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7290 (by decide) v hb
def cl_7292 : CNF.NClause := [(56,false),(25,true),(62,true),(63,false),(64,true),(65,true),(66,true),(92,true)]
theorem inp_7292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7292 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7292 (by decide) v hb
def cl_7294 : CNF.NClause := [(56,false),(25,true),(62,false),(63,true),(64,true),(65,true),(66,true),(92,true)]
theorem inp_7294 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7294 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7294 (by decide) v hb
def cl_7296 : CNF.NClause := [(56,false),(25,true),(62,true),(63,true),(64,true),(65,true),(66,true),(92,true)]
theorem inp_7296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7296 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7296 (by decide) v hb
def cl_7297 : CNF.NClause := [(57,true),(26,false),(62,false),(71,false),(75,false),(79,false),(83,false),(91,false)]
theorem inp_7297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7297 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7297 (by decide) v hb
def cl_7298 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,false),(79,false),(83,false),(91,false)]
theorem inp_7298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7298 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7298 (by decide) v hb
def cl_7299 : CNF.NClause := [(57,false),(26,false),(62,true),(71,false),(75,false),(79,false),(83,false),(91,false)]
theorem inp_7299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7299 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7299 (by decide) v hb
def cl_7300 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,false),(79,false),(83,false),(91,false)]
theorem inp_7300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7300 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7300 (by decide) v hb
def cl_7301 : CNF.NClause := [(57,false),(26,false),(62,false),(71,true),(75,false),(79,false),(83,false),(91,false)]
theorem inp_7301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7301 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7301 (by decide) v hb
def cl_7302 : CNF.NClause := [(57,false),(26,true),(62,false),(71,true),(75,false),(79,false),(83,false),(91,false)]
theorem inp_7302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7302 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7302 (by decide) v hb
def cl_7303 : CNF.NClause := [(57,false),(26,false),(62,true),(71,true),(75,false),(79,false),(83,false),(91,false)]
theorem inp_7303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7303 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7303 (by decide) v hb
def cl_7304 : CNF.NClause := [(57,false),(26,true),(62,true),(71,true),(75,false),(79,false),(83,false),(91,false)]
theorem inp_7304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7304 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7304 (by decide) v hb
def cl_7305 : CNF.NClause := [(57,false),(26,false),(62,false),(71,false),(75,true),(79,false),(83,false),(91,false)]
theorem inp_7305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7305 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7305 (by decide) v hb
def cl_7306 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,true),(79,false),(83,false),(91,false)]
theorem inp_7306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7306 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7306 v hb
def cl_7307 : CNF.NClause := [(57,false),(26,false),(62,true),(71,false),(75,true),(79,false),(83,false),(91,false)]
theorem inp_7307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7307 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7307 (by decide) v hb
def cl_7308 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,true),(79,false),(83,false),(91,false)]
theorem inp_7308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7308 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7308 v hb
def cl_7309 : CNF.NClause := [(57,false),(26,false),(62,false),(71,true),(75,true),(79,false),(83,false),(91,false)]
theorem inp_7309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7309 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7309 (by decide) v hb
def cl_7310 : CNF.NClause := [(57,false),(26,true),(62,false),(71,true),(75,true),(79,false),(83,false),(91,false)]
theorem inp_7310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7310 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7310 (by decide) v hb
def cl_7311 : CNF.NClause := [(57,false),(26,false),(62,true),(71,true),(75,true),(79,false),(83,false),(91,false)]
theorem inp_7311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7311 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7311 (by decide) v hb
def cl_7312 : CNF.NClause := [(57,false),(26,true),(62,true),(71,true),(75,true),(79,false),(83,false),(91,false)]
theorem inp_7312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7312 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7312 (by decide) v hb
def cl_7313 : CNF.NClause := [(57,false),(26,false),(62,false),(71,false),(75,false),(79,true),(83,false),(91,false)]
theorem inp_7313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7313 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7313 (by decide) v hb
def cl_7314 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,false),(79,true),(83,false),(91,false)]
theorem inp_7314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7314 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7314 (by decide) v hb
def cl_7315 : CNF.NClause := [(57,false),(26,false),(62,true),(71,false),(75,false),(79,true),(83,false),(91,false)]
theorem inp_7315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7315 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7315 (by decide) v hb
def cl_7316 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,false),(79,true),(83,false),(91,false)]
theorem inp_7316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7316 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7316 (by decide) v hb
def cl_7317 : CNF.NClause := [(57,false),(26,false),(62,false),(71,true),(75,false),(79,true),(83,false),(91,false)]
theorem inp_7317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7317 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7317 (by decide) v hb
def cl_7318 : CNF.NClause := [(57,false),(26,true),(62,false),(71,true),(75,false),(79,true),(83,false),(91,false)]
theorem inp_7318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7318 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7318 (by decide) v hb
def cl_7319 : CNF.NClause := [(57,false),(26,false),(62,true),(71,true),(75,false),(79,true),(83,false),(91,false)]
theorem inp_7319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7319 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7319 (by decide) v hb
def cl_7320 : CNF.NClause := [(57,false),(26,true),(62,true),(71,true),(75,false),(79,true),(83,false),(91,false)]
theorem inp_7320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7320 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7320 (by decide) v hb
def cl_7321 : CNF.NClause := [(57,false),(26,false),(62,false),(71,false),(75,true),(79,true),(83,false),(91,false)]
theorem inp_7321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7321 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7321 (by decide) v hb
def cl_7322 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,true),(79,true),(83,false),(91,false)]
theorem inp_7322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7322 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7322 v hb
def cl_7323 : CNF.NClause := [(57,false),(26,false),(62,true),(71,false),(75,true),(79,true),(83,false),(91,false)]
theorem inp_7323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7323 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7323 (by decide) v hb
def cl_7324 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,true),(79,true),(83,false),(91,false)]
theorem inp_7324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7324 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7324 v hb
def cl_7325 : CNF.NClause := [(57,false),(26,false),(62,false),(71,true),(75,true),(79,true),(83,false),(91,false)]
theorem inp_7325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7325 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7325 (by decide) v hb
def cl_7326 : CNF.NClause := [(57,false),(26,true),(62,false),(71,true),(75,true),(79,true),(83,false),(91,false)]
theorem inp_7326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7326 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7326 (by decide) v hb
def cl_7328 : CNF.NClause := [(57,false),(26,true),(62,true),(71,true),(75,true),(79,true),(83,false),(91,false)]
theorem inp_7328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7328 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7328 (by decide) v hb
def cl_7329 : CNF.NClause := [(57,false),(26,false),(62,false),(71,false),(75,false),(79,false),(83,true),(91,false)]
theorem inp_7329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7329 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7329 (by decide) v hb
def cl_7330 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,false),(79,false),(83,true),(91,false)]
theorem inp_7330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7330 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7330 (by decide) v hb
def cl_7331 : CNF.NClause := [(57,false),(26,false),(62,true),(71,false),(75,false),(79,false),(83,true),(91,false)]
theorem inp_7331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7331 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7331 (by decide) v hb
def cl_7332 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,false),(79,false),(83,true),(91,false)]
theorem inp_7332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7332 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7332 (by decide) v hb
def cl_7333 : CNF.NClause := [(57,false),(26,false),(62,false),(71,true),(75,false),(79,false),(83,true),(91,false)]
theorem inp_7333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7333 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7333 (by decide) v hb
end Percolation.NReplay
