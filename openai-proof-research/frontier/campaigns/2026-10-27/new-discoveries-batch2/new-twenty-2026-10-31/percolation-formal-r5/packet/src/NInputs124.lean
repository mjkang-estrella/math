import NInputs123
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_7012 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,false),(81,false),(83,true),(89,true)]
theorem inp_7012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7012 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7012 v hb
def cl_7013 : CNF.NClause := [(54,false),(23,false),(65,false),(67,true),(74,false),(81,false),(83,true),(89,true)]
theorem inp_7013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7013 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7013 (by decide) v hb
def cl_7014 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(74,false),(81,false),(83,true),(89,true)]
theorem inp_7014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7014 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7014 (by decide) v hb
def cl_7015 : CNF.NClause := [(54,false),(23,false),(65,true),(67,true),(74,false),(81,false),(83,true),(89,true)]
theorem inp_7015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7015 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7015 (by decide) v hb
def cl_7016 : CNF.NClause := [(54,false),(23,true),(65,true),(67,true),(74,false),(81,false),(83,true),(89,true)]
theorem inp_7016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7016 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7016 (by decide) v hb
def cl_7017 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,true),(81,false),(83,true),(89,true)]
theorem inp_7017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7017 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7017 (by decide) v hb
def cl_7018 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,true),(81,false),(83,true),(89,true)]
theorem inp_7018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7018 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7018 (by decide) v hb
def cl_7019 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(74,true),(81,false),(83,true),(89,true)]
theorem inp_7019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7019 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7019 (by decide) v hb
def cl_7020 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,true),(81,false),(83,true),(89,true)]
theorem inp_7020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7020 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7020 (by decide) v hb
def cl_7021 : CNF.NClause := [(54,false),(23,false),(65,false),(67,true),(74,true),(81,false),(83,true),(89,true)]
theorem inp_7021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7021 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7021 (by decide) v hb
def cl_7022 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(74,true),(81,false),(83,true),(89,true)]
theorem inp_7022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7022 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7022 (by decide) v hb
def cl_7024 : CNF.NClause := [(54,false),(23,true),(65,true),(67,true),(74,true),(81,false),(83,true),(89,true)]
theorem inp_7024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7024 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7024 (by decide) v hb
def cl_7025 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,false),(81,true),(83,true),(89,true)]
theorem inp_7025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7025 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7025 (by decide) v hb
def cl_7026 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,false),(81,true),(83,true),(89,true)]
theorem inp_7026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7026 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7026 v hb
def cl_7027 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(74,false),(81,true),(83,true),(89,true)]
theorem inp_7027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7027 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7027 (by decide) v hb
def cl_7028 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,false),(81,true),(83,true),(89,true)]
theorem inp_7028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7028 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7028 v hb
def cl_7029 : CNF.NClause := [(54,false),(23,false),(65,false),(67,true),(74,false),(81,true),(83,true),(89,true)]
theorem inp_7029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7029 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7029 (by decide) v hb
def cl_7030 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(74,false),(81,true),(83,true),(89,true)]
theorem inp_7030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7030 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7030 (by decide) v hb
def cl_7031 : CNF.NClause := [(54,false),(23,false),(65,true),(67,true),(74,false),(81,true),(83,true),(89,true)]
theorem inp_7031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7031 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7031 (by decide) v hb
def cl_7032 : CNF.NClause := [(54,false),(23,true),(65,true),(67,true),(74,false),(81,true),(83,true),(89,true)]
theorem inp_7032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7032 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7032 (by decide) v hb
def cl_7033 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,true),(81,true),(83,true),(89,true)]
theorem inp_7033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7033 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7033 (by decide) v hb
def cl_7034 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,true),(81,true),(83,true),(89,true)]
theorem inp_7034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7034 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7034 (by decide) v hb
def cl_7036 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,true),(81,true),(83,true),(89,true)]
theorem inp_7036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7036 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7036 (by decide) v hb
def cl_7037 : CNF.NClause := [(54,false),(23,false),(65,false),(67,true),(74,true),(81,true),(83,true),(89,true)]
theorem inp_7037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7037 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7037 (by decide) v hb
def cl_7038 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(74,true),(81,true),(83,true),(89,true)]
theorem inp_7038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7038 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7038 (by decide) v hb
def cl_7040 : CNF.NClause := [(54,false),(23,true),(65,true),(67,true),(74,true),(81,true),(83,true),(89,true)]
theorem inp_7040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7040 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7040 (by decide) v hb
def cl_7041 : CNF.NClause := [(55,true),(24,false),(63,false),(67,false),(76,false),(80,false),(84,false),(91,false)]
theorem inp_7041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7041 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7041 v hb
def cl_7042 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(76,false),(80,false),(84,false),(91,false)]
theorem inp_7042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7042 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7042 (by decide) v hb
def cl_7043 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,false),(80,false),(84,false),(91,false)]
theorem inp_7043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7043 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7043 v hb
def cl_7044 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,false),(80,false),(84,false),(91,false)]
theorem inp_7044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7044 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7044 v hb
def cl_7045 : CNF.NClause := [(55,false),(24,false),(63,false),(67,true),(76,false),(80,false),(84,false),(91,false)]
theorem inp_7045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7045 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7045 (by decide) v hb
def cl_7046 : CNF.NClause := [(55,false),(24,true),(63,false),(67,true),(76,false),(80,false),(84,false),(91,false)]
theorem inp_7046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7046 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7046 (by decide) v hb
def cl_7047 : CNF.NClause := [(55,false),(24,false),(63,true),(67,true),(76,false),(80,false),(84,false),(91,false)]
theorem inp_7047 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7047 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7047 (by decide) v hb
def cl_7048 : CNF.NClause := [(55,false),(24,true),(63,true),(67,true),(76,false),(80,false),(84,false),(91,false)]
theorem inp_7048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7048 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7048 (by decide) v hb
def cl_7049 : CNF.NClause := [(55,false),(24,false),(63,false),(67,false),(76,true),(80,false),(84,false),(91,false)]
theorem inp_7049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7049 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7049 (by decide) v hb
def cl_7050 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(76,true),(80,false),(84,false),(91,false)]
theorem inp_7050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7050 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7050 v hb
def cl_7051 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,true),(80,false),(84,false),(91,false)]
theorem inp_7051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7051 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7051 (by decide) v hb
def cl_7052 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,true),(80,false),(84,false),(91,false)]
theorem inp_7052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7052 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7052 v hb
def cl_7053 : CNF.NClause := [(55,false),(24,false),(63,false),(67,true),(76,true),(80,false),(84,false),(91,false)]
theorem inp_7053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7053 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7053 (by decide) v hb
def cl_7054 : CNF.NClause := [(55,false),(24,true),(63,false),(67,true),(76,true),(80,false),(84,false),(91,false)]
theorem inp_7054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7054 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7054 (by decide) v hb
def cl_7055 : CNF.NClause := [(55,false),(24,false),(63,true),(67,true),(76,true),(80,false),(84,false),(91,false)]
theorem inp_7055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7055 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7055 (by decide) v hb
def cl_7056 : CNF.NClause := [(55,false),(24,true),(63,true),(67,true),(76,true),(80,false),(84,false),(91,false)]
theorem inp_7056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7056 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7056 (by decide) v hb
def cl_7057 : CNF.NClause := [(55,false),(24,false),(63,false),(67,false),(76,false),(80,true),(84,false),(91,false)]
theorem inp_7057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7057 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7057 (by decide) v hb
def cl_7058 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(76,false),(80,true),(84,false),(91,false)]
theorem inp_7058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7058 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7058 (by decide) v hb
def cl_7059 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,false),(80,true),(84,false),(91,false)]
theorem inp_7059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7059 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7059 (by decide) v hb
def cl_7060 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,false),(80,true),(84,false),(91,false)]
theorem inp_7060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7060 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7060 (by decide) v hb
def cl_7061 : CNF.NClause := [(55,false),(24,false),(63,false),(67,true),(76,false),(80,true),(84,false),(91,false)]
theorem inp_7061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7061 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7061 (by decide) v hb
def cl_7062 : CNF.NClause := [(55,false),(24,true),(63,false),(67,true),(76,false),(80,true),(84,false),(91,false)]
theorem inp_7062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7062 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7062 (by decide) v hb
def cl_7063 : CNF.NClause := [(55,false),(24,false),(63,true),(67,true),(76,false),(80,true),(84,false),(91,false)]
theorem inp_7063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7063 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7063 (by decide) v hb
def cl_7064 : CNF.NClause := [(55,false),(24,true),(63,true),(67,true),(76,false),(80,true),(84,false),(91,false)]
theorem inp_7064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7064 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7064 (by decide) v hb
end Percolation.NReplay
