import NInputs126
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_7170 : CNF.NClause := [(56,false),(25,true),(62,false),(63,false),(64,false),(65,false),(66,false),(92,false)]
theorem inp_7170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7170 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7170 v hb
def cl_7172 : CNF.NClause := [(56,false),(25,true),(62,true),(63,false),(64,false),(65,false),(66,false),(92,false)]
theorem inp_7172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7172 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7172 (by decide) v hb
def cl_7174 : CNF.NClause := [(56,false),(25,true),(62,false),(63,true),(64,false),(65,false),(66,false),(92,false)]
theorem inp_7174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7174 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7174 v hb
def cl_7176 : CNF.NClause := [(56,false),(25,true),(62,true),(63,true),(64,false),(65,false),(66,false),(92,false)]
theorem inp_7176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7176 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7176 (by decide) v hb
def cl_7178 : CNF.NClause := [(56,false),(25,true),(62,false),(63,false),(64,true),(65,false),(66,false),(92,false)]
theorem inp_7178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7178 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7178 (by decide) v hb
def cl_7180 : CNF.NClause := [(56,false),(25,true),(62,true),(63,false),(64,true),(65,false),(66,false),(92,false)]
theorem inp_7180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7180 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7180 (by decide) v hb
def cl_7182 : CNF.NClause := [(56,false),(25,true),(62,false),(63,true),(64,true),(65,false),(66,false),(92,false)]
theorem inp_7182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7182 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7182 (by decide) v hb
def cl_7184 : CNF.NClause := [(56,false),(25,true),(62,true),(63,true),(64,true),(65,false),(66,false),(92,false)]
theorem inp_7184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7184 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7184 (by decide) v hb
def cl_7186 : CNF.NClause := [(56,false),(25,true),(62,false),(63,false),(64,false),(65,true),(66,false),(92,false)]
theorem inp_7186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7186 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7186 (by decide) v hb
def cl_7188 : CNF.NClause := [(56,false),(25,true),(62,true),(63,false),(64,false),(65,true),(66,false),(92,false)]
theorem inp_7188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7188 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7188 (by decide) v hb
def cl_7190 : CNF.NClause := [(56,false),(25,true),(62,false),(63,true),(64,false),(65,true),(66,false),(92,false)]
theorem inp_7190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7190 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7190 (by decide) v hb
def cl_7192 : CNF.NClause := [(56,false),(25,true),(62,true),(63,true),(64,false),(65,true),(66,false),(92,false)]
theorem inp_7192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7192 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7192 (by decide) v hb
def cl_7194 : CNF.NClause := [(56,false),(25,true),(62,false),(63,false),(64,true),(65,true),(66,false),(92,false)]
theorem inp_7194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7194 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7194 (by decide) v hb
def cl_7196 : CNF.NClause := [(56,false),(25,true),(62,true),(63,false),(64,true),(65,true),(66,false),(92,false)]
theorem inp_7196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7196 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7196 (by decide) v hb
def cl_7198 : CNF.NClause := [(56,false),(25,true),(62,false),(63,true),(64,true),(65,true),(66,false),(92,false)]
theorem inp_7198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7198 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7198 (by decide) v hb
def cl_7200 : CNF.NClause := [(56,false),(25,true),(62,true),(63,true),(64,true),(65,true),(66,false),(92,false)]
theorem inp_7200 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7200 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7200 (by decide) v hb
def cl_7202 : CNF.NClause := [(56,false),(25,true),(62,false),(63,false),(64,false),(65,false),(66,true),(92,false)]
theorem inp_7202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7202 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7202 (by decide) v hb
def cl_7204 : CNF.NClause := [(56,false),(25,true),(62,true),(63,false),(64,false),(65,false),(66,true),(92,false)]
theorem inp_7204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7204 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7204 (by decide) v hb
def cl_7206 : CNF.NClause := [(56,false),(25,true),(62,false),(63,true),(64,false),(65,false),(66,true),(92,false)]
theorem inp_7206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7206 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7206 (by decide) v hb
def cl_7208 : CNF.NClause := [(56,false),(25,true),(62,true),(63,true),(64,false),(65,false),(66,true),(92,false)]
theorem inp_7208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7208 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7208 (by decide) v hb
def cl_7210 : CNF.NClause := [(56,false),(25,true),(62,false),(63,false),(64,true),(65,false),(66,true),(92,false)]
theorem inp_7210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7210 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7210 (by decide) v hb
def cl_7212 : CNF.NClause := [(56,false),(25,true),(62,true),(63,false),(64,true),(65,false),(66,true),(92,false)]
theorem inp_7212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7212 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7212 (by decide) v hb
def cl_7214 : CNF.NClause := [(56,false),(25,true),(62,false),(63,true),(64,true),(65,false),(66,true),(92,false)]
theorem inp_7214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7214 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7214 (by decide) v hb
def cl_7216 : CNF.NClause := [(56,false),(25,true),(62,true),(63,true),(64,true),(65,false),(66,true),(92,false)]
theorem inp_7216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7216 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7216 (by decide) v hb
def cl_7218 : CNF.NClause := [(56,false),(25,true),(62,false),(63,false),(64,false),(65,true),(66,true),(92,false)]
theorem inp_7218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7218 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7218 (by decide) v hb
def cl_7220 : CNF.NClause := [(56,false),(25,true),(62,true),(63,false),(64,false),(65,true),(66,true),(92,false)]
theorem inp_7220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7220 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7220 (by decide) v hb
def cl_7222 : CNF.NClause := [(56,false),(25,true),(62,false),(63,true),(64,false),(65,true),(66,true),(92,false)]
theorem inp_7222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7222 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7222 (by decide) v hb
def cl_7224 : CNF.NClause := [(56,false),(25,true),(62,true),(63,true),(64,false),(65,true),(66,true),(92,false)]
theorem inp_7224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7224 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7224 (by decide) v hb
def cl_7226 : CNF.NClause := [(56,false),(25,true),(62,false),(63,false),(64,true),(65,true),(66,true),(92,false)]
theorem inp_7226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7226 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7226 (by decide) v hb
def cl_7228 : CNF.NClause := [(56,false),(25,true),(62,true),(63,false),(64,true),(65,true),(66,true),(92,false)]
theorem inp_7228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7228 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7228 (by decide) v hb
def cl_7230 : CNF.NClause := [(56,false),(25,true),(62,false),(63,true),(64,true),(65,true),(66,true),(92,false)]
theorem inp_7230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7230 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7230 (by decide) v hb
def cl_7232 : CNF.NClause := [(56,false),(25,true),(62,true),(63,true),(64,true),(65,true),(66,true),(92,false)]
theorem inp_7232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7232 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7232 (by decide) v hb
def cl_7234 : CNF.NClause := [(56,false),(25,true),(62,false),(63,false),(64,false),(65,false),(66,false),(92,true)]
theorem inp_7234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7234 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7234 (by decide) v hb
def cl_7236 : CNF.NClause := [(56,false),(25,true),(62,true),(63,false),(64,false),(65,false),(66,false),(92,true)]
theorem inp_7236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7236 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7236 (by decide) v hb
def cl_7238 : CNF.NClause := [(56,false),(25,true),(62,false),(63,true),(64,false),(65,false),(66,false),(92,true)]
theorem inp_7238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7238 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7238 (by decide) v hb
def cl_7240 : CNF.NClause := [(56,false),(25,true),(62,true),(63,true),(64,false),(65,false),(66,false),(92,true)]
theorem inp_7240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7240 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7240 (by decide) v hb
def cl_7242 : CNF.NClause := [(56,false),(25,true),(62,false),(63,false),(64,true),(65,false),(66,false),(92,true)]
theorem inp_7242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7242 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7242 (by decide) v hb
def cl_7244 : CNF.NClause := [(56,false),(25,true),(62,true),(63,false),(64,true),(65,false),(66,false),(92,true)]
theorem inp_7244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7244 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7244 (by decide) v hb
def cl_7246 : CNF.NClause := [(56,false),(25,true),(62,false),(63,true),(64,true),(65,false),(66,false),(92,true)]
theorem inp_7246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7246 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7246 (by decide) v hb
def cl_7248 : CNF.NClause := [(56,false),(25,true),(62,true),(63,true),(64,true),(65,false),(66,false),(92,true)]
theorem inp_7248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7248 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7248 (by decide) v hb
def cl_7250 : CNF.NClause := [(56,false),(25,true),(62,false),(63,false),(64,false),(65,true),(66,false),(92,true)]
theorem inp_7250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7250 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7250 (by decide) v hb
def cl_7252 : CNF.NClause := [(56,false),(25,true),(62,true),(63,false),(64,false),(65,true),(66,false),(92,true)]
theorem inp_7252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7252 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7252 (by decide) v hb
def cl_7254 : CNF.NClause := [(56,false),(25,true),(62,false),(63,true),(64,false),(65,true),(66,false),(92,true)]
theorem inp_7254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7254 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7254 (by decide) v hb
def cl_7256 : CNF.NClause := [(56,false),(25,true),(62,true),(63,true),(64,false),(65,true),(66,false),(92,true)]
theorem inp_7256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7256 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7256 (by decide) v hb
def cl_7258 : CNF.NClause := [(56,false),(25,true),(62,false),(63,false),(64,true),(65,true),(66,false),(92,true)]
theorem inp_7258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7258 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7258 (by decide) v hb
def cl_7260 : CNF.NClause := [(56,false),(25,true),(62,true),(63,false),(64,true),(65,true),(66,false),(92,true)]
theorem inp_7260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7260 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7260 (by decide) v hb
def cl_7262 : CNF.NClause := [(56,false),(25,true),(62,false),(63,true),(64,true),(65,true),(66,false),(92,true)]
theorem inp_7262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7262 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7262 (by decide) v hb
def cl_7264 : CNF.NClause := [(56,false),(25,true),(62,true),(63,true),(64,true),(65,true),(66,false),(92,true)]
theorem inp_7264 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7264 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7264 (by decide) v hb
def cl_7266 : CNF.NClause := [(56,false),(25,true),(62,false),(63,false),(64,false),(65,false),(66,true),(92,true)]
theorem inp_7266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7266 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7266 (by decide) v hb
def cl_7268 : CNF.NClause := [(56,false),(25,true),(62,true),(63,false),(64,false),(65,false),(66,true),(92,true)]
theorem inp_7268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7268 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7268 (by decide) v hb
end Percolation.NReplay
