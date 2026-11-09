import NInputs069
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_4226 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,false),(79,false),(84,false),(87,false)]
theorem inp_4226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4226 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4226 v hb
def cl_4227 : CNF.NClause := [(33,false),(2,false),(64,true),(69,false),(74,false),(79,false),(84,false),(87,false)]
theorem inp_4227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4227 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4227 (by decide) v hb
def cl_4228 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(74,false),(79,false),(84,false),(87,false)]
theorem inp_4228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4228 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4228 (by decide) v hb
def cl_4229 : CNF.NClause := [(33,false),(2,false),(64,false),(69,true),(74,false),(79,false),(84,false),(87,false)]
theorem inp_4229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4229 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4229 (by decide) v hb
def cl_4230 : CNF.NClause := [(33,false),(2,true),(64,false),(69,true),(74,false),(79,false),(84,false),(87,false)]
theorem inp_4230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4230 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4230 (by decide) v hb
def cl_4231 : CNF.NClause := [(33,false),(2,false),(64,true),(69,true),(74,false),(79,false),(84,false),(87,false)]
theorem inp_4231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4231 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4231 (by decide) v hb
def cl_4232 : CNF.NClause := [(33,false),(2,true),(64,true),(69,true),(74,false),(79,false),(84,false),(87,false)]
theorem inp_4232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4232 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4232 (by decide) v hb
def cl_4233 : CNF.NClause := [(33,false),(2,false),(64,false),(69,false),(74,true),(79,false),(84,false),(87,false)]
theorem inp_4233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4233 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4233 (by decide) v hb
def cl_4234 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,true),(79,false),(84,false),(87,false)]
theorem inp_4234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4234 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4234 (by decide) v hb
def cl_4235 : CNF.NClause := [(33,false),(2,false),(64,true),(69,false),(74,true),(79,false),(84,false),(87,false)]
theorem inp_4235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4235 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4235 (by decide) v hb
def cl_4236 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(74,true),(79,false),(84,false),(87,false)]
theorem inp_4236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4236 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4236 (by decide) v hb
def cl_4237 : CNF.NClause := [(33,false),(2,false),(64,false),(69,true),(74,true),(79,false),(84,false),(87,false)]
theorem inp_4237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4237 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4237 (by decide) v hb
def cl_4238 : CNF.NClause := [(33,false),(2,true),(64,false),(69,true),(74,true),(79,false),(84,false),(87,false)]
theorem inp_4238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4238 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4238 (by decide) v hb
def cl_4239 : CNF.NClause := [(33,false),(2,false),(64,true),(69,true),(74,true),(79,false),(84,false),(87,false)]
theorem inp_4239 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4239 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4239 (by decide) v hb
def cl_4240 : CNF.NClause := [(33,false),(2,true),(64,true),(69,true),(74,true),(79,false),(84,false),(87,false)]
theorem inp_4240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4240 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4240 (by decide) v hb
def cl_4241 : CNF.NClause := [(33,false),(2,false),(64,false),(69,false),(74,false),(79,true),(84,false),(87,false)]
theorem inp_4241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4241 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4241 v hb
def cl_4242 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,false),(79,true),(84,false),(87,false)]
theorem inp_4242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4242 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4242 (by decide) v hb
def cl_4243 : CNF.NClause := [(33,false),(2,false),(64,true),(69,false),(74,false),(79,true),(84,false),(87,false)]
theorem inp_4243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4243 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4243 v hb
def cl_4244 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(74,false),(79,true),(84,false),(87,false)]
theorem inp_4244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4244 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4244 (by decide) v hb
def cl_4245 : CNF.NClause := [(33,false),(2,false),(64,false),(69,true),(74,false),(79,true),(84,false),(87,false)]
theorem inp_4245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4245 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4245 (by decide) v hb
def cl_4246 : CNF.NClause := [(33,false),(2,true),(64,false),(69,true),(74,false),(79,true),(84,false),(87,false)]
theorem inp_4246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4246 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4246 (by decide) v hb
def cl_4247 : CNF.NClause := [(33,false),(2,false),(64,true),(69,true),(74,false),(79,true),(84,false),(87,false)]
theorem inp_4247 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4247 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4247 (by decide) v hb
def cl_4248 : CNF.NClause := [(33,false),(2,true),(64,true),(69,true),(74,false),(79,true),(84,false),(87,false)]
theorem inp_4248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4248 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4248 (by decide) v hb
def cl_4249 : CNF.NClause := [(33,false),(2,false),(64,false),(69,false),(74,true),(79,true),(84,false),(87,false)]
theorem inp_4249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4249 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4249 (by decide) v hb
def cl_4250 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,true),(79,true),(84,false),(87,false)]
theorem inp_4250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4250 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4250 (by decide) v hb
def cl_4251 : CNF.NClause := [(33,false),(2,false),(64,true),(69,false),(74,true),(79,true),(84,false),(87,false)]
theorem inp_4251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4251 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4251 (by decide) v hb
def cl_4252 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(74,true),(79,true),(84,false),(87,false)]
theorem inp_4252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4252 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4252 (by decide) v hb
def cl_4253 : CNF.NClause := [(33,false),(2,false),(64,false),(69,true),(74,true),(79,true),(84,false),(87,false)]
theorem inp_4253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4253 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4253 (by decide) v hb
def cl_4254 : CNF.NClause := [(33,false),(2,true),(64,false),(69,true),(74,true),(79,true),(84,false),(87,false)]
theorem inp_4254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4254 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4254 (by decide) v hb
def cl_4256 : CNF.NClause := [(33,false),(2,true),(64,true),(69,true),(74,true),(79,true),(84,false),(87,false)]
theorem inp_4256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4256 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4256 (by decide) v hb
def cl_4257 : CNF.NClause := [(33,false),(2,false),(64,false),(69,false),(74,false),(79,false),(84,true),(87,false)]
theorem inp_4257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4257 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4257 v hb
def cl_4258 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,false),(79,false),(84,true),(87,false)]
theorem inp_4258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4258 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4258 v hb
def cl_4259 : CNF.NClause := [(33,false),(2,false),(64,true),(69,false),(74,false),(79,false),(84,true),(87,false)]
theorem inp_4259 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4259 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4259 (by decide) v hb
def cl_4260 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(74,false),(79,false),(84,true),(87,false)]
theorem inp_4260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4260 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4260 (by decide) v hb
def cl_4261 : CNF.NClause := [(33,false),(2,false),(64,false),(69,true),(74,false),(79,false),(84,true),(87,false)]
theorem inp_4261 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4261 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4261 (by decide) v hb
def cl_4262 : CNF.NClause := [(33,false),(2,true),(64,false),(69,true),(74,false),(79,false),(84,true),(87,false)]
theorem inp_4262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4262 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4262 (by decide) v hb
def cl_4263 : CNF.NClause := [(33,false),(2,false),(64,true),(69,true),(74,false),(79,false),(84,true),(87,false)]
theorem inp_4263 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4263 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4263 (by decide) v hb
def cl_4264 : CNF.NClause := [(33,false),(2,true),(64,true),(69,true),(74,false),(79,false),(84,true),(87,false)]
theorem inp_4264 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4264 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4264 (by decide) v hb
def cl_4265 : CNF.NClause := [(33,false),(2,false),(64,false),(69,false),(74,true),(79,false),(84,true),(87,false)]
theorem inp_4265 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4265 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4265 (by decide) v hb
def cl_4266 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,true),(79,false),(84,true),(87,false)]
theorem inp_4266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4266 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4266 (by decide) v hb
def cl_4267 : CNF.NClause := [(33,false),(2,false),(64,true),(69,false),(74,true),(79,false),(84,true),(87,false)]
theorem inp_4267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4267 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4267 (by decide) v hb
def cl_4268 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(74,true),(79,false),(84,true),(87,false)]
theorem inp_4268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4268 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4268 (by decide) v hb
def cl_4269 : CNF.NClause := [(33,false),(2,false),(64,false),(69,true),(74,true),(79,false),(84,true),(87,false)]
theorem inp_4269 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4269 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4269 (by decide) v hb
def cl_4270 : CNF.NClause := [(33,false),(2,true),(64,false),(69,true),(74,true),(79,false),(84,true),(87,false)]
theorem inp_4270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4270 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4270 (by decide) v hb
def cl_4271 : CNF.NClause := [(33,false),(2,false),(64,true),(69,true),(74,true),(79,false),(84,true),(87,false)]
theorem inp_4271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4271 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4271 (by decide) v hb
def cl_4272 : CNF.NClause := [(33,false),(2,true),(64,true),(69,true),(74,true),(79,false),(84,true),(87,false)]
theorem inp_4272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4272 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4272 (by decide) v hb
def cl_4273 : CNF.NClause := [(33,false),(2,false),(64,false),(69,false),(74,false),(79,true),(84,true),(87,false)]
theorem inp_4273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4273 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4273 (by decide) v hb
def cl_4274 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,false),(79,true),(84,true),(87,false)]
theorem inp_4274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4274 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4274 (by decide) v hb
def cl_4275 : CNF.NClause := [(33,false),(2,false),(64,true),(69,false),(74,false),(79,true),(84,true),(87,false)]
theorem inp_4275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4275 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4275 (by decide) v hb
def cl_4276 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(74,false),(79,true),(84,true),(87,false)]
theorem inp_4276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4276 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4276 (by decide) v hb
end Percolation.NReplay
