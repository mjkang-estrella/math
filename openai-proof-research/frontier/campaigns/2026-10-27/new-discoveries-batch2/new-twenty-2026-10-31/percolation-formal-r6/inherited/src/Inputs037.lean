import Inputs036
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_5953 : CNF.NClause := [(46,false),(15,false),(77,false),(78,false),(79,false),(80,false),(81,false),(92,true)]
theorem inp_5953 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5953 := by
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5953 (by decide) v h
def cl_5954 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,false),(80,false),(81,false),(92,true)]
theorem inp_5954 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5954 := by
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5954 (by decide) v h
def cl_5970 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,false),(80,true),(81,false),(92,true)]
theorem inp_5970 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5970 := by
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5970 (by decide) v h
def cl_5978 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,true),(80,true),(81,false),(92,true)]
theorem inp_5978 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5978 := by
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5978 (by decide) v h
def cl_6015 : CNF.NClause := [(46,false),(15,false),(77,true),(78,true),(79,true),(80,true),(81,true),(92,true)]
theorem inp_6015 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6015 := by
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_6015 (by decide) v h
def cl_6016 : CNF.NClause := [(46,false),(15,true),(77,true),(78,true),(79,true),(80,true),(81,true),(92,true)]
theorem inp_6016 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6016 := by
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_6016 (by decide) v h
def cl_6026 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,true),(77,false),(84,false),(89,false)]
theorem inp_6026 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6026 := by
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6026 (by decide) v h
def cl_6042 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,true),(77,true),(84,false),(89,false)]
theorem inp_6042 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6042 := by
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6042 (by decide) v h
def cl_6058 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,true),(77,false),(84,true),(89,false)]
theorem inp_6058 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6058 := by
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6058 (by decide) v h
def cl_6074 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,true),(77,true),(84,true),(89,false)]
theorem inp_6074 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6074 := by
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6074 (by decide) v h
def cl_6090 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,true),(77,false),(84,false),(89,true)]
theorem inp_6090 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6090 := by
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6090 (by decide) v h
def cl_6094 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true),(75,true),(77,false),(84,false),(89,true)]
theorem inp_6094 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6094 := by
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6094 (by decide) v h
def cl_6106 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,true),(77,true),(84,false),(89,true)]
theorem inp_6106 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6106 := by
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6106 (by decide) v h
def cl_6122 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,true),(77,false),(84,true),(89,true)]
theorem inp_6122 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6122 := by
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6122 (by decide) v h
def cl_6138 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,true),(77,true),(84,true),(89,true)]
theorem inp_6138 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6138 := by
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6138 (by decide) v h
def cl_6143 : CNF.NClause := [(47,false),(16,false),(66,true),(68,true),(75,true),(77,true),(84,true),(89,true)]
theorem inp_6143 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6143 := by
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6143 (by decide) v h
def cl_6144 : CNF.NClause := [(47,false),(16,true),(66,true),(68,true),(75,true),(77,true),(84,true),(89,true)]
theorem inp_6144 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6144 := by
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6144 (by decide) v h
def cl_6146 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,false),(77,false),(83,false),(88,false)]
theorem inp_6146 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6146 := by
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6146 (by decide) v h
def cl_6150 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,false),(77,false),(83,false),(88,false)]
theorem inp_6150 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6150 := by
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6150 (by decide) v h
def cl_6153 : CNF.NClause := [(48,false),(17,false),(64,false),(70,false),(76,true),(77,false),(83,false),(88,false)]
theorem inp_6153 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6153 := by
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6153 (by decide) v h
def cl_6154 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,true),(77,false),(83,false),(88,false)]
theorem inp_6154 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6154 := by
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6154 (by decide) v h
def cl_6178 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,false),(77,false),(83,true),(88,false)]
theorem inp_6178 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6178 := by
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6178 (by decide) v h
def cl_6186 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,true),(77,false),(83,true),(88,false)]
theorem inp_6186 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6186 := by
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6186 (by decide) v h
def cl_6210 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,false),(77,false),(83,false),(88,true)]
theorem inp_6210 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6210 := by
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6210 (by decide) v h
def cl_6214 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,false),(77,false),(83,false),(88,true)]
theorem inp_6214 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6214 := by
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6214 (by decide) v h
def cl_6274 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,false),(77,false),(86,false),(91,false)]
theorem inp_6274 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6274 := by
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6274 (by decide) v h
def cl_6277 : CNF.NClause := [(49,false),(18,false),(65,false),(69,true),(73,false),(77,false),(86,false),(91,false)]
theorem inp_6277 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6277 := by
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6277 (by decide) v h
def cl_6278 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,false),(77,false),(86,false),(91,false)]
theorem inp_6278 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6278 := by
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6278 (by decide) v h
def cl_6281 : CNF.NClause := [(49,false),(18,false),(65,false),(69,false),(73,true),(77,false),(86,false),(91,false)]
theorem inp_6281 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6281 := by
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6281 (by decide) v h
def cl_6283 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(73,true),(77,false),(86,false),(91,false)]
theorem inp_6283 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6283 := by
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6283 (by decide) v h
def cl_6285 : CNF.NClause := [(49,false),(18,false),(65,false),(69,true),(73,true),(77,false),(86,false),(91,false)]
theorem inp_6285 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6285 := by
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6285 (by decide) v h
def cl_6289 : CNF.NClause := [(49,false),(18,false),(65,false),(69,false),(73,false),(77,true),(86,false),(91,false)]
theorem inp_6289 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6289 := by
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6289 (by decide) v h
def cl_6290 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,false),(77,true),(86,false),(91,false)]
theorem inp_6290 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6290 := by
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6290 (by decide) v h
def cl_6291 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(73,false),(77,true),(86,false),(91,false)]
theorem inp_6291 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6291 := by
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6291 (by decide) v h
def cl_6293 : CNF.NClause := [(49,false),(18,false),(65,false),(69,true),(73,false),(77,true),(86,false),(91,false)]
theorem inp_6293 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6293 := by
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6293 (by decide) v h
def cl_6294 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,false),(77,true),(86,false),(91,false)]
theorem inp_6294 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6294 := by
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6294 (by decide) v h
def cl_6295 : CNF.NClause := [(49,false),(18,false),(65,true),(69,true),(73,false),(77,true),(86,false),(91,false)]
theorem inp_6295 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6295 := by
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6295 (by decide) v h
def cl_6298 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,true),(77,true),(86,false),(91,false)]
theorem inp_6298 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6298 := by
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6298 (by decide) v h
def cl_6302 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,true),(77,true),(86,false),(91,false)]
theorem inp_6302 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6302 := by
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6302 (by decide) v h
def cl_6306 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,false),(77,false),(86,true),(91,false)]
theorem inp_6306 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6306 := by
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6306 (by decide) v h
def cl_6310 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,false),(77,false),(86,true),(91,false)]
theorem inp_6310 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6310 := by
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6310 (by decide) v h
def cl_6362 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,true),(77,true),(86,false),(91,true)]
theorem inp_6362 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6362 := by
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6362 (by decide) v h
def cl_6366 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,true),(77,true),(86,false),(91,true)]
theorem inp_6366 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6366 := by
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6366 (by decide) v h
def cl_6434 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,false),(77,false),(85,true),(90,false)]
theorem inp_6434 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6434 := by
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6434 (by decide) v h
def cl_6436 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,false),(77,false),(85,true),(90,false)]
theorem inp_6436 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6436 := by
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6436 (by decide) v h
def cl_6438 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,false),(77,false),(85,true),(90,false)]
theorem inp_6438 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6438 := by
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6438 (by decide) v h
def cl_6440 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,false),(77,false),(85,true),(90,false)]
theorem inp_6440 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6440 := by
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6440 (by decide) v h
def cl_6442 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,true),(77,false),(85,true),(90,false)]
theorem inp_6442 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6442 := by
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6442 (by decide) v h
def cl_6444 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,true),(77,false),(85,true),(90,false)]
theorem inp_6444 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6444 := by
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6444 (by decide) v h
def cl_6450 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,false),(77,true),(85,true),(90,false)]
theorem inp_6450 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6450 := by
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6450 (by decide) v h
end Percolation.Replay
