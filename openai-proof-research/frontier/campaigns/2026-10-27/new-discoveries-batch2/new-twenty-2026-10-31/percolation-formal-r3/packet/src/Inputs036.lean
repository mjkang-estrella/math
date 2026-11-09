import Inputs035
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_5218 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,false),(81,false),(82,true),(88,true)]
theorem inp_5218 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5218 := by
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5218 (by decide) v h
def cl_5226 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,true),(81,false),(82,true),(88,true)]
theorem inp_5226 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5226 := by
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5226 (by decide) v h
def cl_5266 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,false),(75,true),(76,false),(92,false)]
theorem inp_5266 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5266 := by
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5266 (by decide) v h
def cl_5268 : CNF.NClause := [(41,false),(10,true),(72,true),(73,false),(74,false),(75,true),(76,false),(92,false)]
theorem inp_5268 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5268 := by
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5268 (by decide) v h
def cl_5270 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,false),(75,true),(76,false),(92,false)]
theorem inp_5270 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5270 := by
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5270 (by decide) v h
def cl_5272 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,false),(75,true),(76,false),(92,false)]
theorem inp_5272 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5272 := by
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5272 (by decide) v h
def cl_5298 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,false),(75,true),(76,true),(92,false)]
theorem inp_5298 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5298 := by
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5298 (by decide) v h
def cl_5302 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(74,false),(75,true),(76,true),(92,false)]
theorem inp_5302 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5302 := by
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5302 (by decide) v h
def cl_5375 : CNF.NClause := [(41,false),(10,false),(72,true),(73,true),(74,true),(75,true),(76,true),(92,true)]
theorem inp_5375 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5375 := by
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5375 (by decide) v h
def cl_5376 : CNF.NClause := [(41,false),(10,true),(72,true),(73,true),(74,true),(75,true),(76,true),(92,true)]
theorem inp_5376 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5376 := by
  exact input_gate (spreadGate5 10) (spread_mem 10) cl_5376 (by decide) v h
def cl_5378 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,false),(80,false),(83,false),(90,false)]
theorem inp_5378 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5378 := by
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5378 (by decide) v h
def cl_5382 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,false),(80,false),(83,false),(90,false)]
theorem inp_5382 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5382 := by
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5382 (by decide) v h
def cl_5386 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,true),(80,false),(83,false),(90,false)]
theorem inp_5386 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5386 := by
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5386 (by decide) v h
def cl_5390 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,true),(80,false),(83,false),(90,false)]
theorem inp_5390 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5390 := by
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5390 (by decide) v h
def cl_5393 : CNF.NClause := [(42,false),(11,false),(66,false),(69,false),(72,false),(80,true),(83,false),(90,false)]
theorem inp_5393 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5393 := by
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5393 (by decide) v h
def cl_5394 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,false),(80,true),(83,false),(90,false)]
theorem inp_5394 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5394 := by
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5394 (by decide) v h
def cl_5395 : CNF.NClause := [(42,false),(11,false),(66,true),(69,false),(72,false),(80,true),(83,false),(90,false)]
theorem inp_5395 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5395 := by
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5395 (by decide) v h
def cl_5398 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,false),(80,true),(83,false),(90,false)]
theorem inp_5398 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5398 := by
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5398 (by decide) v h
def cl_5402 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,true),(80,true),(83,false),(90,false)]
theorem inp_5402 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5402 := by
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5402 (by decide) v h
def cl_5406 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,true),(80,true),(83,false),(90,false)]
theorem inp_5406 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5406 := by
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5406 (by decide) v h
def cl_5409 : CNF.NClause := [(42,false),(11,false),(66,false),(69,false),(72,false),(80,false),(83,true),(90,false)]
theorem inp_5409 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5409 := by
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5409 (by decide) v h
def cl_5410 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,false),(80,false),(83,true),(90,false)]
theorem inp_5410 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5410 := by
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5410 (by decide) v h
def cl_5413 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(72,false),(80,false),(83,true),(90,false)]
theorem inp_5413 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5413 := by
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5413 (by decide) v h
def cl_5414 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,false),(80,false),(83,true),(90,false)]
theorem inp_5414 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5414 := by
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5414 (by decide) v h
def cl_5418 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,true),(80,false),(83,true),(90,false)]
theorem inp_5418 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5418 := by
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5418 (by decide) v h
def cl_5422 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,true),(80,false),(83,true),(90,false)]
theorem inp_5422 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5422 := by
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5422 (by decide) v h
def cl_5426 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,false),(80,true),(83,true),(90,false)]
theorem inp_5426 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5426 := by
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5426 (by decide) v h
def cl_5430 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,false),(80,true),(83,true),(90,false)]
theorem inp_5430 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5430 := by
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5430 (by decide) v h
def cl_5434 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,true),(80,true),(83,true),(90,false)]
theorem inp_5434 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5434 := by
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5434 (by decide) v h
def cl_5438 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,true),(80,true),(83,true),(90,false)]
theorem inp_5438 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5438 := by
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5438 (by decide) v h
def cl_5442 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,false),(80,false),(83,false),(90,true)]
theorem inp_5442 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5442 := by
  exact input_gate (spreadGate5 11) (spread_mem 11) cl_5442 (by decide) v h
def cl_5633 : CNF.NClause := [(44,true),(13,false),(65,false),(71,false),(72,false),(78,false),(84,false),(88,false)]
theorem inp_5633 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5633 := by
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5633 (by decide) v h
def cl_5642 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,true),(78,false),(84,false),(88,false)]
theorem inp_5642 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5642 := by
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5642 (by decide) v h
def cl_5646 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,true),(78,false),(84,false),(88,false)]
theorem inp_5646 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5646 := by
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5646 (by decide) v h
def cl_5666 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,false),(78,false),(84,true),(88,false)]
theorem inp_5666 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5666 := by
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5666 (by decide) v h
def cl_5670 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,false),(78,false),(84,true),(88,false)]
theorem inp_5670 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5670 := by
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5670 (by decide) v h
def cl_5674 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,true),(78,false),(84,true),(88,false)]
theorem inp_5674 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5674 := by
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5674 (by decide) v h
def cl_5678 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,true),(78,false),(84,true),(88,false)]
theorem inp_5678 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5678 := by
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5678 (by decide) v h
def cl_5698 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,false),(78,false),(84,false),(88,true)]
theorem inp_5698 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5698 := by
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5698 (by decide) v h
def cl_5702 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,false),(78,false),(84,false),(88,true)]
theorem inp_5702 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5702 := by
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5702 (by decide) v h
def cl_5762 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,false),(79,false),(86,false),(89,false)]
theorem inp_5762 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5762 := by
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5762 (by decide) v h
def cl_5825 : CNF.NClause := [(45,false),(14,false),(63,false),(70,false),(72,false),(79,false),(86,false),(89,true)]
theorem inp_5825 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5825 := by
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5825 (by decide) v h
def cl_5826 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,false),(79,false),(86,false),(89,true)]
theorem inp_5826 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5826 := by
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5826 (by decide) v h
def cl_5827 : CNF.NClause := [(45,false),(14,false),(63,true),(70,false),(72,false),(79,false),(86,false),(89,true)]
theorem inp_5827 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5827 := by
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5827 (by decide) v h
def cl_5842 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,false),(79,true),(86,false),(89,true)]
theorem inp_5842 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5842 := by
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5842 (by decide) v h
def cl_5844 : CNF.NClause := [(45,false),(14,true),(63,true),(70,false),(72,false),(79,true),(86,false),(89,true)]
theorem inp_5844 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5844 := by
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5844 (by decide) v h
def cl_5890 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,false),(80,false),(81,false),(92,false)]
theorem inp_5890 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5890 := by
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5890 (by decide) v h
def cl_5898 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,true),(80,false),(81,false),(92,false)]
theorem inp_5898 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5898 := by
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5898 (by decide) v h
def cl_5906 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,false),(80,true),(81,false),(92,false)]
theorem inp_5906 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5906 := by
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5906 (by decide) v h
def cl_5914 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,true),(80,true),(81,false),(92,false)]
theorem inp_5914 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5914 := by
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5914 (by decide) v h
end Percolation.Replay
