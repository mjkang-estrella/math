import Inputs034
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_4380 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,true),(80,true),(85,false),(87,false)]
theorem inp_4380 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4380 := by
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4380 (by decide) v h
def cl_4394 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,true),(80,false),(85,true),(87,false)]
theorem inp_4394 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4394 := by
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4394 (by decide) v h
def cl_4396 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,true),(80,false),(85,true),(87,false)]
theorem inp_4396 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4396 := by
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4396 (by decide) v h
def cl_4398 : CNF.NClause := [(34,false),(3,true),(65,false),(70,true),(75,true),(80,false),(85,true),(87,false)]
theorem inp_4398 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4398 := by
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4398 (by decide) v h
def cl_4410 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,true),(80,true),(85,true),(87,false)]
theorem inp_4410 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4410 := by
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4410 (by decide) v h
def cl_4417 : CNF.NClause := [(34,false),(3,false),(65,false),(70,false),(75,false),(80,false),(85,false),(87,true)]
theorem inp_4417 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4417 := by
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4417 (by decide) v h
def cl_4418 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,false),(80,false),(85,false),(87,true)]
theorem inp_4418 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4418 := by
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4418 (by decide) v h
def cl_4458 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,true),(80,false),(85,true),(87,true)]
theorem inp_4458 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4458 := by
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4458 (by decide) v h
def cl_4474 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,true),(80,true),(85,true),(87,true)]
theorem inp_4474 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4474 := by
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4474 (by decide) v h
def cl_4481 : CNF.NClause := [(35,true),(4,false),(63,false),(68,false),(73,false),(78,false),(83,false),(87,false)]
theorem inp_4481 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4481 := by
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4481 (by decide) v h
def cl_4483 : CNF.NClause := [(35,false),(4,false),(63,true),(68,false),(73,false),(78,false),(83,false),(87,false)]
theorem inp_4483 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4483 := by
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4483 (by decide) v h
def cl_4484 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,false),(78,false),(83,false),(87,false)]
theorem inp_4484 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4484 := by
  exact input_gate (spreadGate5 4) (spread_mem 4) cl_4484 (by decide) v h
def cl_4612 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,false),(85,false),(86,false),(92,false)]
theorem inp_4612 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4612 := by
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4612 (by decide) v h
def cl_4620 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,true),(85,false),(86,false),(92,false)]
theorem inp_4620 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4620 := by
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4620 (by decide) v h
def cl_4626 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,false),(85,true),(86,false),(92,false)]
theorem inp_4626 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4626 := by
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4626 (by decide) v h
def cl_4628 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,false),(85,true),(86,false),(92,false)]
theorem inp_4628 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4628 := by
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4628 (by decide) v h
def cl_4630 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,false),(85,true),(86,false),(92,false)]
theorem inp_4630 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4630 := by
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4630 (by decide) v h
def cl_4632 : CNF.NClause := [(36,false),(5,true),(82,true),(83,true),(84,false),(85,true),(86,false),(92,false)]
theorem inp_4632 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4632 := by
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4632 (by decide) v h
def cl_4634 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,true),(85,true),(86,false),(92,false)]
theorem inp_4634 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4634 := by
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4634 (by decide) v h
def cl_4638 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,true),(85,true),(86,false),(92,false)]
theorem inp_4638 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4638 := by
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4638 (by decide) v h
def cl_4690 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,false),(85,true),(86,false),(92,true)]
theorem inp_4690 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4690 := by
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4690 (by decide) v h
def cl_4692 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,false),(85,true),(86,false),(92,true)]
theorem inp_4692 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4692 := by
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4692 (by decide) v h
def cl_4698 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,true),(85,true),(86,false),(92,true)]
theorem inp_4698 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4698 := by
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4698 (by decide) v h
def cl_4769 : CNF.NClause := [(37,false),(6,false),(66,false),(70,false),(74,false),(78,false),(82,true),(91,false)]
theorem inp_4769 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4769 := by
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4769 (by decide) v h
def cl_4773 : CNF.NClause := [(37,false),(6,false),(66,false),(70,true),(74,false),(78,false),(82,true),(91,false)]
theorem inp_4773 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4773 := by
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4773 (by decide) v h
def cl_4778 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,true),(78,false),(82,true),(91,false)]
theorem inp_4778 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4778 := by
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4778 (by decide) v h
def cl_4782 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,true),(78,false),(82,true),(91,false)]
theorem inp_4782 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4782 := by
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4782 (by decide) v h
def cl_4833 : CNF.NClause := [(37,false),(6,false),(66,false),(70,false),(74,false),(78,false),(82,true),(91,true)]
theorem inp_4833 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4833 := by
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4833 (by decide) v h
def cl_4898 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,false),(80,false),(82,true),(89,false)]
theorem inp_4898 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4898 := by
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4898 (by decide) v h
def cl_4902 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,false),(80,false),(82,true),(89,false)]
theorem inp_4902 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4902 := by
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4902 (by decide) v h
def cl_4906 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,true),(80,false),(82,true),(89,false)]
theorem inp_4906 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4906 := by
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4906 (by decide) v h
def cl_4914 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,false),(80,true),(82,true),(89,false)]
theorem inp_4914 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4914 := by
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4914 (by decide) v h
def cl_4922 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,true),(80,true),(82,true),(89,false)]
theorem inp_4922 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4922 := by
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4922 (by decide) v h
def cl_4962 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,false),(80,false),(82,true),(89,true)]
theorem inp_4962 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4962 := by
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4962 (by decide) v h
def cl_4966 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,false),(80,false),(82,true),(89,true)]
theorem inp_4966 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4966 := by
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4966 (by decide) v h
def cl_4970 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,true),(80,false),(82,true),(89,true)]
theorem inp_4970 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4970 := by
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4970 (by decide) v h
def cl_4978 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,false),(80,true),(82,true),(89,true)]
theorem inp_4978 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4978 := by
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4978 (by decide) v h
def cl_4986 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,true),(80,true),(82,true),(89,true)]
theorem inp_4986 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4986 := by
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4986 (by decide) v h
def cl_5026 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,false),(79,false),(82,true),(90,false)]
theorem inp_5026 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5026 := by
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5026 (by decide) v h
def cl_5028 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,false),(79,false),(82,true),(90,false)]
theorem inp_5028 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5028 := by
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5028 (by decide) v h
def cl_5034 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,true),(79,false),(82,true),(90,false)]
theorem inp_5034 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5034 := by
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5034 (by decide) v h
def cl_5036 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,true),(79,false),(82,true),(90,false)]
theorem inp_5036 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5036 := by
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5036 (by decide) v h
def cl_5042 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,false),(79,true),(82,true),(90,false)]
theorem inp_5042 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5042 := by
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5042 (by decide) v h
def cl_5044 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,false),(79,true),(82,true),(90,false)]
theorem inp_5044 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5044 := by
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5044 (by decide) v h
def cl_5050 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,true),(79,true),(82,true),(90,false)]
theorem inp_5050 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5050 := by
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5050 (by decide) v h
def cl_5052 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,true),(79,true),(82,true),(90,false)]
theorem inp_5052 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5052 := by
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5052 (by decide) v h
def cl_5154 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,false),(81,false),(82,true),(88,false)]
theorem inp_5154 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5154 := by
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5154 (by decide) v h
def cl_5162 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,true),(81,false),(82,true),(88,false)]
theorem inp_5162 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5162 := by
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5162 (by decide) v h
def cl_5164 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,true),(81,false),(82,true),(88,false)]
theorem inp_5164 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5164 := by
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5164 (by decide) v h
def cl_5166 : CNF.NClause := [(40,false),(9,true),(63,false),(69,true),(75,true),(81,false),(82,true),(88,false)]
theorem inp_5166 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5166 := by
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5166 (by decide) v h
end Percolation.Replay
