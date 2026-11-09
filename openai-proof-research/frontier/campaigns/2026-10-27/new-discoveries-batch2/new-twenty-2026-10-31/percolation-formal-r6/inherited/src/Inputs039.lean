import Inputs038
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_7170 : CNF.NClause := [(56,false),(25,true),(62,false),(63,false),(64,false),(65,false),(66,false),(92,false)]
theorem inp_7170 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7170 := by
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7170 (by decide) v h
def cl_7173 : CNF.NClause := [(56,false),(25,false),(62,false),(63,true),(64,false),(65,false),(66,false),(92,false)]
theorem inp_7173 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7173 := by
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7173 (by decide) v h
def cl_7174 : CNF.NClause := [(56,false),(25,true),(62,false),(63,true),(64,false),(65,false),(66,false),(92,false)]
theorem inp_7174 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7174 := by
  exact input_gate (spreadGate5 25) (spread_mem 25) cl_7174 (by decide) v h
def cl_7306 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,true),(79,false),(83,false),(91,false)]
theorem inp_7306 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7306 := by
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7306 (by decide) v h
def cl_7308 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,true),(79,false),(83,false),(91,false)]
theorem inp_7308 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7308 := by
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7308 (by decide) v h
def cl_7322 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,true),(79,true),(83,false),(91,false)]
theorem inp_7322 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7322 := by
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7322 (by decide) v h
def cl_7324 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,true),(79,true),(83,false),(91,false)]
theorem inp_7324 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7324 := by
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7324 (by decide) v h
def cl_7338 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,true),(79,false),(83,true),(91,false)]
theorem inp_7338 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7338 := by
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7338 (by decide) v h
def cl_7340 : CNF.NClause := [(57,false),(26,true),(62,true),(71,false),(75,true),(79,false),(83,true),(91,false)]
theorem inp_7340 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7340 := by
  exact input_gate (spreadGate5 26) (spread_mem 26) cl_7340 (by decide) v h
def cl_7426 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,false),(78,false),(85,false),(89,false)]
theorem inp_7426 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7426 := by
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7426 (by decide) v h
def cl_7428 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,false),(78,false),(85,false),(89,false)]
theorem inp_7428 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7428 := by
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7428 (by decide) v h
def cl_7434 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,true),(78,false),(85,false),(89,false)]
theorem inp_7434 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7434 := by
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7434 (by decide) v h
def cl_7436 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,true),(78,false),(85,false),(89,false)]
theorem inp_7436 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7436 := by
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7436 (by decide) v h
def cl_7458 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,false),(78,false),(85,true),(89,false)]
theorem inp_7458 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7458 := by
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7458 (by decide) v h
def cl_7460 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,false),(78,false),(85,true),(89,false)]
theorem inp_7460 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7460 := by
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7460 (by decide) v h
def cl_7466 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,true),(78,false),(85,true),(89,false)]
theorem inp_7466 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7466 := by
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7466 (by decide) v h
def cl_7468 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,true),(78,false),(85,true),(89,false)]
theorem inp_7468 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7468 := by
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7468 (by decide) v h
def cl_7490 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,false),(78,false),(85,false),(89,true)]
theorem inp_7490 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7490 := by
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7490 (by decide) v h
def cl_7492 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,false),(78,false),(85,false),(89,true)]
theorem inp_7492 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7492 := by
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7492 (by decide) v h
def cl_7522 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,false),(78,false),(85,true),(89,true)]
theorem inp_7522 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7522 := by
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7522 (by decide) v h
def cl_7524 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,false),(78,false),(85,true),(89,true)]
theorem inp_7524 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7524 := by
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7524 (by decide) v h
def cl_7530 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,true),(78,false),(85,true),(89,true)]
theorem inp_7530 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7530 := by
  exact input_gate (spreadGate5 27) (spread_mem 27) cl_7530 (by decide) v h
def cl_7554 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,false),(81,false),(84,false),(90,false)]
theorem inp_7554 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7554 := by
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7554 (by decide) v h
def cl_7556 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,false),(81,false),(84,false),(90,false)]
theorem inp_7556 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7556 := by
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7556 (by decide) v h
def cl_7557 : CNF.NClause := [(59,false),(28,false),(62,false),(70,true),(73,false),(81,false),(84,false),(90,false)]
theorem inp_7557 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7557 := by
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7557 (by decide) v h
def cl_7558 : CNF.NClause := [(59,false),(28,true),(62,false),(70,true),(73,false),(81,false),(84,false),(90,false)]
theorem inp_7558 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7558 := by
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7558 (by decide) v h
def cl_7559 : CNF.NClause := [(59,false),(28,false),(62,true),(70,true),(73,false),(81,false),(84,false),(90,false)]
theorem inp_7559 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7559 := by
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7559 (by decide) v h
def cl_7562 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,true),(81,false),(84,false),(90,false)]
theorem inp_7562 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7562 := by
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7562 (by decide) v h
def cl_7564 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,true),(81,false),(84,false),(90,false)]
theorem inp_7564 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7564 := by
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7564 (by decide) v h
def cl_7570 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,false),(81,true),(84,false),(90,false)]
theorem inp_7570 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7570 := by
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7570 (by decide) v h
def cl_7572 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,false),(81,true),(84,false),(90,false)]
theorem inp_7572 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7572 := by
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7572 (by decide) v h
def cl_7578 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,true),(81,true),(84,false),(90,false)]
theorem inp_7578 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7578 := by
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7578 (by decide) v h
def cl_7580 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,true),(81,true),(84,false),(90,false)]
theorem inp_7580 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7580 := by
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7580 (by decide) v h
def cl_7586 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,false),(81,false),(84,true),(90,false)]
theorem inp_7586 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7586 := by
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7586 (by decide) v h
def cl_7588 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,false),(81,false),(84,true),(90,false)]
theorem inp_7588 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7588 := by
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7588 (by decide) v h
def cl_7842 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,false),(77,false),(82,true),(87,false)]
theorem inp_7842 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7842 := by
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7842 (by decide) v h
def cl_7844 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,false),(77,false),(82,true),(87,false)]
theorem inp_7844 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7844 := by
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7844 (by decide) v h
def cl_7850 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,true),(77,false),(82,true),(87,false)]
theorem inp_7850 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7850 := by
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7850 (by decide) v h
def cl_7852 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,true),(77,false),(82,true),(87,false)]
theorem inp_7852 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7852 := by
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7852 (by decide) v h
def cl_7858 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,false),(77,true),(82,true),(87,false)]
theorem inp_7858 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7858 := by
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7858 (by decide) v h
def cl_7860 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,false),(77,true),(82,true),(87,false)]
theorem inp_7860 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7860 := by
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7860 (by decide) v h
def cl_8054 : CNF.NClause := [(125,true),(132,true),(134,true),(141,false),(148,true),(151,true)]
theorem inp_8054 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8054 := by
  exact input_gate (closedGate5 0 14) (closed_mem 0 14) cl_8054 (by decide) v h
def cl_8094 : CNF.NClause := [(128,true),(129,true),(135,true),(141,true),(147,true),(150,false)]
theorem inp_8094 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8094 := by
  exact input_gate (closedGate5 0 21) (closed_mem 0 21) cl_8094 (by decide) v h
def cl_8147 : CNF.NClause := [(124,false),(130,true),(136,true),(142,true),(148,true),(150,true)]
theorem inp_8147 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8147 := by
  exact input_gate (closedGate5 0 29) (closed_mem 0 29) cl_8147 (by decide) v h
def cl_8520 : CNF.NClause := [(186,true),(191,true),(196,true),(201,true),(206,true),(211,false)]
theorem inp_8520 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8520 := by
  exact input_gate (closedGate5 2 30) (closed_mem 2 30) cl_8520 (by decide) v h
def cl_8572 : CNF.NClause := [(219,true),(226,false),(228,true),(235,true),(237,true),(244,true)]
theorem inp_8572 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8572 := by
  exact input_gate (closedGate5 3 7) (closed_mem 3 7) cl_8572 (by decide) v h
def cl_8659 : CNF.NClause := [(219,true),(222,true),(230,true),(233,true),(241,false),(245,true)]
theorem inp_8659 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8659 := by
  exact input_gate (closedGate5 3 22) (closed_mem 3 22) cl_8659 (by decide) v h
def cl_8671 : CNF.NClause := [(218,true),(222,true),(231,true),(235,true),(239,false),(246,true)]
theorem inp_8671 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8671 := by
  exact input_gate (closedGate5 3 24) (closed_mem 3 24) cl_8671 (by decide) v h
def cl_8684 : CNF.NClause := [(217,true),(226,true),(230,true),(234,false),(238,true),(246,true)]
theorem inp_8684 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8684 := by
  exact input_gate (closedGate5 3 26) (closed_mem 3 26) cl_8684 (by decide) v h
def cl_8685 : CNF.NClause := [(217,true),(226,true),(230,false),(234,true),(238,true),(246,true)]
theorem inp_8685 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8685 := by
  exact input_gate (closedGate5 3 26) (closed_mem 3 26) cl_8685 (by decide) v h
end Percolation.Replay
