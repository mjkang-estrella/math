import NInputs133
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_7597 : CNF.NClause := [(59,false),(28,false),(62,false),(70,true),(73,true),(81,false),(84,true),(90,false)]
theorem inp_7597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7597 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7597 (by decide) v hb
def cl_7598 : CNF.NClause := [(59,false),(28,true),(62,false),(70,true),(73,true),(81,false),(84,true),(90,false)]
theorem inp_7598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7598 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7598 (by decide) v hb
def cl_7599 : CNF.NClause := [(59,false),(28,false),(62,true),(70,true),(73,true),(81,false),(84,true),(90,false)]
theorem inp_7599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7599 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7599 (by decide) v hb
def cl_7600 : CNF.NClause := [(59,false),(28,true),(62,true),(70,true),(73,true),(81,false),(84,true),(90,false)]
theorem inp_7600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7600 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7600 (by decide) v hb
def cl_7601 : CNF.NClause := [(59,false),(28,false),(62,false),(70,false),(73,false),(81,true),(84,true),(90,false)]
theorem inp_7601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7601 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7601 (by decide) v hb
def cl_7602 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,false),(81,true),(84,true),(90,false)]
theorem inp_7602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7602 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7602 (by decide) v hb
def cl_7603 : CNF.NClause := [(59,false),(28,false),(62,true),(70,false),(73,false),(81,true),(84,true),(90,false)]
theorem inp_7603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7603 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7603 (by decide) v hb
def cl_7604 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,false),(81,true),(84,true),(90,false)]
theorem inp_7604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7604 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7604 (by decide) v hb
def cl_7605 : CNF.NClause := [(59,false),(28,false),(62,false),(70,true),(73,false),(81,true),(84,true),(90,false)]
theorem inp_7605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7605 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7605 (by decide) v hb
def cl_7606 : CNF.NClause := [(59,false),(28,true),(62,false),(70,true),(73,false),(81,true),(84,true),(90,false)]
theorem inp_7606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7606 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7606 (by decide) v hb
def cl_7607 : CNF.NClause := [(59,false),(28,false),(62,true),(70,true),(73,false),(81,true),(84,true),(90,false)]
theorem inp_7607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7607 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7607 (by decide) v hb
def cl_7608 : CNF.NClause := [(59,false),(28,true),(62,true),(70,true),(73,false),(81,true),(84,true),(90,false)]
theorem inp_7608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7608 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7608 (by decide) v hb
def cl_7609 : CNF.NClause := [(59,false),(28,false),(62,false),(70,false),(73,true),(81,true),(84,true),(90,false)]
theorem inp_7609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7609 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7609 (by decide) v hb
def cl_7610 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,true),(81,true),(84,true),(90,false)]
theorem inp_7610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7610 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7610 (by decide) v hb
def cl_7611 : CNF.NClause := [(59,false),(28,false),(62,true),(70,false),(73,true),(81,true),(84,true),(90,false)]
theorem inp_7611 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7611 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7611 (by decide) v hb
def cl_7612 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,true),(81,true),(84,true),(90,false)]
theorem inp_7612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7612 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7612 (by decide) v hb
def cl_7613 : CNF.NClause := [(59,false),(28,false),(62,false),(70,true),(73,true),(81,true),(84,true),(90,false)]
theorem inp_7613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7613 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7613 (by decide) v hb
def cl_7614 : CNF.NClause := [(59,false),(28,true),(62,false),(70,true),(73,true),(81,true),(84,true),(90,false)]
theorem inp_7614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7614 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7614 (by decide) v hb
def cl_7615 : CNF.NClause := [(59,false),(28,false),(62,true),(70,true),(73,true),(81,true),(84,true),(90,false)]
theorem inp_7615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7615 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7615 (by decide) v hb
def cl_7616 : CNF.NClause := [(59,false),(28,true),(62,true),(70,true),(73,true),(81,true),(84,true),(90,false)]
theorem inp_7616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7616 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7616 (by decide) v hb
def cl_7617 : CNF.NClause := [(59,false),(28,false),(62,false),(70,false),(73,false),(81,false),(84,false),(90,true)]
theorem inp_7617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7617 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7617 (by decide) v hb
def cl_7618 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,false),(81,false),(84,false),(90,true)]
theorem inp_7618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7618 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7618 (by decide) v hb
def cl_7619 : CNF.NClause := [(59,false),(28,false),(62,true),(70,false),(73,false),(81,false),(84,false),(90,true)]
theorem inp_7619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7619 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7619 (by decide) v hb
def cl_7620 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,false),(81,false),(84,false),(90,true)]
theorem inp_7620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7620 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7620 (by decide) v hb
def cl_7621 : CNF.NClause := [(59,false),(28,false),(62,false),(70,true),(73,false),(81,false),(84,false),(90,true)]
theorem inp_7621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7621 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7621 (by decide) v hb
def cl_7622 : CNF.NClause := [(59,false),(28,true),(62,false),(70,true),(73,false),(81,false),(84,false),(90,true)]
theorem inp_7622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7622 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7622 (by decide) v hb
def cl_7623 : CNF.NClause := [(59,false),(28,false),(62,true),(70,true),(73,false),(81,false),(84,false),(90,true)]
theorem inp_7623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7623 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7623 (by decide) v hb
def cl_7624 : CNF.NClause := [(59,false),(28,true),(62,true),(70,true),(73,false),(81,false),(84,false),(90,true)]
theorem inp_7624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7624 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7624 (by decide) v hb
def cl_7625 : CNF.NClause := [(59,false),(28,false),(62,false),(70,false),(73,true),(81,false),(84,false),(90,true)]
theorem inp_7625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7625 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7625 (by decide) v hb
def cl_7626 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,true),(81,false),(84,false),(90,true)]
theorem inp_7626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7626 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7626 (by decide) v hb
def cl_7627 : CNF.NClause := [(59,false),(28,false),(62,true),(70,false),(73,true),(81,false),(84,false),(90,true)]
theorem inp_7627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7627 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7627 (by decide) v hb
def cl_7628 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,true),(81,false),(84,false),(90,true)]
theorem inp_7628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7628 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7628 (by decide) v hb
def cl_7629 : CNF.NClause := [(59,false),(28,false),(62,false),(70,true),(73,true),(81,false),(84,false),(90,true)]
theorem inp_7629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7629 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7629 (by decide) v hb
def cl_7630 : CNF.NClause := [(59,false),(28,true),(62,false),(70,true),(73,true),(81,false),(84,false),(90,true)]
theorem inp_7630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7630 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7630 (by decide) v hb
def cl_7631 : CNF.NClause := [(59,false),(28,false),(62,true),(70,true),(73,true),(81,false),(84,false),(90,true)]
theorem inp_7631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7631 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7631 (by decide) v hb
def cl_7632 : CNF.NClause := [(59,false),(28,true),(62,true),(70,true),(73,true),(81,false),(84,false),(90,true)]
theorem inp_7632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7632 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7632 (by decide) v hb
def cl_7633 : CNF.NClause := [(59,false),(28,false),(62,false),(70,false),(73,false),(81,true),(84,false),(90,true)]
theorem inp_7633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7633 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7633 (by decide) v hb
def cl_7634 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,false),(81,true),(84,false),(90,true)]
theorem inp_7634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7634 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7634 (by decide) v hb
def cl_7635 : CNF.NClause := [(59,false),(28,false),(62,true),(70,false),(73,false),(81,true),(84,false),(90,true)]
theorem inp_7635 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7635 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7635 (by decide) v hb
def cl_7636 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,false),(81,true),(84,false),(90,true)]
theorem inp_7636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7636 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7636 (by decide) v hb
def cl_7637 : CNF.NClause := [(59,false),(28,false),(62,false),(70,true),(73,false),(81,true),(84,false),(90,true)]
theorem inp_7637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7637 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7637 (by decide) v hb
def cl_7638 : CNF.NClause := [(59,false),(28,true),(62,false),(70,true),(73,false),(81,true),(84,false),(90,true)]
theorem inp_7638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7638 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7638 (by decide) v hb
def cl_7639 : CNF.NClause := [(59,false),(28,false),(62,true),(70,true),(73,false),(81,true),(84,false),(90,true)]
theorem inp_7639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7639 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7639 (by decide) v hb
def cl_7640 : CNF.NClause := [(59,false),(28,true),(62,true),(70,true),(73,false),(81,true),(84,false),(90,true)]
theorem inp_7640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7640 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7640 (by decide) v hb
def cl_7641 : CNF.NClause := [(59,false),(28,false),(62,false),(70,false),(73,true),(81,true),(84,false),(90,true)]
theorem inp_7641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7641 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7641 (by decide) v hb
def cl_7642 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,true),(81,true),(84,false),(90,true)]
theorem inp_7642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7642 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7642 (by decide) v hb
def cl_7643 : CNF.NClause := [(59,false),(28,false),(62,true),(70,false),(73,true),(81,true),(84,false),(90,true)]
theorem inp_7643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7643 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7643 (by decide) v hb
def cl_7644 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,true),(81,true),(84,false),(90,true)]
theorem inp_7644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7644 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7644 (by decide) v hb
def cl_7645 : CNF.NClause := [(59,false),(28,false),(62,false),(70,true),(73,true),(81,true),(84,false),(90,true)]
theorem inp_7645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7645 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7645 (by decide) v hb
def cl_7646 : CNF.NClause := [(59,false),(28,true),(62,false),(70,true),(73,true),(81,true),(84,false),(90,true)]
theorem inp_7646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7646 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7646 (by decide) v hb
end Percolation.NReplay
