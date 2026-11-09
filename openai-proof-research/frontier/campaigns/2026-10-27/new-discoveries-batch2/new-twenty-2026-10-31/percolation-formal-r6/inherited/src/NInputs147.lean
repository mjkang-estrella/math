import NInputs146
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_8584 : CNF.NClause := [(218,true),(224,false),(230,true),(236,true),(237,true),(243,true)]
theorem inp_8584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8584 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 9) (closed_mem 3 9) cl_8584 (by decide) v hb
def cl_8585 : CNF.NClause := [(218,false),(224,true),(230,true),(236,true),(237,true),(243,true)]
theorem inp_8585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8585 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 9) (closed_mem 3 9) cl_8585 (by decide) v hb
def cl_8587 : CNF.NClause := [(227,true),(228,true),(229,true),(230,true),(231,false),(247,true)]
theorem inp_8587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8587 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 10) (closed_mem 3 10) cl_8587 (by decide) v hb
def cl_8588 : CNF.NClause := [(227,true),(228,true),(229,true),(230,false),(231,true),(247,true)]
theorem inp_8588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8588 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 10) (closed_mem 3 10) cl_8588 (by decide) v hb
def cl_8589 : CNF.NClause := [(227,true),(228,true),(229,false),(230,true),(231,true),(247,true)]
theorem inp_8589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8589 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 10) (closed_mem 3 10) cl_8589 (by decide) v hb
def cl_8590 : CNF.NClause := [(227,true),(228,false),(229,true),(230,true),(231,true),(247,true)]
theorem inp_8590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8590 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 10) (closed_mem 3 10) cl_8590 (by decide) v hb
def cl_8591 : CNF.NClause := [(227,false),(228,true),(229,true),(230,true),(231,true),(247,true)]
theorem inp_8591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8591 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 10) (closed_mem 3 10) cl_8591 (by decide) v hb
def cl_8592 : CNF.NClause := [(221,true),(224,true),(227,true),(235,true),(238,true),(245,false)]
theorem inp_8592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8592 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 11) (closed_mem 3 11) cl_8592 (by decide) v hb
def cl_8593 : CNF.NClause := [(221,true),(224,true),(227,true),(235,true),(238,false),(245,true)]
theorem inp_8593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8593 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 11) (closed_mem 3 11) cl_8593 (by decide) v hb
def cl_8594 : CNF.NClause := [(221,true),(224,true),(227,true),(235,false),(238,true),(245,true)]
theorem inp_8594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8594 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 11) (closed_mem 3 11) cl_8594 (by decide) v hb
def cl_8595 : CNF.NClause := [(221,true),(224,true),(227,false),(235,true),(238,true),(245,true)]
theorem inp_8595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8595 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 11) (closed_mem 3 11) cl_8595 (by decide) v hb
def cl_8596 : CNF.NClause := [(221,true),(224,false),(227,true),(235,true),(238,true),(245,true)]
theorem inp_8596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8596 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 11) (closed_mem 3 11) cl_8596 (by decide) v hb
def cl_8597 : CNF.NClause := [(221,false),(224,true),(227,true),(235,true),(238,true),(245,true)]
theorem inp_8597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8597 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 11) (closed_mem 3 11) cl_8597 (by decide) v hb
def cl_8598 : CNF.NClause := [(219,true),(223,true),(227,true),(236,true),(240,true),(246,false)]
theorem inp_8598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8598 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 12) (closed_mem 3 12) cl_8598 (by decide) v hb
def cl_8599 : CNF.NClause := [(219,true),(223,true),(227,true),(236,true),(240,false),(246,true)]
theorem inp_8599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8599 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 12) (closed_mem 3 12) cl_8599 (by decide) v hb
def cl_8600 : CNF.NClause := [(219,true),(223,true),(227,true),(236,false),(240,true),(246,true)]
theorem inp_8600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8600 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 12) (closed_mem 3 12) cl_8600 (by decide) v hb
def cl_8601 : CNF.NClause := [(219,true),(223,true),(227,false),(236,true),(240,true),(246,true)]
theorem inp_8601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8601 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 12) (closed_mem 3 12) cl_8601 (by decide) v hb
def cl_8602 : CNF.NClause := [(219,true),(223,false),(227,true),(236,true),(240,true),(246,true)]
theorem inp_8602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8602 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 12) (closed_mem 3 12) cl_8602 (by decide) v hb
def cl_8603 : CNF.NClause := [(219,false),(223,true),(227,true),(236,true),(240,true),(246,true)]
theorem inp_8603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8603 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 12) (closed_mem 3 12) cl_8603 (by decide) v hb
def cl_8609 : CNF.NClause := [(220,false),(226,true),(227,true),(233,true),(239,true),(243,true)]
theorem inp_8609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8609 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 13) (closed_mem 3 13) cl_8609 (by decide) v hb
def cl_8611 : CNF.NClause := [(218,true),(225,true),(227,true),(234,true),(241,false),(244,true)]
theorem inp_8611 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8611 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 14) (closed_mem 3 14) cl_8611 (by decide) v hb
def cl_8612 : CNF.NClause := [(218,true),(225,true),(227,true),(234,false),(241,true),(244,true)]
theorem inp_8612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8612 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 14) (closed_mem 3 14) cl_8612 (by decide) v hb
def cl_8613 : CNF.NClause := [(218,true),(225,true),(227,false),(234,true),(241,true),(244,true)]
theorem inp_8613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8613 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 14) (closed_mem 3 14) cl_8613 (by decide) v hb
def cl_8614 : CNF.NClause := [(218,true),(225,false),(227,true),(234,true),(241,true),(244,true)]
theorem inp_8614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8614 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 14) (closed_mem 3 14) cl_8614 (by decide) v hb
def cl_8615 : CNF.NClause := [(218,false),(225,true),(227,true),(234,true),(241,true),(244,true)]
theorem inp_8615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8615 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 14) (closed_mem 3 14) cl_8615 (by decide) v hb
def cl_8617 : CNF.NClause := [(232,true),(233,true),(234,true),(235,true),(236,false),(247,true)]
theorem inp_8617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8617 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 15) (closed_mem 3 15) cl_8617 (by decide) v hb
def cl_8618 : CNF.NClause := [(232,true),(233,true),(234,true),(235,false),(236,true),(247,true)]
theorem inp_8618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8618 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 15) (closed_mem 3 15) cl_8618 (by decide) v hb
def cl_8619 : CNF.NClause := [(232,true),(233,true),(234,false),(235,true),(236,true),(247,true)]
theorem inp_8619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8619 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 15) (closed_mem 3 15) cl_8619 (by decide) v hb
def cl_8620 : CNF.NClause := [(232,true),(233,false),(234,true),(235,true),(236,true),(247,true)]
theorem inp_8620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8620 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 15) (closed_mem 3 15) cl_8620 (by decide) v hb
def cl_8621 : CNF.NClause := [(232,false),(233,true),(234,true),(235,true),(236,true),(247,true)]
theorem inp_8621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8621 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 15) (closed_mem 3 15) cl_8621 (by decide) v hb
def cl_8622 : CNF.NClause := [(221,true),(223,true),(230,true),(232,true),(239,true),(244,false)]
theorem inp_8622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8622 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 16) (closed_mem 3 16) cl_8622 (by decide) v hb
def cl_8623 : CNF.NClause := [(221,true),(223,true),(230,true),(232,true),(239,false),(244,true)]
theorem inp_8623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8623 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 16) (closed_mem 3 16) cl_8623 (by decide) v hb
def cl_8624 : CNF.NClause := [(221,true),(223,true),(230,true),(232,false),(239,true),(244,true)]
theorem inp_8624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8624 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 16) (closed_mem 3 16) cl_8624 (by decide) v hb
def cl_8625 : CNF.NClause := [(221,true),(223,true),(230,false),(232,true),(239,true),(244,true)]
theorem inp_8625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8625 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 16) (closed_mem 3 16) cl_8625 (by decide) v hb
def cl_8626 : CNF.NClause := [(221,true),(223,false),(230,true),(232,true),(239,true),(244,true)]
theorem inp_8626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8626 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 16) (closed_mem 3 16) cl_8626 (by decide) v hb
def cl_8627 : CNF.NClause := [(221,false),(223,true),(230,true),(232,true),(239,true),(244,true)]
theorem inp_8627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8627 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 16) (closed_mem 3 16) cl_8627 (by decide) v hb
def cl_8629 : CNF.NClause := [(219,true),(225,true),(231,true),(232,true),(238,false),(243,true)]
theorem inp_8629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8629 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 17) (closed_mem 3 17) cl_8629 (by decide) v hb
def cl_8630 : CNF.NClause := [(219,true),(225,true),(231,true),(232,false),(238,true),(243,true)]
theorem inp_8630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8630 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 17) (closed_mem 3 17) cl_8630 (by decide) v hb
def cl_8631 : CNF.NClause := [(219,true),(225,true),(231,false),(232,true),(238,true),(243,true)]
theorem inp_8631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8631 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 17) (closed_mem 3 17) cl_8631 (by decide) v hb
def cl_8632 : CNF.NClause := [(219,true),(225,false),(231,true),(232,true),(238,true),(243,true)]
theorem inp_8632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8632 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 17) (closed_mem 3 17) cl_8632 (by decide) v hb
def cl_8633 : CNF.NClause := [(219,false),(225,true),(231,true),(232,true),(238,true),(243,true)]
theorem inp_8633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8633 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 17) (closed_mem 3 17) cl_8633 (by decide) v hb
def cl_8639 : CNF.NClause := [(220,false),(224,true),(228,true),(232,true),(241,true),(246,true)]
theorem inp_8639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8639 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 18) (closed_mem 3 18) cl_8639 (by decide) v hb
def cl_8640 : CNF.NClause := [(218,true),(226,true),(229,true),(232,true),(240,true),(245,false)]
theorem inp_8640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8640 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 19) (closed_mem 3 19) cl_8640 (by decide) v hb
def cl_8641 : CNF.NClause := [(218,true),(226,true),(229,true),(232,true),(240,false),(245,true)]
theorem inp_8641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8641 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 19) (closed_mem 3 19) cl_8641 (by decide) v hb
def cl_8642 : CNF.NClause := [(218,true),(226,true),(229,true),(232,false),(240,true),(245,true)]
theorem inp_8642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8642 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 19) (closed_mem 3 19) cl_8642 (by decide) v hb
def cl_8644 : CNF.NClause := [(218,true),(226,false),(229,true),(232,true),(240,true),(245,true)]
theorem inp_8644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8644 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 19) (closed_mem 3 19) cl_8644 (by decide) v hb
def cl_8645 : CNF.NClause := [(218,false),(226,true),(229,true),(232,true),(240,true),(245,true)]
theorem inp_8645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8645 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 19) (closed_mem 3 19) cl_8645 (by decide) v hb
def cl_8647 : CNF.NClause := [(222,true),(223,true),(224,true),(225,true),(226,false),(247,true)]
theorem inp_8647 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8647 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 20) (closed_mem 3 20) cl_8647 (by decide) v hb
def cl_8648 : CNF.NClause := [(222,true),(223,true),(224,true),(225,false),(226,true),(247,true)]
theorem inp_8648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8648 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 20) (closed_mem 3 20) cl_8648 (by decide) v hb
def cl_8649 : CNF.NClause := [(222,true),(223,true),(224,false),(225,true),(226,true),(247,true)]
theorem inp_8649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8649 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 20) (closed_mem 3 20) cl_8649 (by decide) v hb
end Percolation.NReplay
