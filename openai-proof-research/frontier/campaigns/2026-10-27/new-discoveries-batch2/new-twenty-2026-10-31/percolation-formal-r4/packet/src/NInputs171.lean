import NInputs170
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_10597 : CNF.NClause := [(559,true),(564,true),(569,true),(574,true),(579,false),(583,true)]
theorem inp_10597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10597 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 4) (closed_mem 14 4) cl_10597 (by decide) v hb
def cl_10598 : CNF.NClause := [(559,true),(564,true),(569,true),(574,false),(579,true),(583,true)]
theorem inp_10598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10598 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 4) (closed_mem 14 4) cl_10598 (by decide) v hb
def cl_10599 : CNF.NClause := [(559,true),(564,true),(569,false),(574,true),(579,true),(583,true)]
theorem inp_10599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10599 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 4) (closed_mem 14 4) cl_10599 (by decide) v hb
def cl_10600 : CNF.NClause := [(559,true),(564,false),(569,true),(574,true),(579,true),(583,true)]
theorem inp_10600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10600 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 4) (closed_mem 14 4) cl_10600 (by decide) v hb
def cl_10601 : CNF.NClause := [(559,false),(564,true),(569,true),(574,true),(579,true),(583,true)]
theorem inp_10601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10601 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 4) (closed_mem 14 4) cl_10601 (by decide) v hb
def cl_10603 : CNF.NClause := [(578,true),(579,true),(580,true),(581,true),(582,false),(588,true)]
theorem inp_10603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10603 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 5) (closed_mem 14 5) cl_10603 (by decide) v hb
def cl_10604 : CNF.NClause := [(578,true),(579,true),(580,true),(581,false),(582,true),(588,true)]
theorem inp_10604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10604 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 5) (closed_mem 14 5) cl_10604 (by decide) v hb
def cl_10605 : CNF.NClause := [(578,true),(579,true),(580,false),(581,true),(582,true),(588,true)]
theorem inp_10605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10605 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 5) (closed_mem 14 5) cl_10605 (by decide) v hb
def cl_10606 : CNF.NClause := [(578,true),(579,false),(580,true),(581,true),(582,true),(588,true)]
theorem inp_10606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10606 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 5) (closed_mem 14 5) cl_10606 (by decide) v hb
def cl_10607 : CNF.NClause := [(578,false),(579,true),(580,true),(581,true),(582,true),(588,true)]
theorem inp_10607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10607 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 5) (closed_mem 14 5) cl_10607 (by decide) v hb
def cl_10608 : CNF.NClause := [(562,true),(566,true),(570,true),(574,true),(578,true),(587,false)]
theorem inp_10608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10608 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 6) (closed_mem 14 6) cl_10608 (by decide) v hb
def cl_10609 : CNF.NClause := [(562,true),(566,true),(570,true),(574,true),(578,false),(587,true)]
theorem inp_10609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10609 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 6) (closed_mem 14 6) cl_10609 (by decide) v hb
def cl_10611 : CNF.NClause := [(562,true),(566,true),(570,false),(574,true),(578,true),(587,true)]
theorem inp_10611 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10611 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 6) (closed_mem 14 6) cl_10611 (by decide) v hb
def cl_10612 : CNF.NClause := [(562,true),(566,false),(570,true),(574,true),(578,true),(587,true)]
theorem inp_10612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10612 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 6) (closed_mem 14 6) cl_10612 (by decide) v hb
def cl_10613 : CNF.NClause := [(562,false),(566,true),(570,true),(574,true),(578,true),(587,true)]
theorem inp_10613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10613 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 6) (closed_mem 14 6) cl_10613 (by decide) v hb
def cl_10614 : CNF.NClause := [(560,true),(567,true),(569,true),(576,true),(578,true),(585,false)]
theorem inp_10614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10614 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 7) (closed_mem 14 7) cl_10614 (by decide) v hb
def cl_10615 : CNF.NClause := [(560,true),(567,true),(569,true),(576,true),(578,false),(585,true)]
theorem inp_10615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10615 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 7) (closed_mem 14 7) cl_10615 (by decide) v hb
def cl_10616 : CNF.NClause := [(560,true),(567,true),(569,true),(576,false),(578,true),(585,true)]
theorem inp_10616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10616 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 7) (closed_mem 14 7) cl_10616 (by decide) v hb
def cl_10617 : CNF.NClause := [(560,true),(567,true),(569,false),(576,true),(578,true),(585,true)]
theorem inp_10617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10617 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 7) (closed_mem 14 7) cl_10617 (by decide) v hb
def cl_10618 : CNF.NClause := [(560,true),(567,false),(569,true),(576,true),(578,true),(585,true)]
theorem inp_10618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10618 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 7) (closed_mem 14 7) cl_10618 (by decide) v hb
def cl_10619 : CNF.NClause := [(560,false),(567,true),(569,true),(576,true),(578,true),(585,true)]
theorem inp_10619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10619 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 7) (closed_mem 14 7) cl_10619 (by decide) v hb
def cl_10623 : CNF.NClause := [(561,true),(564,true),(572,false),(575,true),(578,true),(586,true)]
theorem inp_10623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10623 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 8) (closed_mem 14 8) cl_10623 (by decide) v hb
def cl_10626 : CNF.NClause := [(559,true),(565,true),(571,true),(577,true),(578,true),(584,false)]
theorem inp_10626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10626 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 9) (closed_mem 14 9) cl_10626 (by decide) v hb
def cl_10627 : CNF.NClause := [(559,true),(565,true),(571,true),(577,true),(578,false),(584,true)]
theorem inp_10627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10627 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 9) (closed_mem 14 9) cl_10627 (by decide) v hb
def cl_10629 : CNF.NClause := [(559,true),(565,true),(571,false),(577,true),(578,true),(584,true)]
theorem inp_10629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10629 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 9) (closed_mem 14 9) cl_10629 (by decide) v hb
def cl_10631 : CNF.NClause := [(559,false),(565,true),(571,true),(577,true),(578,true),(584,true)]
theorem inp_10631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10631 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 9) (closed_mem 14 9) cl_10631 (by decide) v hb
def cl_10633 : CNF.NClause := [(568,true),(569,true),(570,true),(571,true),(572,false),(588,true)]
theorem inp_10633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10633 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 10) (closed_mem 14 10) cl_10633 (by decide) v hb
def cl_10638 : CNF.NClause := [(562,true),(565,true),(568,true),(576,true),(579,true),(586,false)]
theorem inp_10638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10638 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 11) (closed_mem 14 11) cl_10638 (by decide) v hb
def cl_10640 : CNF.NClause := [(562,true),(565,true),(568,true),(576,false),(579,true),(586,true)]
theorem inp_10640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10640 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 11) (closed_mem 14 11) cl_10640 (by decide) v hb
def cl_10641 : CNF.NClause := [(562,true),(565,true),(568,false),(576,true),(579,true),(586,true)]
theorem inp_10641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10641 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 11) (closed_mem 14 11) cl_10641 (by decide) v hb
def cl_10643 : CNF.NClause := [(562,false),(565,true),(568,true),(576,true),(579,true),(586,true)]
theorem inp_10643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10643 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 11) (closed_mem 14 11) cl_10643 (by decide) v hb
def cl_10645 : CNF.NClause := [(560,true),(564,true),(568,true),(577,true),(581,false),(587,true)]
theorem inp_10645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10645 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 12) (closed_mem 14 12) cl_10645 (by decide) v hb
def cl_10647 : CNF.NClause := [(560,true),(564,true),(568,false),(577,true),(581,true),(587,true)]
theorem inp_10647 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10647 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 12) (closed_mem 14 12) cl_10647 (by decide) v hb
def cl_10649 : CNF.NClause := [(560,false),(564,true),(568,true),(577,true),(581,true),(587,true)]
theorem inp_10649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10649 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 12) (closed_mem 14 12) cl_10649 (by decide) v hb
def cl_10652 : CNF.NClause := [(561,true),(567,true),(568,true),(574,false),(580,true),(584,true)]
theorem inp_10652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10652 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 13) (closed_mem 14 13) cl_10652 (by decide) v hb
def cl_10653 : CNF.NClause := [(561,true),(567,true),(568,false),(574,true),(580,true),(584,true)]
theorem inp_10653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10653 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 13) (closed_mem 14 13) cl_10653 (by decide) v hb
def cl_10655 : CNF.NClause := [(561,false),(567,true),(568,true),(574,true),(580,true),(584,true)]
theorem inp_10655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10655 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 13) (closed_mem 14 13) cl_10655 (by decide) v hb
def cl_10656 : CNF.NClause := [(559,true),(566,true),(568,true),(575,true),(582,true),(585,false)]
theorem inp_10656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10656 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 14) (closed_mem 14 14) cl_10656 (by decide) v hb
def cl_10657 : CNF.NClause := [(559,true),(566,true),(568,true),(575,true),(582,false),(585,true)]
theorem inp_10657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10657 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 14) (closed_mem 14 14) cl_10657 (by decide) v hb
def cl_10658 : CNF.NClause := [(559,true),(566,true),(568,true),(575,false),(582,true),(585,true)]
theorem inp_10658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10658 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 14) (closed_mem 14 14) cl_10658 (by decide) v hb
def cl_10659 : CNF.NClause := [(559,true),(566,true),(568,false),(575,true),(582,true),(585,true)]
theorem inp_10659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10659 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 14) (closed_mem 14 14) cl_10659 (by decide) v hb
def cl_10661 : CNF.NClause := [(559,false),(566,true),(568,true),(575,true),(582,true),(585,true)]
theorem inp_10661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10661 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 14) (closed_mem 14 14) cl_10661 (by decide) v hb
def cl_10663 : CNF.NClause := [(573,true),(574,true),(575,true),(576,true),(577,false),(588,true)]
theorem inp_10663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10663 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 15) (closed_mem 14 15) cl_10663 (by decide) v hb
def cl_10664 : CNF.NClause := [(573,true),(574,true),(575,true),(576,false),(577,true),(588,true)]
theorem inp_10664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10664 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 15) (closed_mem 14 15) cl_10664 (by decide) v hb
def cl_10665 : CNF.NClause := [(573,true),(574,true),(575,false),(576,true),(577,true),(588,true)]
theorem inp_10665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10665 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 15) (closed_mem 14 15) cl_10665 (by decide) v hb
def cl_10666 : CNF.NClause := [(573,true),(574,false),(575,true),(576,true),(577,true),(588,true)]
theorem inp_10666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10666 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 15) (closed_mem 14 15) cl_10666 (by decide) v hb
def cl_10667 : CNF.NClause := [(573,false),(574,true),(575,true),(576,true),(577,true),(588,true)]
theorem inp_10667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10667 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 15) (closed_mem 14 15) cl_10667 (by decide) v hb
def cl_10668 : CNF.NClause := [(562,true),(564,true),(571,true),(573,true),(580,true),(585,false)]
theorem inp_10668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10668 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 16) (closed_mem 14 16) cl_10668 (by decide) v hb
def cl_10669 : CNF.NClause := [(562,true),(564,true),(571,true),(573,true),(580,false),(585,true)]
theorem inp_10669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10669 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 16) (closed_mem 14 16) cl_10669 (by decide) v hb
def cl_10670 : CNF.NClause := [(562,true),(564,true),(571,true),(573,false),(580,true),(585,true)]
theorem inp_10670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10670 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 16) (closed_mem 14 16) cl_10670 (by decide) v hb
end Percolation.NReplay
