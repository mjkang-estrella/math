import NInputs098
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_5716 : CNF.NClause := [(44,false),(13,true),(65,true),(71,false),(72,false),(78,true),(84,false),(88,true)]
theorem inp_5716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5716 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5716 (by decide) v hb
def cl_5717 : CNF.NClause := [(44,false),(13,false),(65,false),(71,true),(72,false),(78,true),(84,false),(88,true)]
theorem inp_5717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5717 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5717 (by decide) v hb
def cl_5718 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,false),(78,true),(84,false),(88,true)]
theorem inp_5718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5718 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5718 (by decide) v hb
def cl_5719 : CNF.NClause := [(44,false),(13,false),(65,true),(71,true),(72,false),(78,true),(84,false),(88,true)]
theorem inp_5719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5719 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5719 (by decide) v hb
def cl_5720 : CNF.NClause := [(44,false),(13,true),(65,true),(71,true),(72,false),(78,true),(84,false),(88,true)]
theorem inp_5720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5720 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5720 (by decide) v hb
def cl_5721 : CNF.NClause := [(44,false),(13,false),(65,false),(71,false),(72,true),(78,true),(84,false),(88,true)]
theorem inp_5721 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5721 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5721 (by decide) v hb
def cl_5722 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,true),(78,true),(84,false),(88,true)]
theorem inp_5722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5722 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5722 (by decide) v hb
def cl_5723 : CNF.NClause := [(44,false),(13,false),(65,true),(71,false),(72,true),(78,true),(84,false),(88,true)]
theorem inp_5723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5723 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5723 (by decide) v hb
def cl_5724 : CNF.NClause := [(44,false),(13,true),(65,true),(71,false),(72,true),(78,true),(84,false),(88,true)]
theorem inp_5724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5724 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5724 (by decide) v hb
def cl_5725 : CNF.NClause := [(44,false),(13,false),(65,false),(71,true),(72,true),(78,true),(84,false),(88,true)]
theorem inp_5725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5725 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5725 (by decide) v hb
def cl_5726 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,true),(78,true),(84,false),(88,true)]
theorem inp_5726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5726 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5726 (by decide) v hb
def cl_5727 : CNF.NClause := [(44,false),(13,false),(65,true),(71,true),(72,true),(78,true),(84,false),(88,true)]
theorem inp_5727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5727 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5727 (by decide) v hb
def cl_5728 : CNF.NClause := [(44,false),(13,true),(65,true),(71,true),(72,true),(78,true),(84,false),(88,true)]
theorem inp_5728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5728 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5728 (by decide) v hb
def cl_5729 : CNF.NClause := [(44,false),(13,false),(65,false),(71,false),(72,false),(78,false),(84,true),(88,true)]
theorem inp_5729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5729 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5729 (by decide) v hb
def cl_5730 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,false),(78,false),(84,true),(88,true)]
theorem inp_5730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5730 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5730 (by decide) v hb
def cl_5731 : CNF.NClause := [(44,false),(13,false),(65,true),(71,false),(72,false),(78,false),(84,true),(88,true)]
theorem inp_5731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5731 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5731 (by decide) v hb
def cl_5732 : CNF.NClause := [(44,false),(13,true),(65,true),(71,false),(72,false),(78,false),(84,true),(88,true)]
theorem inp_5732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5732 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5732 (by decide) v hb
def cl_5733 : CNF.NClause := [(44,false),(13,false),(65,false),(71,true),(72,false),(78,false),(84,true),(88,true)]
theorem inp_5733 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5733 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5733 (by decide) v hb
def cl_5734 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,false),(78,false),(84,true),(88,true)]
theorem inp_5734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5734 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5734 (by decide) v hb
def cl_5736 : CNF.NClause := [(44,false),(13,true),(65,true),(71,true),(72,false),(78,false),(84,true),(88,true)]
theorem inp_5736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5736 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5736 (by decide) v hb
def cl_5737 : CNF.NClause := [(44,false),(13,false),(65,false),(71,false),(72,true),(78,false),(84,true),(88,true)]
theorem inp_5737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5737 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5737 (by decide) v hb
def cl_5738 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,true),(78,false),(84,true),(88,true)]
theorem inp_5738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5738 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5738 (by decide) v hb
def cl_5739 : CNF.NClause := [(44,false),(13,false),(65,true),(71,false),(72,true),(78,false),(84,true),(88,true)]
theorem inp_5739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5739 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5739 (by decide) v hb
def cl_5740 : CNF.NClause := [(44,false),(13,true),(65,true),(71,false),(72,true),(78,false),(84,true),(88,true)]
theorem inp_5740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5740 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5740 (by decide) v hb
def cl_5741 : CNF.NClause := [(44,false),(13,false),(65,false),(71,true),(72,true),(78,false),(84,true),(88,true)]
theorem inp_5741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5741 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5741 (by decide) v hb
def cl_5742 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,true),(78,false),(84,true),(88,true)]
theorem inp_5742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5742 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5742 (by decide) v hb
def cl_5743 : CNF.NClause := [(44,false),(13,false),(65,true),(71,true),(72,true),(78,false),(84,true),(88,true)]
theorem inp_5743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5743 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5743 (by decide) v hb
def cl_5744 : CNF.NClause := [(44,false),(13,true),(65,true),(71,true),(72,true),(78,false),(84,true),(88,true)]
theorem inp_5744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5744 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5744 (by decide) v hb
def cl_5745 : CNF.NClause := [(44,false),(13,false),(65,false),(71,false),(72,false),(78,true),(84,true),(88,true)]
theorem inp_5745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5745 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5745 (by decide) v hb
def cl_5746 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,false),(78,true),(84,true),(88,true)]
theorem inp_5746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5746 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5746 (by decide) v hb
def cl_5747 : CNF.NClause := [(44,false),(13,false),(65,true),(71,false),(72,false),(78,true),(84,true),(88,true)]
theorem inp_5747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5747 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5747 (by decide) v hb
def cl_5748 : CNF.NClause := [(44,false),(13,true),(65,true),(71,false),(72,false),(78,true),(84,true),(88,true)]
theorem inp_5748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5748 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5748 (by decide) v hb
def cl_5749 : CNF.NClause := [(44,false),(13,false),(65,false),(71,true),(72,false),(78,true),(84,true),(88,true)]
theorem inp_5749 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5749 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5749 (by decide) v hb
def cl_5750 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,false),(78,true),(84,true),(88,true)]
theorem inp_5750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5750 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5750 (by decide) v hb
def cl_5751 : CNF.NClause := [(44,false),(13,false),(65,true),(71,true),(72,false),(78,true),(84,true),(88,true)]
theorem inp_5751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5751 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5751 (by decide) v hb
def cl_5752 : CNF.NClause := [(44,false),(13,true),(65,true),(71,true),(72,false),(78,true),(84,true),(88,true)]
theorem inp_5752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5752 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5752 (by decide) v hb
def cl_5753 : CNF.NClause := [(44,false),(13,false),(65,false),(71,false),(72,true),(78,true),(84,true),(88,true)]
theorem inp_5753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5753 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5753 (by decide) v hb
def cl_5754 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,true),(78,true),(84,true),(88,true)]
theorem inp_5754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5754 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5754 (by decide) v hb
def cl_5756 : CNF.NClause := [(44,false),(13,true),(65,true),(71,false),(72,true),(78,true),(84,true),(88,true)]
theorem inp_5756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5756 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5756 (by decide) v hb
def cl_5757 : CNF.NClause := [(44,false),(13,false),(65,false),(71,true),(72,true),(78,true),(84,true),(88,true)]
theorem inp_5757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5757 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5757 (by decide) v hb
def cl_5758 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,true),(78,true),(84,true),(88,true)]
theorem inp_5758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5758 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5758 (by decide) v hb
def cl_5759 : CNF.NClause := [(44,false),(13,false),(65,true),(71,true),(72,true),(78,true),(84,true),(88,true)]
theorem inp_5759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5759 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5759 (by decide) v hb
def cl_5760 : CNF.NClause := [(44,false),(13,true),(65,true),(71,true),(72,true),(78,true),(84,true),(88,true)]
theorem inp_5760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5760 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5760 (by decide) v hb
def cl_5761 : CNF.NClause := [(45,true),(14,false),(63,false),(70,false),(72,false),(79,false),(86,false),(89,false)]
theorem inp_5761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5761 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5761 (by decide) v hb
def cl_5762 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,false),(79,false),(86,false),(89,false)]
theorem inp_5762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5762 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5762 v hb
def cl_5763 : CNF.NClause := [(45,false),(14,false),(63,true),(70,false),(72,false),(79,false),(86,false),(89,false)]
theorem inp_5763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5763 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5763 (by decide) v hb
def cl_5764 : CNF.NClause := [(45,false),(14,true),(63,true),(70,false),(72,false),(79,false),(86,false),(89,false)]
theorem inp_5764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5764 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5764 (by decide) v hb
def cl_5765 : CNF.NClause := [(45,false),(14,false),(63,false),(70,true),(72,false),(79,false),(86,false),(89,false)]
theorem inp_5765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5765 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5765 (by decide) v hb
def cl_5766 : CNF.NClause := [(45,false),(14,true),(63,false),(70,true),(72,false),(79,false),(86,false),(89,false)]
theorem inp_5766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5766 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5766 (by decide) v hb
def cl_5767 : CNF.NClause := [(45,false),(14,false),(63,true),(70,true),(72,false),(79,false),(86,false),(89,false)]
theorem inp_5767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5767 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5767 (by decide) v hb
end Percolation.NReplay
