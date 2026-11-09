import NInputs099
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_5768 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(72,false),(79,false),(86,false),(89,false)]
theorem inp_5768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5768 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5768 (by decide) v hb
def cl_5769 : CNF.NClause := [(45,false),(14,false),(63,false),(70,false),(72,true),(79,false),(86,false),(89,false)]
theorem inp_5769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5769 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5769 (by decide) v hb
def cl_5770 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,true),(79,false),(86,false),(89,false)]
theorem inp_5770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5770 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5770 (by decide) v hb
def cl_5771 : CNF.NClause := [(45,false),(14,false),(63,true),(70,false),(72,true),(79,false),(86,false),(89,false)]
theorem inp_5771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5771 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5771 (by decide) v hb
def cl_5772 : CNF.NClause := [(45,false),(14,true),(63,true),(70,false),(72,true),(79,false),(86,false),(89,false)]
theorem inp_5772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5772 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5772 (by decide) v hb
def cl_5773 : CNF.NClause := [(45,false),(14,false),(63,false),(70,true),(72,true),(79,false),(86,false),(89,false)]
theorem inp_5773 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5773 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5773 (by decide) v hb
def cl_5774 : CNF.NClause := [(45,false),(14,true),(63,false),(70,true),(72,true),(79,false),(86,false),(89,false)]
theorem inp_5774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5774 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5774 (by decide) v hb
def cl_5775 : CNF.NClause := [(45,false),(14,false),(63,true),(70,true),(72,true),(79,false),(86,false),(89,false)]
theorem inp_5775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5775 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5775 (by decide) v hb
def cl_5776 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(72,true),(79,false),(86,false),(89,false)]
theorem inp_5776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5776 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5776 (by decide) v hb
def cl_5777 : CNF.NClause := [(45,false),(14,false),(63,false),(70,false),(72,false),(79,true),(86,false),(89,false)]
theorem inp_5777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5777 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5777 (by decide) v hb
def cl_5778 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,false),(79,true),(86,false),(89,false)]
theorem inp_5778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5778 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5778 (by decide) v hb
def cl_5779 : CNF.NClause := [(45,false),(14,false),(63,true),(70,false),(72,false),(79,true),(86,false),(89,false)]
theorem inp_5779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5779 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5779 (by decide) v hb
def cl_5780 : CNF.NClause := [(45,false),(14,true),(63,true),(70,false),(72,false),(79,true),(86,false),(89,false)]
theorem inp_5780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5780 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5780 (by decide) v hb
def cl_5781 : CNF.NClause := [(45,false),(14,false),(63,false),(70,true),(72,false),(79,true),(86,false),(89,false)]
theorem inp_5781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5781 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5781 (by decide) v hb
def cl_5782 : CNF.NClause := [(45,false),(14,true),(63,false),(70,true),(72,false),(79,true),(86,false),(89,false)]
theorem inp_5782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5782 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5782 (by decide) v hb
def cl_5783 : CNF.NClause := [(45,false),(14,false),(63,true),(70,true),(72,false),(79,true),(86,false),(89,false)]
theorem inp_5783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5783 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5783 (by decide) v hb
def cl_5784 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(72,false),(79,true),(86,false),(89,false)]
theorem inp_5784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5784 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5784 (by decide) v hb
def cl_5785 : CNF.NClause := [(45,false),(14,false),(63,false),(70,false),(72,true),(79,true),(86,false),(89,false)]
theorem inp_5785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5785 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5785 (by decide) v hb
def cl_5786 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,true),(79,true),(86,false),(89,false)]
theorem inp_5786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5786 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5786 (by decide) v hb
def cl_5787 : CNF.NClause := [(45,false),(14,false),(63,true),(70,false),(72,true),(79,true),(86,false),(89,false)]
theorem inp_5787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5787 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5787 (by decide) v hb
def cl_5788 : CNF.NClause := [(45,false),(14,true),(63,true),(70,false),(72,true),(79,true),(86,false),(89,false)]
theorem inp_5788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5788 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5788 (by decide) v hb
def cl_5789 : CNF.NClause := [(45,false),(14,false),(63,false),(70,true),(72,true),(79,true),(86,false),(89,false)]
theorem inp_5789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5789 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5789 (by decide) v hb
def cl_5790 : CNF.NClause := [(45,false),(14,true),(63,false),(70,true),(72,true),(79,true),(86,false),(89,false)]
theorem inp_5790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5790 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5790 (by decide) v hb
def cl_5791 : CNF.NClause := [(45,false),(14,false),(63,true),(70,true),(72,true),(79,true),(86,false),(89,false)]
theorem inp_5791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5791 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5791 (by decide) v hb
def cl_5792 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(72,true),(79,true),(86,false),(89,false)]
theorem inp_5792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5792 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5792 (by decide) v hb
def cl_5793 : CNF.NClause := [(45,false),(14,false),(63,false),(70,false),(72,false),(79,false),(86,true),(89,false)]
theorem inp_5793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5793 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5793 (by decide) v hb
def cl_5794 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,false),(79,false),(86,true),(89,false)]
theorem inp_5794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5794 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5794 (by decide) v hb
def cl_5795 : CNF.NClause := [(45,false),(14,false),(63,true),(70,false),(72,false),(79,false),(86,true),(89,false)]
theorem inp_5795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5795 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5795 (by decide) v hb
def cl_5796 : CNF.NClause := [(45,false),(14,true),(63,true),(70,false),(72,false),(79,false),(86,true),(89,false)]
theorem inp_5796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5796 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5796 (by decide) v hb
def cl_5797 : CNF.NClause := [(45,false),(14,false),(63,false),(70,true),(72,false),(79,false),(86,true),(89,false)]
theorem inp_5797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5797 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5797 (by decide) v hb
def cl_5798 : CNF.NClause := [(45,false),(14,true),(63,false),(70,true),(72,false),(79,false),(86,true),(89,false)]
theorem inp_5798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5798 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5798 (by decide) v hb
def cl_5799 : CNF.NClause := [(45,false),(14,false),(63,true),(70,true),(72,false),(79,false),(86,true),(89,false)]
theorem inp_5799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5799 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5799 (by decide) v hb
def cl_5800 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(72,false),(79,false),(86,true),(89,false)]
theorem inp_5800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5800 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5800 (by decide) v hb
def cl_5801 : CNF.NClause := [(45,false),(14,false),(63,false),(70,false),(72,true),(79,false),(86,true),(89,false)]
theorem inp_5801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5801 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5801 (by decide) v hb
def cl_5802 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,true),(79,false),(86,true),(89,false)]
theorem inp_5802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5802 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5802 (by decide) v hb
def cl_5803 : CNF.NClause := [(45,false),(14,false),(63,true),(70,false),(72,true),(79,false),(86,true),(89,false)]
theorem inp_5803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5803 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5803 (by decide) v hb
def cl_5804 : CNF.NClause := [(45,false),(14,true),(63,true),(70,false),(72,true),(79,false),(86,true),(89,false)]
theorem inp_5804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5804 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5804 (by decide) v hb
def cl_5805 : CNF.NClause := [(45,false),(14,false),(63,false),(70,true),(72,true),(79,false),(86,true),(89,false)]
theorem inp_5805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5805 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5805 (by decide) v hb
def cl_5806 : CNF.NClause := [(45,false),(14,true),(63,false),(70,true),(72,true),(79,false),(86,true),(89,false)]
theorem inp_5806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5806 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5806 (by decide) v hb
def cl_5807 : CNF.NClause := [(45,false),(14,false),(63,true),(70,true),(72,true),(79,false),(86,true),(89,false)]
theorem inp_5807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5807 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5807 (by decide) v hb
def cl_5808 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(72,true),(79,false),(86,true),(89,false)]
theorem inp_5808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5808 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5808 (by decide) v hb
def cl_5809 : CNF.NClause := [(45,false),(14,false),(63,false),(70,false),(72,false),(79,true),(86,true),(89,false)]
theorem inp_5809 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5809 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5809 (by decide) v hb
def cl_5810 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,false),(79,true),(86,true),(89,false)]
theorem inp_5810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5810 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5810 (by decide) v hb
def cl_5811 : CNF.NClause := [(45,false),(14,false),(63,true),(70,false),(72,false),(79,true),(86,true),(89,false)]
theorem inp_5811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5811 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5811 (by decide) v hb
def cl_5812 : CNF.NClause := [(45,false),(14,true),(63,true),(70,false),(72,false),(79,true),(86,true),(89,false)]
theorem inp_5812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5812 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5812 (by decide) v hb
def cl_5813 : CNF.NClause := [(45,false),(14,false),(63,false),(70,true),(72,false),(79,true),(86,true),(89,false)]
theorem inp_5813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5813 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5813 (by decide) v hb
def cl_5814 : CNF.NClause := [(45,false),(14,true),(63,false),(70,true),(72,false),(79,true),(86,true),(89,false)]
theorem inp_5814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5814 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5814 (by decide) v hb
def cl_5815 : CNF.NClause := [(45,false),(14,false),(63,true),(70,true),(72,false),(79,true),(86,true),(89,false)]
theorem inp_5815 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5815 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5815 (by decide) v hb
def cl_5816 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(72,false),(79,true),(86,true),(89,false)]
theorem inp_5816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5816 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5816 (by decide) v hb
def cl_5817 : CNF.NClause := [(45,false),(14,false),(63,false),(70,false),(72,true),(79,true),(86,true),(89,false)]
theorem inp_5817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5817 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5817 (by decide) v hb
end Percolation.NReplay
