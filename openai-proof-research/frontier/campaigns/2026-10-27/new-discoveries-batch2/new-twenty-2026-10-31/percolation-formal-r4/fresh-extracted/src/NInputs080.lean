import NInputs079
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_4736 : CNF.NClause := [(36,false),(5,true),(82,true),(83,true),(84,true),(85,true),(86,true),(92,true)]
theorem inp_4736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4736 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4736 (by decide) v hb
def cl_4737 : CNF.NClause := [(37,true),(6,false),(66,false),(70,false),(74,false),(78,false),(82,false),(91,false)]
theorem inp_4737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4737 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4737 (by decide) v hb
def cl_4738 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,false),(78,false),(82,false),(91,false)]
theorem inp_4738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4738 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4738 (by decide) v hb
def cl_4739 : CNF.NClause := [(37,false),(6,false),(66,true),(70,false),(74,false),(78,false),(82,false),(91,false)]
theorem inp_4739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4739 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4739 (by decide) v hb
def cl_4740 : CNF.NClause := [(37,false),(6,true),(66,true),(70,false),(74,false),(78,false),(82,false),(91,false)]
theorem inp_4740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4740 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4740 (by decide) v hb
def cl_4741 : CNF.NClause := [(37,false),(6,false),(66,false),(70,true),(74,false),(78,false),(82,false),(91,false)]
theorem inp_4741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4741 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4741 (by decide) v hb
def cl_4742 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,false),(78,false),(82,false),(91,false)]
theorem inp_4742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4742 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4742 (by decide) v hb
def cl_4743 : CNF.NClause := [(37,false),(6,false),(66,true),(70,true),(74,false),(78,false),(82,false),(91,false)]
theorem inp_4743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4743 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4743 (by decide) v hb
def cl_4744 : CNF.NClause := [(37,false),(6,true),(66,true),(70,true),(74,false),(78,false),(82,false),(91,false)]
theorem inp_4744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4744 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4744 (by decide) v hb
def cl_4745 : CNF.NClause := [(37,false),(6,false),(66,false),(70,false),(74,true),(78,false),(82,false),(91,false)]
theorem inp_4745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4745 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4745 (by decide) v hb
def cl_4746 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,true),(78,false),(82,false),(91,false)]
theorem inp_4746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4746 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4746 (by decide) v hb
def cl_4747 : CNF.NClause := [(37,false),(6,false),(66,true),(70,false),(74,true),(78,false),(82,false),(91,false)]
theorem inp_4747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4747 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4747 (by decide) v hb
def cl_4748 : CNF.NClause := [(37,false),(6,true),(66,true),(70,false),(74,true),(78,false),(82,false),(91,false)]
theorem inp_4748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4748 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4748 (by decide) v hb
def cl_4749 : CNF.NClause := [(37,false),(6,false),(66,false),(70,true),(74,true),(78,false),(82,false),(91,false)]
theorem inp_4749 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4749 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4749 (by decide) v hb
def cl_4750 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,true),(78,false),(82,false),(91,false)]
theorem inp_4750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4750 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4750 (by decide) v hb
def cl_4751 : CNF.NClause := [(37,false),(6,false),(66,true),(70,true),(74,true),(78,false),(82,false),(91,false)]
theorem inp_4751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4751 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4751 (by decide) v hb
def cl_4752 : CNF.NClause := [(37,false),(6,true),(66,true),(70,true),(74,true),(78,false),(82,false),(91,false)]
theorem inp_4752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4752 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4752 (by decide) v hb
def cl_4753 : CNF.NClause := [(37,false),(6,false),(66,false),(70,false),(74,false),(78,true),(82,false),(91,false)]
theorem inp_4753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4753 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4753 (by decide) v hb
def cl_4754 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,false),(78,true),(82,false),(91,false)]
theorem inp_4754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4754 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4754 (by decide) v hb
def cl_4755 : CNF.NClause := [(37,false),(6,false),(66,true),(70,false),(74,false),(78,true),(82,false),(91,false)]
theorem inp_4755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4755 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4755 (by decide) v hb
def cl_4756 : CNF.NClause := [(37,false),(6,true),(66,true),(70,false),(74,false),(78,true),(82,false),(91,false)]
theorem inp_4756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4756 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4756 (by decide) v hb
def cl_4757 : CNF.NClause := [(37,false),(6,false),(66,false),(70,true),(74,false),(78,true),(82,false),(91,false)]
theorem inp_4757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4757 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4757 (by decide) v hb
def cl_4758 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,false),(78,true),(82,false),(91,false)]
theorem inp_4758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4758 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4758 (by decide) v hb
def cl_4759 : CNF.NClause := [(37,false),(6,false),(66,true),(70,true),(74,false),(78,true),(82,false),(91,false)]
theorem inp_4759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4759 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4759 (by decide) v hb
def cl_4760 : CNF.NClause := [(37,false),(6,true),(66,true),(70,true),(74,false),(78,true),(82,false),(91,false)]
theorem inp_4760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4760 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4760 (by decide) v hb
def cl_4761 : CNF.NClause := [(37,false),(6,false),(66,false),(70,false),(74,true),(78,true),(82,false),(91,false)]
theorem inp_4761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4761 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4761 (by decide) v hb
def cl_4762 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,true),(78,true),(82,false),(91,false)]
theorem inp_4762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4762 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4762 (by decide) v hb
def cl_4763 : CNF.NClause := [(37,false),(6,false),(66,true),(70,false),(74,true),(78,true),(82,false),(91,false)]
theorem inp_4763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4763 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4763 (by decide) v hb
def cl_4764 : CNF.NClause := [(37,false),(6,true),(66,true),(70,false),(74,true),(78,true),(82,false),(91,false)]
theorem inp_4764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4764 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4764 (by decide) v hb
def cl_4765 : CNF.NClause := [(37,false),(6,false),(66,false),(70,true),(74,true),(78,true),(82,false),(91,false)]
theorem inp_4765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4765 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4765 (by decide) v hb
def cl_4766 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,true),(78,true),(82,false),(91,false)]
theorem inp_4766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4766 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4766 (by decide) v hb
def cl_4767 : CNF.NClause := [(37,false),(6,false),(66,true),(70,true),(74,true),(78,true),(82,false),(91,false)]
theorem inp_4767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4767 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4767 (by decide) v hb
def cl_4768 : CNF.NClause := [(37,false),(6,true),(66,true),(70,true),(74,true),(78,true),(82,false),(91,false)]
theorem inp_4768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4768 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4768 (by decide) v hb
def cl_4769 : CNF.NClause := [(37,false),(6,false),(66,false),(70,false),(74,false),(78,false),(82,true),(91,false)]
theorem inp_4769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4769 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4769 v hb
def cl_4770 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,false),(78,false),(82,true),(91,false)]
theorem inp_4770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4770 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4770 (by decide) v hb
def cl_4771 : CNF.NClause := [(37,false),(6,false),(66,true),(70,false),(74,false),(78,false),(82,true),(91,false)]
theorem inp_4771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4771 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4771 (by decide) v hb
def cl_4772 : CNF.NClause := [(37,false),(6,true),(66,true),(70,false),(74,false),(78,false),(82,true),(91,false)]
theorem inp_4772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4772 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4772 (by decide) v hb
def cl_4773 : CNF.NClause := [(37,false),(6,false),(66,false),(70,true),(74,false),(78,false),(82,true),(91,false)]
theorem inp_4773 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4773 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4773 v hb
def cl_4774 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,false),(78,false),(82,true),(91,false)]
theorem inp_4774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4774 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4774 (by decide) v hb
def cl_4775 : CNF.NClause := [(37,false),(6,false),(66,true),(70,true),(74,false),(78,false),(82,true),(91,false)]
theorem inp_4775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4775 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4775 (by decide) v hb
def cl_4776 : CNF.NClause := [(37,false),(6,true),(66,true),(70,true),(74,false),(78,false),(82,true),(91,false)]
theorem inp_4776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4776 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4776 (by decide) v hb
def cl_4777 : CNF.NClause := [(37,false),(6,false),(66,false),(70,false),(74,true),(78,false),(82,true),(91,false)]
theorem inp_4777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4777 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4777 (by decide) v hb
def cl_4778 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,true),(78,false),(82,true),(91,false)]
theorem inp_4778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4778 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4778 v hb
def cl_4779 : CNF.NClause := [(37,false),(6,false),(66,true),(70,false),(74,true),(78,false),(82,true),(91,false)]
theorem inp_4779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4779 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4779 (by decide) v hb
def cl_4780 : CNF.NClause := [(37,false),(6,true),(66,true),(70,false),(74,true),(78,false),(82,true),(91,false)]
theorem inp_4780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4780 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4780 (by decide) v hb
def cl_4781 : CNF.NClause := [(37,false),(6,false),(66,false),(70,true),(74,true),(78,false),(82,true),(91,false)]
theorem inp_4781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4781 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4781 (by decide) v hb
def cl_4782 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,true),(78,false),(82,true),(91,false)]
theorem inp_4782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4782 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4782 v hb
def cl_4783 : CNF.NClause := [(37,false),(6,false),(66,true),(70,true),(74,true),(78,false),(82,true),(91,false)]
theorem inp_4783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4783 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4783 (by decide) v hb
def cl_4784 : CNF.NClause := [(37,false),(6,true),(66,true),(70,true),(74,true),(78,false),(82,true),(91,false)]
theorem inp_4784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4784 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4784 (by decide) v hb
def cl_4785 : CNF.NClause := [(37,false),(6,false),(66,false),(70,false),(74,false),(78,true),(82,true),(91,false)]
theorem inp_4785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4785 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4785 (by decide) v hb
end Percolation.NReplay
