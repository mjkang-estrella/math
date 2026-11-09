import NInputs080
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_4786 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,false),(78,true),(82,true),(91,false)]
theorem inp_4786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4786 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4786 (by decide) v hb
def cl_4787 : CNF.NClause := [(37,false),(6,false),(66,true),(70,false),(74,false),(78,true),(82,true),(91,false)]
theorem inp_4787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4787 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4787 (by decide) v hb
def cl_4788 : CNF.NClause := [(37,false),(6,true),(66,true),(70,false),(74,false),(78,true),(82,true),(91,false)]
theorem inp_4788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4788 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4788 (by decide) v hb
def cl_4789 : CNF.NClause := [(37,false),(6,false),(66,false),(70,true),(74,false),(78,true),(82,true),(91,false)]
theorem inp_4789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4789 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4789 (by decide) v hb
def cl_4790 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,false),(78,true),(82,true),(91,false)]
theorem inp_4790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4790 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4790 (by decide) v hb
def cl_4791 : CNF.NClause := [(37,false),(6,false),(66,true),(70,true),(74,false),(78,true),(82,true),(91,false)]
theorem inp_4791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4791 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4791 (by decide) v hb
def cl_4792 : CNF.NClause := [(37,false),(6,true),(66,true),(70,true),(74,false),(78,true),(82,true),(91,false)]
theorem inp_4792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4792 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4792 (by decide) v hb
def cl_4793 : CNF.NClause := [(37,false),(6,false),(66,false),(70,false),(74,true),(78,true),(82,true),(91,false)]
theorem inp_4793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4793 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4793 (by decide) v hb
def cl_4794 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,true),(78,true),(82,true),(91,false)]
theorem inp_4794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4794 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4794 (by decide) v hb
def cl_4795 : CNF.NClause := [(37,false),(6,false),(66,true),(70,false),(74,true),(78,true),(82,true),(91,false)]
theorem inp_4795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4795 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4795 (by decide) v hb
def cl_4796 : CNF.NClause := [(37,false),(6,true),(66,true),(70,false),(74,true),(78,true),(82,true),(91,false)]
theorem inp_4796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4796 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4796 (by decide) v hb
def cl_4797 : CNF.NClause := [(37,false),(6,false),(66,false),(70,true),(74,true),(78,true),(82,true),(91,false)]
theorem inp_4797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4797 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4797 (by decide) v hb
def cl_4798 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,true),(78,true),(82,true),(91,false)]
theorem inp_4798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4798 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4798 (by decide) v hb
def cl_4799 : CNF.NClause := [(37,false),(6,false),(66,true),(70,true),(74,true),(78,true),(82,true),(91,false)]
theorem inp_4799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4799 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4799 (by decide) v hb
def cl_4800 : CNF.NClause := [(37,false),(6,true),(66,true),(70,true),(74,true),(78,true),(82,true),(91,false)]
theorem inp_4800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4800 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4800 (by decide) v hb
def cl_4801 : CNF.NClause := [(37,false),(6,false),(66,false),(70,false),(74,false),(78,false),(82,false),(91,true)]
theorem inp_4801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4801 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4801 (by decide) v hb
def cl_4802 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,false),(78,false),(82,false),(91,true)]
theorem inp_4802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4802 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4802 (by decide) v hb
def cl_4803 : CNF.NClause := [(37,false),(6,false),(66,true),(70,false),(74,false),(78,false),(82,false),(91,true)]
theorem inp_4803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4803 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4803 (by decide) v hb
def cl_4804 : CNF.NClause := [(37,false),(6,true),(66,true),(70,false),(74,false),(78,false),(82,false),(91,true)]
theorem inp_4804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4804 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4804 (by decide) v hb
def cl_4805 : CNF.NClause := [(37,false),(6,false),(66,false),(70,true),(74,false),(78,false),(82,false),(91,true)]
theorem inp_4805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4805 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4805 (by decide) v hb
def cl_4806 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,false),(78,false),(82,false),(91,true)]
theorem inp_4806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4806 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4806 (by decide) v hb
def cl_4807 : CNF.NClause := [(37,false),(6,false),(66,true),(70,true),(74,false),(78,false),(82,false),(91,true)]
theorem inp_4807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4807 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4807 (by decide) v hb
def cl_4808 : CNF.NClause := [(37,false),(6,true),(66,true),(70,true),(74,false),(78,false),(82,false),(91,true)]
theorem inp_4808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4808 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4808 (by decide) v hb
def cl_4809 : CNF.NClause := [(37,false),(6,false),(66,false),(70,false),(74,true),(78,false),(82,false),(91,true)]
theorem inp_4809 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4809 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4809 (by decide) v hb
def cl_4810 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,true),(78,false),(82,false),(91,true)]
theorem inp_4810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4810 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4810 (by decide) v hb
def cl_4811 : CNF.NClause := [(37,false),(6,false),(66,true),(70,false),(74,true),(78,false),(82,false),(91,true)]
theorem inp_4811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4811 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4811 (by decide) v hb
def cl_4812 : CNF.NClause := [(37,false),(6,true),(66,true),(70,false),(74,true),(78,false),(82,false),(91,true)]
theorem inp_4812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4812 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4812 (by decide) v hb
def cl_4814 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,true),(78,false),(82,false),(91,true)]
theorem inp_4814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4814 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4814 (by decide) v hb
def cl_4815 : CNF.NClause := [(37,false),(6,false),(66,true),(70,true),(74,true),(78,false),(82,false),(91,true)]
theorem inp_4815 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4815 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4815 (by decide) v hb
def cl_4816 : CNF.NClause := [(37,false),(6,true),(66,true),(70,true),(74,true),(78,false),(82,false),(91,true)]
theorem inp_4816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4816 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4816 (by decide) v hb
def cl_4817 : CNF.NClause := [(37,false),(6,false),(66,false),(70,false),(74,false),(78,true),(82,false),(91,true)]
theorem inp_4817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4817 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4817 (by decide) v hb
def cl_4818 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,false),(78,true),(82,false),(91,true)]
theorem inp_4818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4818 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4818 (by decide) v hb
def cl_4819 : CNF.NClause := [(37,false),(6,false),(66,true),(70,false),(74,false),(78,true),(82,false),(91,true)]
theorem inp_4819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4819 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4819 (by decide) v hb
def cl_4820 : CNF.NClause := [(37,false),(6,true),(66,true),(70,false),(74,false),(78,true),(82,false),(91,true)]
theorem inp_4820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4820 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4820 (by decide) v hb
def cl_4821 : CNF.NClause := [(37,false),(6,false),(66,false),(70,true),(74,false),(78,true),(82,false),(91,true)]
theorem inp_4821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4821 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4821 (by decide) v hb
def cl_4822 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,false),(78,true),(82,false),(91,true)]
theorem inp_4822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4822 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4822 (by decide) v hb
def cl_4824 : CNF.NClause := [(37,false),(6,true),(66,true),(70,true),(74,false),(78,true),(82,false),(91,true)]
theorem inp_4824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4824 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4824 (by decide) v hb
def cl_4825 : CNF.NClause := [(37,false),(6,false),(66,false),(70,false),(74,true),(78,true),(82,false),(91,true)]
theorem inp_4825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4825 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4825 (by decide) v hb
def cl_4826 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,true),(78,true),(82,false),(91,true)]
theorem inp_4826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4826 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4826 (by decide) v hb
def cl_4827 : CNF.NClause := [(37,false),(6,false),(66,true),(70,false),(74,true),(78,true),(82,false),(91,true)]
theorem inp_4827 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4827 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4827 (by decide) v hb
def cl_4828 : CNF.NClause := [(37,false),(6,true),(66,true),(70,false),(74,true),(78,true),(82,false),(91,true)]
theorem inp_4828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4828 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4828 (by decide) v hb
def cl_4829 : CNF.NClause := [(37,false),(6,false),(66,false),(70,true),(74,true),(78,true),(82,false),(91,true)]
theorem inp_4829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4829 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4829 (by decide) v hb
def cl_4830 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,true),(78,true),(82,false),(91,true)]
theorem inp_4830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4830 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4830 (by decide) v hb
def cl_4832 : CNF.NClause := [(37,false),(6,true),(66,true),(70,true),(74,true),(78,true),(82,false),(91,true)]
theorem inp_4832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4832 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4832 (by decide) v hb
def cl_4833 : CNF.NClause := [(37,false),(6,false),(66,false),(70,false),(74,false),(78,false),(82,true),(91,true)]
theorem inp_4833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4833 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4833 v hb
def cl_4834 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,false),(78,false),(82,true),(91,true)]
theorem inp_4834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4834 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4834 (by decide) v hb
def cl_4835 : CNF.NClause := [(37,false),(6,false),(66,true),(70,false),(74,false),(78,false),(82,true),(91,true)]
theorem inp_4835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4835 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4835 (by decide) v hb
def cl_4836 : CNF.NClause := [(37,false),(6,true),(66,true),(70,false),(74,false),(78,false),(82,true),(91,true)]
theorem inp_4836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4836 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4836 (by decide) v hb
def cl_4837 : CNF.NClause := [(37,false),(6,false),(66,false),(70,true),(74,false),(78,false),(82,true),(91,true)]
theorem inp_4837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4837 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4837 (by decide) v hb
def cl_4838 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,false),(78,false),(82,true),(91,true)]
theorem inp_4838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4838 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4838 (by decide) v hb
end Percolation.NReplay
