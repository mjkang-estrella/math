import NInputs119
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_6805 : CNF.NClause := [(53,false),(22,false),(64,false),(67,true),(75,false),(78,true),(86,false),(90,false)]
theorem inp_6805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6805 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6805 (by decide) v hb
def cl_6806 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,false),(78,true),(86,false),(90,false)]
theorem inp_6806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6806 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6806 v hb
def cl_6807 : CNF.NClause := [(53,false),(22,false),(64,true),(67,true),(75,false),(78,true),(86,false),(90,false)]
theorem inp_6807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6807 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6807 (by decide) v hb
def cl_6808 : CNF.NClause := [(53,false),(22,true),(64,true),(67,true),(75,false),(78,true),(86,false),(90,false)]
theorem inp_6808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6808 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6808 (by decide) v hb
def cl_6809 : CNF.NClause := [(53,false),(22,false),(64,false),(67,false),(75,true),(78,true),(86,false),(90,false)]
theorem inp_6809 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6809 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6809 (by decide) v hb
def cl_6810 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,true),(78,true),(86,false),(90,false)]
theorem inp_6810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6810 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6810 (by decide) v hb
def cl_6811 : CNF.NClause := [(53,false),(22,false),(64,true),(67,false),(75,true),(78,true),(86,false),(90,false)]
theorem inp_6811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6811 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6811 (by decide) v hb
def cl_6812 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(75,true),(78,true),(86,false),(90,false)]
theorem inp_6812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6812 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6812 (by decide) v hb
def cl_6813 : CNF.NClause := [(53,false),(22,false),(64,false),(67,true),(75,true),(78,true),(86,false),(90,false)]
theorem inp_6813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6813 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6813 (by decide) v hb
def cl_6814 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,true),(78,true),(86,false),(90,false)]
theorem inp_6814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6814 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6814 (by decide) v hb
def cl_6815 : CNF.NClause := [(53,false),(22,false),(64,true),(67,true),(75,true),(78,true),(86,false),(90,false)]
theorem inp_6815 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6815 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6815 (by decide) v hb
def cl_6816 : CNF.NClause := [(53,false),(22,true),(64,true),(67,true),(75,true),(78,true),(86,false),(90,false)]
theorem inp_6816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6816 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6816 (by decide) v hb
def cl_6817 : CNF.NClause := [(53,false),(22,false),(64,false),(67,false),(75,false),(78,false),(86,true),(90,false)]
theorem inp_6817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6817 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6817 (by decide) v hb
def cl_6818 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,false),(78,false),(86,true),(90,false)]
theorem inp_6818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6818 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6818 (by decide) v hb
def cl_6819 : CNF.NClause := [(53,false),(22,false),(64,true),(67,false),(75,false),(78,false),(86,true),(90,false)]
theorem inp_6819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6819 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6819 (by decide) v hb
def cl_6820 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(75,false),(78,false),(86,true),(90,false)]
theorem inp_6820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6820 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6820 (by decide) v hb
def cl_6821 : CNF.NClause := [(53,false),(22,false),(64,false),(67,true),(75,false),(78,false),(86,true),(90,false)]
theorem inp_6821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6821 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6821 (by decide) v hb
def cl_6822 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,false),(78,false),(86,true),(90,false)]
theorem inp_6822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6822 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6822 (by decide) v hb
def cl_6823 : CNF.NClause := [(53,false),(22,false),(64,true),(67,true),(75,false),(78,false),(86,true),(90,false)]
theorem inp_6823 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6823 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6823 (by decide) v hb
def cl_6824 : CNF.NClause := [(53,false),(22,true),(64,true),(67,true),(75,false),(78,false),(86,true),(90,false)]
theorem inp_6824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6824 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6824 (by decide) v hb
def cl_6825 : CNF.NClause := [(53,false),(22,false),(64,false),(67,false),(75,true),(78,false),(86,true),(90,false)]
theorem inp_6825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6825 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6825 (by decide) v hb
def cl_6826 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,true),(78,false),(86,true),(90,false)]
theorem inp_6826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6826 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6826 (by decide) v hb
def cl_6827 : CNF.NClause := [(53,false),(22,false),(64,true),(67,false),(75,true),(78,false),(86,true),(90,false)]
theorem inp_6827 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6827 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6827 (by decide) v hb
def cl_6828 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(75,true),(78,false),(86,true),(90,false)]
theorem inp_6828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6828 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6828 (by decide) v hb
def cl_6829 : CNF.NClause := [(53,false),(22,false),(64,false),(67,true),(75,true),(78,false),(86,true),(90,false)]
theorem inp_6829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6829 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6829 (by decide) v hb
def cl_6830 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,true),(78,false),(86,true),(90,false)]
theorem inp_6830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6830 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6830 (by decide) v hb
def cl_6831 : CNF.NClause := [(53,false),(22,false),(64,true),(67,true),(75,true),(78,false),(86,true),(90,false)]
theorem inp_6831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6831 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6831 (by decide) v hb
def cl_6832 : CNF.NClause := [(53,false),(22,true),(64,true),(67,true),(75,true),(78,false),(86,true),(90,false)]
theorem inp_6832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6832 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6832 (by decide) v hb
def cl_6833 : CNF.NClause := [(53,false),(22,false),(64,false),(67,false),(75,false),(78,true),(86,true),(90,false)]
theorem inp_6833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6833 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6833 (by decide) v hb
def cl_6834 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,false),(78,true),(86,true),(90,false)]
theorem inp_6834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6834 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6834 (by decide) v hb
def cl_6835 : CNF.NClause := [(53,false),(22,false),(64,true),(67,false),(75,false),(78,true),(86,true),(90,false)]
theorem inp_6835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6835 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6835 (by decide) v hb
def cl_6836 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(75,false),(78,true),(86,true),(90,false)]
theorem inp_6836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6836 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6836 (by decide) v hb
def cl_6837 : CNF.NClause := [(53,false),(22,false),(64,false),(67,true),(75,false),(78,true),(86,true),(90,false)]
theorem inp_6837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6837 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6837 (by decide) v hb
def cl_6838 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,false),(78,true),(86,true),(90,false)]
theorem inp_6838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6838 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6838 (by decide) v hb
def cl_6839 : CNF.NClause := [(53,false),(22,false),(64,true),(67,true),(75,false),(78,true),(86,true),(90,false)]
theorem inp_6839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6839 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6839 (by decide) v hb
def cl_6840 : CNF.NClause := [(53,false),(22,true),(64,true),(67,true),(75,false),(78,true),(86,true),(90,false)]
theorem inp_6840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6840 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6840 (by decide) v hb
def cl_6841 : CNF.NClause := [(53,false),(22,false),(64,false),(67,false),(75,true),(78,true),(86,true),(90,false)]
theorem inp_6841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6841 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6841 (by decide) v hb
def cl_6842 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,true),(78,true),(86,true),(90,false)]
theorem inp_6842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6842 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6842 (by decide) v hb
def cl_6843 : CNF.NClause := [(53,false),(22,false),(64,true),(67,false),(75,true),(78,true),(86,true),(90,false)]
theorem inp_6843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6843 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6843 (by decide) v hb
def cl_6844 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(75,true),(78,true),(86,true),(90,false)]
theorem inp_6844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6844 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6844 (by decide) v hb
def cl_6845 : CNF.NClause := [(53,false),(22,false),(64,false),(67,true),(75,true),(78,true),(86,true),(90,false)]
theorem inp_6845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6845 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6845 (by decide) v hb
def cl_6846 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,true),(78,true),(86,true),(90,false)]
theorem inp_6846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6846 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6846 (by decide) v hb
def cl_6847 : CNF.NClause := [(53,false),(22,false),(64,true),(67,true),(75,true),(78,true),(86,true),(90,false)]
theorem inp_6847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6847 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6847 (by decide) v hb
def cl_6848 : CNF.NClause := [(53,false),(22,true),(64,true),(67,true),(75,true),(78,true),(86,true),(90,false)]
theorem inp_6848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6848 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6848 (by decide) v hb
def cl_6849 : CNF.NClause := [(53,false),(22,false),(64,false),(67,false),(75,false),(78,false),(86,false),(90,true)]
theorem inp_6849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6849 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6849 (by decide) v hb
def cl_6850 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,false),(78,false),(86,false),(90,true)]
theorem inp_6850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6850 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6850 (by decide) v hb
def cl_6851 : CNF.NClause := [(53,false),(22,false),(64,true),(67,false),(75,false),(78,false),(86,false),(90,true)]
theorem inp_6851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6851 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6851 (by decide) v hb
def cl_6852 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(75,false),(78,false),(86,false),(90,true)]
theorem inp_6852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6852 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6852 (by decide) v hb
def cl_6853 : CNF.NClause := [(53,false),(22,false),(64,false),(67,true),(75,false),(78,false),(86,false),(90,true)]
theorem inp_6853 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6853 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6853 (by decide) v hb
def cl_6854 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,false),(78,false),(86,false),(90,true)]
theorem inp_6854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6854 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6854 (by decide) v hb
end Percolation.NReplay
