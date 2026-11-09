import NInputs100
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_5818 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,true),(79,true),(86,true),(89,false)]
theorem inp_5818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5818 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5818 (by decide) v hb
def cl_5819 : CNF.NClause := [(45,false),(14,false),(63,true),(70,false),(72,true),(79,true),(86,true),(89,false)]
theorem inp_5819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5819 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5819 (by decide) v hb
def cl_5820 : CNF.NClause := [(45,false),(14,true),(63,true),(70,false),(72,true),(79,true),(86,true),(89,false)]
theorem inp_5820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5820 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5820 (by decide) v hb
def cl_5821 : CNF.NClause := [(45,false),(14,false),(63,false),(70,true),(72,true),(79,true),(86,true),(89,false)]
theorem inp_5821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5821 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5821 (by decide) v hb
def cl_5822 : CNF.NClause := [(45,false),(14,true),(63,false),(70,true),(72,true),(79,true),(86,true),(89,false)]
theorem inp_5822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5822 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5822 (by decide) v hb
def cl_5823 : CNF.NClause := [(45,false),(14,false),(63,true),(70,true),(72,true),(79,true),(86,true),(89,false)]
theorem inp_5823 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5823 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5823 (by decide) v hb
def cl_5824 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(72,true),(79,true),(86,true),(89,false)]
theorem inp_5824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5824 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5824 (by decide) v hb
def cl_5825 : CNF.NClause := [(45,false),(14,false),(63,false),(70,false),(72,false),(79,false),(86,false),(89,true)]
theorem inp_5825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5825 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5825 v hb
def cl_5826 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,false),(79,false),(86,false),(89,true)]
theorem inp_5826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5826 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5826 v hb
def cl_5827 : CNF.NClause := [(45,false),(14,false),(63,true),(70,false),(72,false),(79,false),(86,false),(89,true)]
theorem inp_5827 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5827 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5827 v hb
def cl_5828 : CNF.NClause := [(45,false),(14,true),(63,true),(70,false),(72,false),(79,false),(86,false),(89,true)]
theorem inp_5828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5828 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5828 (by decide) v hb
def cl_5829 : CNF.NClause := [(45,false),(14,false),(63,false),(70,true),(72,false),(79,false),(86,false),(89,true)]
theorem inp_5829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5829 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5829 (by decide) v hb
def cl_5830 : CNF.NClause := [(45,false),(14,true),(63,false),(70,true),(72,false),(79,false),(86,false),(89,true)]
theorem inp_5830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5830 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5830 (by decide) v hb
def cl_5831 : CNF.NClause := [(45,false),(14,false),(63,true),(70,true),(72,false),(79,false),(86,false),(89,true)]
theorem inp_5831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5831 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5831 (by decide) v hb
def cl_5832 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(72,false),(79,false),(86,false),(89,true)]
theorem inp_5832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5832 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5832 (by decide) v hb
def cl_5833 : CNF.NClause := [(45,false),(14,false),(63,false),(70,false),(72,true),(79,false),(86,false),(89,true)]
theorem inp_5833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5833 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5833 (by decide) v hb
def cl_5834 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,true),(79,false),(86,false),(89,true)]
theorem inp_5834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5834 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5834 (by decide) v hb
def cl_5835 : CNF.NClause := [(45,false),(14,false),(63,true),(70,false),(72,true),(79,false),(86,false),(89,true)]
theorem inp_5835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5835 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5835 (by decide) v hb
def cl_5836 : CNF.NClause := [(45,false),(14,true),(63,true),(70,false),(72,true),(79,false),(86,false),(89,true)]
theorem inp_5836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5836 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5836 (by decide) v hb
def cl_5837 : CNF.NClause := [(45,false),(14,false),(63,false),(70,true),(72,true),(79,false),(86,false),(89,true)]
theorem inp_5837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5837 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5837 (by decide) v hb
def cl_5838 : CNF.NClause := [(45,false),(14,true),(63,false),(70,true),(72,true),(79,false),(86,false),(89,true)]
theorem inp_5838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5838 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5838 (by decide) v hb
def cl_5839 : CNF.NClause := [(45,false),(14,false),(63,true),(70,true),(72,true),(79,false),(86,false),(89,true)]
theorem inp_5839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5839 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5839 (by decide) v hb
def cl_5840 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(72,true),(79,false),(86,false),(89,true)]
theorem inp_5840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5840 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5840 (by decide) v hb
def cl_5841 : CNF.NClause := [(45,false),(14,false),(63,false),(70,false),(72,false),(79,true),(86,false),(89,true)]
theorem inp_5841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5841 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5841 (by decide) v hb
def cl_5842 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,false),(79,true),(86,false),(89,true)]
theorem inp_5842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5842 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5842 v hb
def cl_5843 : CNF.NClause := [(45,false),(14,false),(63,true),(70,false),(72,false),(79,true),(86,false),(89,true)]
theorem inp_5843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5843 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5843 (by decide) v hb
def cl_5844 : CNF.NClause := [(45,false),(14,true),(63,true),(70,false),(72,false),(79,true),(86,false),(89,true)]
theorem inp_5844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5844 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5844 v hb
def cl_5845 : CNF.NClause := [(45,false),(14,false),(63,false),(70,true),(72,false),(79,true),(86,false),(89,true)]
theorem inp_5845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5845 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5845 (by decide) v hb
def cl_5846 : CNF.NClause := [(45,false),(14,true),(63,false),(70,true),(72,false),(79,true),(86,false),(89,true)]
theorem inp_5846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5846 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5846 (by decide) v hb
def cl_5847 : CNF.NClause := [(45,false),(14,false),(63,true),(70,true),(72,false),(79,true),(86,false),(89,true)]
theorem inp_5847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5847 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5847 (by decide) v hb
def cl_5848 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(72,false),(79,true),(86,false),(89,true)]
theorem inp_5848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5848 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5848 (by decide) v hb
def cl_5849 : CNF.NClause := [(45,false),(14,false),(63,false),(70,false),(72,true),(79,true),(86,false),(89,true)]
theorem inp_5849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5849 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5849 (by decide) v hb
def cl_5850 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,true),(79,true),(86,false),(89,true)]
theorem inp_5850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5850 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5850 (by decide) v hb
def cl_5852 : CNF.NClause := [(45,false),(14,true),(63,true),(70,false),(72,true),(79,true),(86,false),(89,true)]
theorem inp_5852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5852 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5852 (by decide) v hb
def cl_5853 : CNF.NClause := [(45,false),(14,false),(63,false),(70,true),(72,true),(79,true),(86,false),(89,true)]
theorem inp_5853 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5853 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5853 (by decide) v hb
def cl_5854 : CNF.NClause := [(45,false),(14,true),(63,false),(70,true),(72,true),(79,true),(86,false),(89,true)]
theorem inp_5854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5854 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5854 (by decide) v hb
def cl_5856 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(72,true),(79,true),(86,false),(89,true)]
theorem inp_5856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5856 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5856 (by decide) v hb
def cl_5857 : CNF.NClause := [(45,false),(14,false),(63,false),(70,false),(72,false),(79,false),(86,true),(89,true)]
theorem inp_5857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5857 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5857 (by decide) v hb
def cl_5858 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,false),(79,false),(86,true),(89,true)]
theorem inp_5858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5858 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5858 (by decide) v hb
def cl_5859 : CNF.NClause := [(45,false),(14,false),(63,true),(70,false),(72,false),(79,false),(86,true),(89,true)]
theorem inp_5859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5859 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5859 (by decide) v hb
def cl_5860 : CNF.NClause := [(45,false),(14,true),(63,true),(70,false),(72,false),(79,false),(86,true),(89,true)]
theorem inp_5860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5860 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5860 (by decide) v hb
def cl_5861 : CNF.NClause := [(45,false),(14,false),(63,false),(70,true),(72,false),(79,false),(86,true),(89,true)]
theorem inp_5861 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5861 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5861 (by decide) v hb
def cl_5862 : CNF.NClause := [(45,false),(14,true),(63,false),(70,true),(72,false),(79,false),(86,true),(89,true)]
theorem inp_5862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5862 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5862 (by decide) v hb
def cl_5863 : CNF.NClause := [(45,false),(14,false),(63,true),(70,true),(72,false),(79,false),(86,true),(89,true)]
theorem inp_5863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5863 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5863 (by decide) v hb
def cl_5864 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(72,false),(79,false),(86,true),(89,true)]
theorem inp_5864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5864 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5864 (by decide) v hb
def cl_5865 : CNF.NClause := [(45,false),(14,false),(63,false),(70,false),(72,true),(79,false),(86,true),(89,true)]
theorem inp_5865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5865 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5865 (by decide) v hb
def cl_5866 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,true),(79,false),(86,true),(89,true)]
theorem inp_5866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5866 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5866 (by decide) v hb
def cl_5867 : CNF.NClause := [(45,false),(14,false),(63,true),(70,false),(72,true),(79,false),(86,true),(89,true)]
theorem inp_5867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5867 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5867 (by decide) v hb
def cl_5868 : CNF.NClause := [(45,false),(14,true),(63,true),(70,false),(72,true),(79,false),(86,true),(89,true)]
theorem inp_5868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5868 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5868 (by decide) v hb
def cl_5869 : CNF.NClause := [(45,false),(14,false),(63,false),(70,true),(72,true),(79,false),(86,true),(89,true)]
theorem inp_5869 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5869 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5869 (by decide) v hb
end Percolation.NReplay
