import NInputs101
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_5870 : CNF.NClause := [(45,false),(14,true),(63,false),(70,true),(72,true),(79,false),(86,true),(89,true)]
theorem inp_5870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5870 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5870 (by decide) v hb
def cl_5871 : CNF.NClause := [(45,false),(14,false),(63,true),(70,true),(72,true),(79,false),(86,true),(89,true)]
theorem inp_5871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5871 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5871 (by decide) v hb
def cl_5872 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(72,true),(79,false),(86,true),(89,true)]
theorem inp_5872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5872 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5872 (by decide) v hb
def cl_5873 : CNF.NClause := [(45,false),(14,false),(63,false),(70,false),(72,false),(79,true),(86,true),(89,true)]
theorem inp_5873 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5873 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5873 (by decide) v hb
def cl_5874 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,false),(79,true),(86,true),(89,true)]
theorem inp_5874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5874 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5874 (by decide) v hb
def cl_5876 : CNF.NClause := [(45,false),(14,true),(63,true),(70,false),(72,false),(79,true),(86,true),(89,true)]
theorem inp_5876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5876 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5876 (by decide) v hb
def cl_5877 : CNF.NClause := [(45,false),(14,false),(63,false),(70,true),(72,false),(79,true),(86,true),(89,true)]
theorem inp_5877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5877 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5877 (by decide) v hb
def cl_5878 : CNF.NClause := [(45,false),(14,true),(63,false),(70,true),(72,false),(79,true),(86,true),(89,true)]
theorem inp_5878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5878 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5878 (by decide) v hb
def cl_5879 : CNF.NClause := [(45,false),(14,false),(63,true),(70,true),(72,false),(79,true),(86,true),(89,true)]
theorem inp_5879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5879 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5879 (by decide) v hb
def cl_5880 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(72,false),(79,true),(86,true),(89,true)]
theorem inp_5880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5880 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5880 (by decide) v hb
def cl_5881 : CNF.NClause := [(45,false),(14,false),(63,false),(70,false),(72,true),(79,true),(86,true),(89,true)]
theorem inp_5881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5881 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5881 (by decide) v hb
def cl_5882 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,true),(79,true),(86,true),(89,true)]
theorem inp_5882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5882 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5882 (by decide) v hb
def cl_5884 : CNF.NClause := [(45,false),(14,true),(63,true),(70,false),(72,true),(79,true),(86,true),(89,true)]
theorem inp_5884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5884 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5884 (by decide) v hb
def cl_5886 : CNF.NClause := [(45,false),(14,true),(63,false),(70,true),(72,true),(79,true),(86,true),(89,true)]
theorem inp_5886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5886 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5886 (by decide) v hb
def cl_5888 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(72,true),(79,true),(86,true),(89,true)]
theorem inp_5888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5888 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) cl_5888 (by decide) v hb
def cl_5889 : CNF.NClause := [(46,true),(15,false),(77,false),(78,false),(79,false),(80,false),(81,false),(92,false)]
theorem inp_5889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5889 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5889 (by decide) v hb
def cl_5890 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,false),(80,false),(81,false),(92,false)]
theorem inp_5890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5890 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5890 v hb
def cl_5891 : CNF.NClause := [(46,false),(15,false),(77,true),(78,false),(79,false),(80,false),(81,false),(92,false)]
theorem inp_5891 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5891 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5891 (by decide) v hb
def cl_5892 : CNF.NClause := [(46,false),(15,true),(77,true),(78,false),(79,false),(80,false),(81,false),(92,false)]
theorem inp_5892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5892 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5892 (by decide) v hb
def cl_5893 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(79,false),(80,false),(81,false),(92,false)]
theorem inp_5893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5893 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5893 (by decide) v hb
def cl_5894 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(79,false),(80,false),(81,false),(92,false)]
theorem inp_5894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5894 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5894 (by decide) v hb
def cl_5895 : CNF.NClause := [(46,false),(15,false),(77,true),(78,true),(79,false),(80,false),(81,false),(92,false)]
theorem inp_5895 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5895 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5895 (by decide) v hb
def cl_5896 : CNF.NClause := [(46,false),(15,true),(77,true),(78,true),(79,false),(80,false),(81,false),(92,false)]
theorem inp_5896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5896 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5896 (by decide) v hb
def cl_5897 : CNF.NClause := [(46,false),(15,false),(77,false),(78,false),(79,true),(80,false),(81,false),(92,false)]
theorem inp_5897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5897 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5897 (by decide) v hb
def cl_5898 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,true),(80,false),(81,false),(92,false)]
theorem inp_5898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5898 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5898 v hb
def cl_5899 : CNF.NClause := [(46,false),(15,false),(77,true),(78,false),(79,true),(80,false),(81,false),(92,false)]
theorem inp_5899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5899 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5899 (by decide) v hb
def cl_5900 : CNF.NClause := [(46,false),(15,true),(77,true),(78,false),(79,true),(80,false),(81,false),(92,false)]
theorem inp_5900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5900 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5900 (by decide) v hb
def cl_5901 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(79,true),(80,false),(81,false),(92,false)]
theorem inp_5901 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5901 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5901 (by decide) v hb
def cl_5902 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(79,true),(80,false),(81,false),(92,false)]
theorem inp_5902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5902 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5902 (by decide) v hb
def cl_5903 : CNF.NClause := [(46,false),(15,false),(77,true),(78,true),(79,true),(80,false),(81,false),(92,false)]
theorem inp_5903 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5903 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5903 (by decide) v hb
def cl_5904 : CNF.NClause := [(46,false),(15,true),(77,true),(78,true),(79,true),(80,false),(81,false),(92,false)]
theorem inp_5904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5904 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5904 (by decide) v hb
def cl_5905 : CNF.NClause := [(46,false),(15,false),(77,false),(78,false),(79,false),(80,true),(81,false),(92,false)]
theorem inp_5905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5905 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5905 (by decide) v hb
def cl_5906 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,false),(80,true),(81,false),(92,false)]
theorem inp_5906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5906 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5906 v hb
def cl_5907 : CNF.NClause := [(46,false),(15,false),(77,true),(78,false),(79,false),(80,true),(81,false),(92,false)]
theorem inp_5907 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5907 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5907 (by decide) v hb
def cl_5908 : CNF.NClause := [(46,false),(15,true),(77,true),(78,false),(79,false),(80,true),(81,false),(92,false)]
theorem inp_5908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5908 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5908 (by decide) v hb
def cl_5909 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(79,false),(80,true),(81,false),(92,false)]
theorem inp_5909 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5909 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5909 (by decide) v hb
def cl_5910 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(79,false),(80,true),(81,false),(92,false)]
theorem inp_5910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5910 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5910 (by decide) v hb
def cl_5911 : CNF.NClause := [(46,false),(15,false),(77,true),(78,true),(79,false),(80,true),(81,false),(92,false)]
theorem inp_5911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5911 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5911 (by decide) v hb
def cl_5912 : CNF.NClause := [(46,false),(15,true),(77,true),(78,true),(79,false),(80,true),(81,false),(92,false)]
theorem inp_5912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5912 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5912 (by decide) v hb
def cl_5913 : CNF.NClause := [(46,false),(15,false),(77,false),(78,false),(79,true),(80,true),(81,false),(92,false)]
theorem inp_5913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5913 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5913 (by decide) v hb
def cl_5914 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,true),(80,true),(81,false),(92,false)]
theorem inp_5914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5914 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5914 v hb
def cl_5915 : CNF.NClause := [(46,false),(15,false),(77,true),(78,false),(79,true),(80,true),(81,false),(92,false)]
theorem inp_5915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5915 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5915 (by decide) v hb
def cl_5916 : CNF.NClause := [(46,false),(15,true),(77,true),(78,false),(79,true),(80,true),(81,false),(92,false)]
theorem inp_5916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5916 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5916 (by decide) v hb
def cl_5917 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(79,true),(80,true),(81,false),(92,false)]
theorem inp_5917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5917 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5917 (by decide) v hb
def cl_5918 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(79,true),(80,true),(81,false),(92,false)]
theorem inp_5918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5918 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5918 (by decide) v hb
def cl_5919 : CNF.NClause := [(46,false),(15,false),(77,true),(78,true),(79,true),(80,true),(81,false),(92,false)]
theorem inp_5919 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5919 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5919 (by decide) v hb
def cl_5920 : CNF.NClause := [(46,false),(15,true),(77,true),(78,true),(79,true),(80,true),(81,false),(92,false)]
theorem inp_5920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5920 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5920 (by decide) v hb
def cl_5921 : CNF.NClause := [(46,false),(15,false),(77,false),(78,false),(79,false),(80,false),(81,true),(92,false)]
theorem inp_5921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5921 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5921 (by decide) v hb
def cl_5922 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,false),(80,false),(81,true),(92,false)]
theorem inp_5922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5922 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5922 (by decide) v hb
def cl_5923 : CNF.NClause := [(46,false),(15,false),(77,true),(78,false),(79,false),(80,false),(81,true),(92,false)]
theorem inp_5923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5923 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5923 (by decide) v hb
end Percolation.NReplay
