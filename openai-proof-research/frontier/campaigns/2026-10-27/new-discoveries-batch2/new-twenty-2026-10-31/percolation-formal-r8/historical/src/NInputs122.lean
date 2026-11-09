import NInputs121
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_6908 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(75,true),(78,true),(86,true),(90,true)]
theorem inp_6908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6908 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6908 (by decide) v hb
def cl_6909 : CNF.NClause := [(53,false),(22,false),(64,false),(67,true),(75,true),(78,true),(86,true),(90,true)]
theorem inp_6909 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6909 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6909 (by decide) v hb
def cl_6910 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,true),(78,true),(86,true),(90,true)]
theorem inp_6910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6910 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6910 (by decide) v hb
def cl_6912 : CNF.NClause := [(53,false),(22,true),(64,true),(67,true),(75,true),(78,true),(86,true),(90,true)]
theorem inp_6912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6912 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6912 (by decide) v hb
def cl_6913 : CNF.NClause := [(54,true),(23,false),(65,false),(67,false),(74,false),(81,false),(83,false),(89,false)]
theorem inp_6913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6913 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6913 v hb
def cl_6914 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,false),(81,false),(83,false),(89,false)]
theorem inp_6914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6914 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6914 v hb
def cl_6915 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(74,false),(81,false),(83,false),(89,false)]
theorem inp_6915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6915 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6915 v hb
def cl_6916 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,false),(81,false),(83,false),(89,false)]
theorem inp_6916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6916 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6916 v hb
def cl_6917 : CNF.NClause := [(54,false),(23,false),(65,false),(67,true),(74,false),(81,false),(83,false),(89,false)]
theorem inp_6917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6917 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6917 (by decide) v hb
def cl_6918 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(74,false),(81,false),(83,false),(89,false)]
theorem inp_6918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6918 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6918 (by decide) v hb
def cl_6919 : CNF.NClause := [(54,false),(23,false),(65,true),(67,true),(74,false),(81,false),(83,false),(89,false)]
theorem inp_6919 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6919 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6919 (by decide) v hb
def cl_6920 : CNF.NClause := [(54,false),(23,true),(65,true),(67,true),(74,false),(81,false),(83,false),(89,false)]
theorem inp_6920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6920 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6920 (by decide) v hb
def cl_6921 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,true),(81,false),(83,false),(89,false)]
theorem inp_6921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6921 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6921 v hb
def cl_6922 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,true),(81,false),(83,false),(89,false)]
theorem inp_6922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6922 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6922 (by decide) v hb
def cl_6923 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(74,true),(81,false),(83,false),(89,false)]
theorem inp_6923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6923 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6923 (by decide) v hb
def cl_6924 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,true),(81,false),(83,false),(89,false)]
theorem inp_6924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6924 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6924 (by decide) v hb
def cl_6925 : CNF.NClause := [(54,false),(23,false),(65,false),(67,true),(74,true),(81,false),(83,false),(89,false)]
theorem inp_6925 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6925 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6925 (by decide) v hb
def cl_6926 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(74,true),(81,false),(83,false),(89,false)]
theorem inp_6926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6926 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6926 (by decide) v hb
def cl_6927 : CNF.NClause := [(54,false),(23,false),(65,true),(67,true),(74,true),(81,false),(83,false),(89,false)]
theorem inp_6927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6927 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6927 (by decide) v hb
def cl_6928 : CNF.NClause := [(54,false),(23,true),(65,true),(67,true),(74,true),(81,false),(83,false),(89,false)]
theorem inp_6928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6928 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6928 (by decide) v hb
def cl_6929 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,false),(81,true),(83,false),(89,false)]
theorem inp_6929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6929 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6929 v hb
def cl_6930 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,false),(81,true),(83,false),(89,false)]
theorem inp_6930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6930 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6930 v hb
def cl_6931 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(74,false),(81,true),(83,false),(89,false)]
theorem inp_6931 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6931 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6931 (by decide) v hb
def cl_6932 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,false),(81,true),(83,false),(89,false)]
theorem inp_6932 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6932 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6932 (by decide) v hb
def cl_6933 : CNF.NClause := [(54,false),(23,false),(65,false),(67,true),(74,false),(81,true),(83,false),(89,false)]
theorem inp_6933 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6933 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6933 (by decide) v hb
def cl_6934 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(74,false),(81,true),(83,false),(89,false)]
theorem inp_6934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6934 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6934 (by decide) v hb
def cl_6935 : CNF.NClause := [(54,false),(23,false),(65,true),(67,true),(74,false),(81,true),(83,false),(89,false)]
theorem inp_6935 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6935 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6935 (by decide) v hb
def cl_6936 : CNF.NClause := [(54,false),(23,true),(65,true),(67,true),(74,false),(81,true),(83,false),(89,false)]
theorem inp_6936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6936 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6936 (by decide) v hb
def cl_6937 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,true),(81,true),(83,false),(89,false)]
theorem inp_6937 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6937 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6937 (by decide) v hb
def cl_6938 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,true),(81,true),(83,false),(89,false)]
theorem inp_6938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6938 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6938 (by decide) v hb
def cl_6939 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(74,true),(81,true),(83,false),(89,false)]
theorem inp_6939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6939 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6939 (by decide) v hb
def cl_6940 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,true),(81,true),(83,false),(89,false)]
theorem inp_6940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6940 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6940 (by decide) v hb
def cl_6941 : CNF.NClause := [(54,false),(23,false),(65,false),(67,true),(74,true),(81,true),(83,false),(89,false)]
theorem inp_6941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6941 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6941 (by decide) v hb
def cl_6942 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(74,true),(81,true),(83,false),(89,false)]
theorem inp_6942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6942 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6942 (by decide) v hb
def cl_6943 : CNF.NClause := [(54,false),(23,false),(65,true),(67,true),(74,true),(81,true),(83,false),(89,false)]
theorem inp_6943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6943 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6943 (by decide) v hb
def cl_6944 : CNF.NClause := [(54,false),(23,true),(65,true),(67,true),(74,true),(81,true),(83,false),(89,false)]
theorem inp_6944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6944 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6944 (by decide) v hb
def cl_6945 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,false),(81,false),(83,true),(89,false)]
theorem inp_6945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6945 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6945 (by decide) v hb
def cl_6946 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,false),(81,false),(83,true),(89,false)]
theorem inp_6946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6946 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6946 v hb
def cl_6947 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(74,false),(81,false),(83,true),(89,false)]
theorem inp_6947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6947 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6947 (by decide) v hb
def cl_6948 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,false),(81,false),(83,true),(89,false)]
theorem inp_6948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6948 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6948 v hb
def cl_6949 : CNF.NClause := [(54,false),(23,false),(65,false),(67,true),(74,false),(81,false),(83,true),(89,false)]
theorem inp_6949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6949 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6949 (by decide) v hb
def cl_6950 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(74,false),(81,false),(83,true),(89,false)]
theorem inp_6950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6950 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6950 (by decide) v hb
def cl_6951 : CNF.NClause := [(54,false),(23,false),(65,true),(67,true),(74,false),(81,false),(83,true),(89,false)]
theorem inp_6951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6951 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6951 (by decide) v hb
def cl_6952 : CNF.NClause := [(54,false),(23,true),(65,true),(67,true),(74,false),(81,false),(83,true),(89,false)]
theorem inp_6952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6952 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6952 (by decide) v hb
def cl_6953 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,true),(81,false),(83,true),(89,false)]
theorem inp_6953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6953 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6953 (by decide) v hb
def cl_6954 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,true),(81,false),(83,true),(89,false)]
theorem inp_6954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6954 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6954 (by decide) v hb
def cl_6955 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(74,true),(81,false),(83,true),(89,false)]
theorem inp_6955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6955 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6955 (by decide) v hb
def cl_6956 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,true),(81,false),(83,true),(89,false)]
theorem inp_6956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6956 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6956 (by decide) v hb
def cl_6957 : CNF.NClause := [(54,false),(23,false),(65,false),(67,true),(74,true),(81,false),(83,true),(89,false)]
theorem inp_6957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6957 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6957 (by decide) v hb
def cl_6958 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(74,true),(81,false),(83,true),(89,false)]
theorem inp_6958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6958 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6958 (by decide) v hb
end Percolation.NReplay
