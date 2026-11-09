import NInputs122
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_6959 : CNF.NClause := [(54,false),(23,false),(65,true),(67,true),(74,true),(81,false),(83,true),(89,false)]
theorem inp_6959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6959 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6959 (by decide) v hb
def cl_6960 : CNF.NClause := [(54,false),(23,true),(65,true),(67,true),(74,true),(81,false),(83,true),(89,false)]
theorem inp_6960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6960 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6960 (by decide) v hb
def cl_6961 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,false),(81,true),(83,true),(89,false)]
theorem inp_6961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6961 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6961 (by decide) v hb
def cl_6962 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,false),(81,true),(83,true),(89,false)]
theorem inp_6962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6962 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6962 v hb
def cl_6963 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(74,false),(81,true),(83,true),(89,false)]
theorem inp_6963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6963 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6963 (by decide) v hb
def cl_6964 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,false),(81,true),(83,true),(89,false)]
theorem inp_6964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6964 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6964 v hb
def cl_6965 : CNF.NClause := [(54,false),(23,false),(65,false),(67,true),(74,false),(81,true),(83,true),(89,false)]
theorem inp_6965 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6965 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6965 (by decide) v hb
def cl_6966 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(74,false),(81,true),(83,true),(89,false)]
theorem inp_6966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6966 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6966 (by decide) v hb
def cl_6968 : CNF.NClause := [(54,false),(23,true),(65,true),(67,true),(74,false),(81,true),(83,true),(89,false)]
theorem inp_6968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6968 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6968 (by decide) v hb
def cl_6969 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,true),(81,true),(83,true),(89,false)]
theorem inp_6969 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6969 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6969 (by decide) v hb
def cl_6970 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,true),(81,true),(83,true),(89,false)]
theorem inp_6970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6970 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6970 (by decide) v hb
def cl_6972 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,true),(81,true),(83,true),(89,false)]
theorem inp_6972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6972 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6972 (by decide) v hb
def cl_6973 : CNF.NClause := [(54,false),(23,false),(65,false),(67,true),(74,true),(81,true),(83,true),(89,false)]
theorem inp_6973 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6973 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6973 (by decide) v hb
def cl_6974 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(74,true),(81,true),(83,true),(89,false)]
theorem inp_6974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6974 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6974 (by decide) v hb
def cl_6976 : CNF.NClause := [(54,false),(23,true),(65,true),(67,true),(74,true),(81,true),(83,true),(89,false)]
theorem inp_6976 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6976 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6976 (by decide) v hb
def cl_6977 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,false),(81,false),(83,false),(89,true)]
theorem inp_6977 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6977 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6977 v hb
def cl_6978 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,false),(81,false),(83,false),(89,true)]
theorem inp_6978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6978 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6978 v hb
def cl_6979 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(74,false),(81,false),(83,false),(89,true)]
theorem inp_6979 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6979 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6979 v hb
def cl_6980 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,false),(81,false),(83,false),(89,true)]
theorem inp_6980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6980 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6980 v hb
def cl_6981 : CNF.NClause := [(54,false),(23,false),(65,false),(67,true),(74,false),(81,false),(83,false),(89,true)]
theorem inp_6981 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6981 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6981 (by decide) v hb
def cl_6982 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(74,false),(81,false),(83,false),(89,true)]
theorem inp_6982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6982 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6982 (by decide) v hb
def cl_6983 : CNF.NClause := [(54,false),(23,false),(65,true),(67,true),(74,false),(81,false),(83,false),(89,true)]
theorem inp_6983 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6983 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6983 (by decide) v hb
def cl_6984 : CNF.NClause := [(54,false),(23,true),(65,true),(67,true),(74,false),(81,false),(83,false),(89,true)]
theorem inp_6984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6984 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6984 (by decide) v hb
def cl_6985 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,true),(81,false),(83,false),(89,true)]
theorem inp_6985 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6985 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6985 v hb
def cl_6986 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,true),(81,false),(83,false),(89,true)]
theorem inp_6986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6986 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6986 (by decide) v hb
def cl_6987 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(74,true),(81,false),(83,false),(89,true)]
theorem inp_6987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6987 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6987 (by decide) v hb
def cl_6988 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,true),(81,false),(83,false),(89,true)]
theorem inp_6988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6988 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6988 (by decide) v hb
def cl_6989 : CNF.NClause := [(54,false),(23,false),(65,false),(67,true),(74,true),(81,false),(83,false),(89,true)]
theorem inp_6989 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6989 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6989 (by decide) v hb
def cl_6990 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(74,true),(81,false),(83,false),(89,true)]
theorem inp_6990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6990 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6990 (by decide) v hb
def cl_6991 : CNF.NClause := [(54,false),(23,false),(65,true),(67,true),(74,true),(81,false),(83,false),(89,true)]
theorem inp_6991 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6991 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6991 (by decide) v hb
def cl_6992 : CNF.NClause := [(54,false),(23,true),(65,true),(67,true),(74,true),(81,false),(83,false),(89,true)]
theorem inp_6992 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6992 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6992 (by decide) v hb
def cl_6993 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,false),(81,true),(83,false),(89,true)]
theorem inp_6993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6993 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6993 v hb
def cl_6994 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,false),(81,true),(83,false),(89,true)]
theorem inp_6994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6994 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6994 v hb
def cl_6995 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(74,false),(81,true),(83,false),(89,true)]
theorem inp_6995 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6995 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6995 v hb
def cl_6996 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,false),(81,true),(83,false),(89,true)]
theorem inp_6996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6996 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6996 v hb
def cl_6997 : CNF.NClause := [(54,false),(23,false),(65,false),(67,true),(74,false),(81,true),(83,false),(89,true)]
theorem inp_6997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6997 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6997 (by decide) v hb
def cl_6998 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(74,false),(81,true),(83,false),(89,true)]
theorem inp_6998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6998 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6998 (by decide) v hb
def cl_6999 : CNF.NClause := [(54,false),(23,false),(65,true),(67,true),(74,false),(81,true),(83,false),(89,true)]
theorem inp_6999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6999 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6999 (by decide) v hb
def cl_7000 : CNF.NClause := [(54,false),(23,true),(65,true),(67,true),(74,false),(81,true),(83,false),(89,true)]
theorem inp_7000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7000 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7000 (by decide) v hb
def cl_7001 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,true),(81,true),(83,false),(89,true)]
theorem inp_7001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7001 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7001 (by decide) v hb
def cl_7002 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,true),(81,true),(83,false),(89,true)]
theorem inp_7002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7002 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7002 (by decide) v hb
def cl_7003 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(74,true),(81,true),(83,false),(89,true)]
theorem inp_7003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7003 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7003 (by decide) v hb
def cl_7004 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,true),(81,true),(83,false),(89,true)]
theorem inp_7004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7004 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7004 (by decide) v hb
def cl_7005 : CNF.NClause := [(54,false),(23,false),(65,false),(67,true),(74,true),(81,true),(83,false),(89,true)]
theorem inp_7005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7005 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7005 (by decide) v hb
def cl_7006 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(74,true),(81,true),(83,false),(89,true)]
theorem inp_7006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7006 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7006 (by decide) v hb
def cl_7007 : CNF.NClause := [(54,false),(23,false),(65,true),(67,true),(74,true),(81,true),(83,false),(89,true)]
theorem inp_7007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7007 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7007 (by decide) v hb
def cl_7008 : CNF.NClause := [(54,false),(23,true),(65,true),(67,true),(74,true),(81,true),(83,false),(89,true)]
theorem inp_7008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7008 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7008 (by decide) v hb
def cl_7009 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,false),(81,false),(83,true),(89,true)]
theorem inp_7009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7009 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7009 (by decide) v hb
def cl_7010 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,false),(81,false),(83,true),(89,true)]
theorem inp_7010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7010 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7010 v hb
def cl_7011 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(74,false),(81,false),(83,true),(89,true)]
theorem inp_7011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7011 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7011 (by decide) v hb
end Percolation.NReplay
