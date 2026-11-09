import NInputs014
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_1026 : CNF.NClause := [(78,true),(4,true),(6,false),(13,false),(15,false),(22,false),(27,false)]
theorem inp_1026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1026 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1026 v hb
def cl_1027 : CNF.NClause := [(78,true),(4,false),(6,true),(13,false),(15,false),(22,false),(27,false)]
theorem inp_1027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1027 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1027 v hb
def cl_1028 : CNF.NClause := [(78,true),(4,true),(6,true),(13,false),(15,false),(22,false),(27,false)]
theorem inp_1028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1028 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1028 v hb
def cl_1029 : CNF.NClause := [(78,true),(4,false),(6,false),(13,true),(15,false),(22,false),(27,false)]
theorem inp_1029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1029 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1029 v hb
def cl_1030 : CNF.NClause := [(78,true),(4,true),(6,false),(13,true),(15,false),(22,false),(27,false)]
theorem inp_1030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1030 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1030 v hb
def cl_1031 : CNF.NClause := [(78,true),(4,false),(6,true),(13,true),(15,false),(22,false),(27,false)]
theorem inp_1031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1031 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1031 v hb
def cl_1032 : CNF.NClause := [(78,true),(4,true),(6,true),(13,true),(15,false),(22,false),(27,false)]
theorem inp_1032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1032 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1032 (by decide) v hb
def cl_1033 : CNF.NClause := [(78,true),(4,false),(6,false),(13,false),(15,true),(22,false),(27,false)]
theorem inp_1033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1033 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1033 (by decide) v hb
def cl_1034 : CNF.NClause := [(78,true),(4,true),(6,false),(13,false),(15,true),(22,false),(27,false)]
theorem inp_1034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1034 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1034 v hb
def cl_1035 : CNF.NClause := [(78,true),(4,false),(6,true),(13,false),(15,true),(22,false),(27,false)]
theorem inp_1035 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1035 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1035 (by decide) v hb
def cl_1036 : CNF.NClause := [(78,true),(4,true),(6,true),(13,false),(15,true),(22,false),(27,false)]
theorem inp_1036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1036 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1036 (by decide) v hb
def cl_1037 : CNF.NClause := [(78,true),(4,false),(6,false),(13,true),(15,true),(22,false),(27,false)]
theorem inp_1037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1037 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1037 v hb
def cl_1038 : CNF.NClause := [(78,true),(4,true),(6,false),(13,true),(15,true),(22,false),(27,false)]
theorem inp_1038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1038 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1038 v hb
def cl_1039 : CNF.NClause := [(78,true),(4,false),(6,true),(13,true),(15,true),(22,false),(27,false)]
theorem inp_1039 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1039 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1039 (by decide) v hb
def cl_1040 : CNF.NClause := [(78,true),(4,true),(6,true),(13,true),(15,true),(22,false),(27,false)]
theorem inp_1040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1040 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1040 (by decide) v hb
def cl_1041 : CNF.NClause := [(78,true),(4,false),(6,false),(13,false),(15,false),(22,true),(27,false)]
theorem inp_1041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1041 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1041 (by decide) v hb
def cl_1042 : CNF.NClause := [(78,true),(4,true),(6,false),(13,false),(15,false),(22,true),(27,false)]
theorem inp_1042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1042 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1042 v hb
def cl_1043 : CNF.NClause := [(78,true),(4,false),(6,true),(13,false),(15,false),(22,true),(27,false)]
theorem inp_1043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1043 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1043 (by decide) v hb
def cl_1044 : CNF.NClause := [(78,true),(4,true),(6,true),(13,false),(15,false),(22,true),(27,false)]
theorem inp_1044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1044 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1044 (by decide) v hb
def cl_1045 : CNF.NClause := [(78,true),(4,false),(6,false),(13,true),(15,false),(22,true),(27,false)]
theorem inp_1045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1045 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1045 v hb
def cl_1046 : CNF.NClause := [(78,true),(4,true),(6,false),(13,true),(15,false),(22,true),(27,false)]
theorem inp_1046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1046 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1046 v hb
def cl_1047 : CNF.NClause := [(78,true),(4,false),(6,true),(13,true),(15,false),(22,true),(27,false)]
theorem inp_1047 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1047 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1047 v hb
def cl_1048 : CNF.NClause := [(78,true),(4,true),(6,true),(13,true),(15,false),(22,true),(27,false)]
theorem inp_1048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1048 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1048 (by decide) v hb
def cl_1049 : CNF.NClause := [(78,true),(4,false),(6,false),(13,false),(15,true),(22,true),(27,false)]
theorem inp_1049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1049 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1049 (by decide) v hb
def cl_1050 : CNF.NClause := [(78,true),(4,true),(6,false),(13,false),(15,true),(22,true),(27,false)]
theorem inp_1050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1050 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1050 v hb
def cl_1051 : CNF.NClause := [(78,true),(4,false),(6,true),(13,false),(15,true),(22,true),(27,false)]
theorem inp_1051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1051 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1051 (by decide) v hb
def cl_1052 : CNF.NClause := [(78,true),(4,true),(6,true),(13,false),(15,true),(22,true),(27,false)]
theorem inp_1052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1052 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1052 (by decide) v hb
def cl_1053 : CNF.NClause := [(78,true),(4,false),(6,false),(13,true),(15,true),(22,true),(27,false)]
theorem inp_1053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1053 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1053 v hb
def cl_1054 : CNF.NClause := [(78,true),(4,true),(6,false),(13,true),(15,true),(22,true),(27,false)]
theorem inp_1054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1054 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1054 v hb
def cl_1055 : CNF.NClause := [(78,true),(4,false),(6,true),(13,true),(15,true),(22,true),(27,false)]
theorem inp_1055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1055 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1055 (by decide) v hb
def cl_1056 : CNF.NClause := [(78,false),(4,true),(6,true),(13,true),(15,true),(22,true),(27,false)]
theorem inp_1056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1056 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1056 v hb
def cl_1057 : CNF.NClause := [(78,true),(4,false),(6,false),(13,false),(15,false),(22,false),(27,true)]
theorem inp_1057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1057 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1057 v hb
def cl_1058 : CNF.NClause := [(78,true),(4,true),(6,false),(13,false),(15,false),(22,false),(27,true)]
theorem inp_1058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1058 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1058 v hb
def cl_1059 : CNF.NClause := [(78,true),(4,false),(6,true),(13,false),(15,false),(22,false),(27,true)]
theorem inp_1059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1059 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1059 v hb
def cl_1060 : CNF.NClause := [(78,true),(4,true),(6,true),(13,false),(15,false),(22,false),(27,true)]
theorem inp_1060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1060 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1060 v hb
def cl_1061 : CNF.NClause := [(78,true),(4,false),(6,false),(13,true),(15,false),(22,false),(27,true)]
theorem inp_1061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1061 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1061 v hb
def cl_1062 : CNF.NClause := [(78,true),(4,true),(6,false),(13,true),(15,false),(22,false),(27,true)]
theorem inp_1062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1062 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1062 v hb
def cl_1063 : CNF.NClause := [(78,true),(4,false),(6,true),(13,true),(15,false),(22,false),(27,true)]
theorem inp_1063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1063 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1063 v hb
def cl_1064 : CNF.NClause := [(78,true),(4,true),(6,true),(13,true),(15,false),(22,false),(27,true)]
theorem inp_1064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1064 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1064 v hb
def cl_1065 : CNF.NClause := [(78,true),(4,false),(6,false),(13,false),(15,true),(22,false),(27,true)]
theorem inp_1065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1065 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1065 v hb
def cl_1066 : CNF.NClause := [(78,true),(4,true),(6,false),(13,false),(15,true),(22,false),(27,true)]
theorem inp_1066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1066 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1066 v hb
def cl_1067 : CNF.NClause := [(78,true),(4,false),(6,true),(13,false),(15,true),(22,false),(27,true)]
theorem inp_1067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1067 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1067 v hb
def cl_1068 : CNF.NClause := [(78,true),(4,true),(6,true),(13,false),(15,true),(22,false),(27,true)]
theorem inp_1068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1068 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1068 (by decide) v hb
def cl_1069 : CNF.NClause := [(78,true),(4,false),(6,false),(13,true),(15,true),(22,false),(27,true)]
theorem inp_1069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1069 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1069 v hb
def cl_1070 : CNF.NClause := [(78,true),(4,true),(6,false),(13,true),(15,true),(22,false),(27,true)]
theorem inp_1070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1070 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1070 v hb
def cl_1071 : CNF.NClause := [(78,true),(4,false),(6,true),(13,true),(15,true),(22,false),(27,true)]
theorem inp_1071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1071 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1071 v hb
def cl_1072 : CNF.NClause := [(78,false),(4,true),(6,true),(13,true),(15,true),(22,false),(27,true)]
theorem inp_1072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1072 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1072 v hb
def cl_1073 : CNF.NClause := [(78,true),(4,false),(6,false),(13,false),(15,false),(22,true),(27,true)]
theorem inp_1073 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1073 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1073 (by decide) v hb
def cl_1074 : CNF.NClause := [(78,true),(4,true),(6,false),(13,false),(15,false),(22,true),(27,true)]
theorem inp_1074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1074 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1074 v hb
def cl_1075 : CNF.NClause := [(78,true),(4,false),(6,true),(13,false),(15,false),(22,true),(27,true)]
theorem inp_1075 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1075 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1075 v hb
end Percolation.NReplay
