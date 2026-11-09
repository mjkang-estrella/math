import NInputs015
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_1076 : CNF.NClause := [(78,true),(4,true),(6,true),(13,false),(15,false),(22,true),(27,true)]
theorem inp_1076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1076 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1076 (by decide) v hb
def cl_1077 : CNF.NClause := [(78,true),(4,false),(6,false),(13,true),(15,false),(22,true),(27,true)]
theorem inp_1077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1077 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1077 v hb
def cl_1078 : CNF.NClause := [(78,true),(4,true),(6,false),(13,true),(15,false),(22,true),(27,true)]
theorem inp_1078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1078 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1078 v hb
def cl_1079 : CNF.NClause := [(78,true),(4,false),(6,true),(13,true),(15,false),(22,true),(27,true)]
theorem inp_1079 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1079 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1079 v hb
def cl_1080 : CNF.NClause := [(78,false),(4,true),(6,true),(13,true),(15,false),(22,true),(27,true)]
theorem inp_1080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1080 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1080 v hb
def cl_1081 : CNF.NClause := [(78,true),(4,false),(6,false),(13,false),(15,true),(22,true),(27,true)]
theorem inp_1081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1081 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1081 (by decide) v hb
def cl_1082 : CNF.NClause := [(78,true),(4,true),(6,false),(13,false),(15,true),(22,true),(27,true)]
theorem inp_1082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1082 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1082 v hb
def cl_1083 : CNF.NClause := [(78,true),(4,false),(6,true),(13,false),(15,true),(22,true),(27,true)]
theorem inp_1083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1083 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1083 (by decide) v hb
def cl_1084 : CNF.NClause := [(78,false),(4,true),(6,true),(13,false),(15,true),(22,true),(27,true)]
theorem inp_1084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1084 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1084 v hb
def cl_1085 : CNF.NClause := [(78,true),(4,false),(6,false),(13,true),(15,true),(22,true),(27,true)]
theorem inp_1085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1085 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1085 v hb
def cl_1086 : CNF.NClause := [(78,false),(4,true),(6,false),(13,true),(15,true),(22,true),(27,true)]
theorem inp_1086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1086 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1086 v hb
def cl_1087 : CNF.NClause := [(78,false),(4,false),(6,true),(13,true),(15,true),(22,true),(27,true)]
theorem inp_1087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1087 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1087 v hb
def cl_1088 : CNF.NClause := [(78,false),(4,true),(6,true),(13,true),(15,true),(22,true),(27,true)]
theorem inp_1088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1088 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1088 v hb
def cl_1089 : CNF.NClause := [(79,true),(2,false),(8,false),(14,false),(15,false),(21,false),(26,false)]
theorem inp_1089 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1089 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1089 v hb
def cl_1090 : CNF.NClause := [(79,true),(2,true),(8,false),(14,false),(15,false),(21,false),(26,false)]
theorem inp_1090 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1090 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1090 v hb
def cl_1091 : CNF.NClause := [(79,true),(2,false),(8,true),(14,false),(15,false),(21,false),(26,false)]
theorem inp_1091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1091 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1091 v hb
def cl_1092 : CNF.NClause := [(79,true),(2,true),(8,true),(14,false),(15,false),(21,false),(26,false)]
theorem inp_1092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1092 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1092 v hb
def cl_1093 : CNF.NClause := [(79,true),(2,false),(8,false),(14,true),(15,false),(21,false),(26,false)]
theorem inp_1093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1093 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1093 v hb
def cl_1094 : CNF.NClause := [(79,true),(2,true),(8,false),(14,true),(15,false),(21,false),(26,false)]
theorem inp_1094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1094 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1094 (by decide) v hb
def cl_1095 : CNF.NClause := [(79,true),(2,false),(8,true),(14,true),(15,false),(21,false),(26,false)]
theorem inp_1095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1095 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1095 v hb
def cl_1096 : CNF.NClause := [(79,true),(2,true),(8,true),(14,true),(15,false),(21,false),(26,false)]
theorem inp_1096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1096 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1096 v hb
def cl_1097 : CNF.NClause := [(79,true),(2,false),(8,false),(14,false),(15,true),(21,false),(26,false)]
theorem inp_1097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1097 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1097 v hb
def cl_1098 : CNF.NClause := [(79,true),(2,true),(8,false),(14,false),(15,true),(21,false),(26,false)]
theorem inp_1098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1098 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1098 (by decide) v hb
def cl_1099 : CNF.NClause := [(79,true),(2,false),(8,true),(14,false),(15,true),(21,false),(26,false)]
theorem inp_1099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1099 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1099 v hb
def cl_1100 : CNF.NClause := [(79,true),(2,true),(8,true),(14,false),(15,true),(21,false),(26,false)]
theorem inp_1100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1100 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1100 (by decide) v hb
def cl_1101 : CNF.NClause := [(79,true),(2,false),(8,false),(14,true),(15,true),(21,false),(26,false)]
theorem inp_1101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1101 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1101 v hb
def cl_1102 : CNF.NClause := [(79,true),(2,true),(8,false),(14,true),(15,true),(21,false),(26,false)]
theorem inp_1102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1102 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1102 (by decide) v hb
def cl_1103 : CNF.NClause := [(79,true),(2,false),(8,true),(14,true),(15,true),(21,false),(26,false)]
theorem inp_1103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1103 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1103 v hb
def cl_1104 : CNF.NClause := [(79,true),(2,true),(8,true),(14,true),(15,true),(21,false),(26,false)]
theorem inp_1104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1104 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1104 (by decide) v hb
def cl_1105 : CNF.NClause := [(79,true),(2,false),(8,false),(14,false),(15,false),(21,true),(26,false)]
theorem inp_1105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1105 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1105 (by decide) v hb
def cl_1106 : CNF.NClause := [(79,true),(2,true),(8,false),(14,false),(15,false),(21,true),(26,false)]
theorem inp_1106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1106 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1106 v hb
def cl_1107 : CNF.NClause := [(79,true),(2,false),(8,true),(14,false),(15,false),(21,true),(26,false)]
theorem inp_1107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1107 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1107 v hb
def cl_1108 : CNF.NClause := [(79,true),(2,true),(8,true),(14,false),(15,false),(21,true),(26,false)]
theorem inp_1108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1108 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1108 (by decide) v hb
def cl_1109 : CNF.NClause := [(79,true),(2,false),(8,false),(14,true),(15,false),(21,true),(26,false)]
theorem inp_1109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1109 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1109 (by decide) v hb
def cl_1110 : CNF.NClause := [(79,true),(2,true),(8,false),(14,true),(15,false),(21,true),(26,false)]
theorem inp_1110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1110 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1110 v hb
def cl_1111 : CNF.NClause := [(79,true),(2,false),(8,true),(14,true),(15,false),(21,true),(26,false)]
theorem inp_1111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1111 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1111 v hb
def cl_1112 : CNF.NClause := [(79,true),(2,true),(8,true),(14,true),(15,false),(21,true),(26,false)]
theorem inp_1112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1112 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1112 v hb
def cl_1113 : CNF.NClause := [(79,true),(2,false),(8,false),(14,false),(15,true),(21,true),(26,false)]
theorem inp_1113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1113 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1113 (by decide) v hb
def cl_1114 : CNF.NClause := [(79,true),(2,true),(8,false),(14,false),(15,true),(21,true),(26,false)]
theorem inp_1114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1114 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1114 (by decide) v hb
def cl_1115 : CNF.NClause := [(79,true),(2,false),(8,true),(14,false),(15,true),(21,true),(26,false)]
theorem inp_1115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1115 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1115 v hb
def cl_1116 : CNF.NClause := [(79,true),(2,true),(8,true),(14,false),(15,true),(21,true),(26,false)]
theorem inp_1116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1116 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1116 (by decide) v hb
def cl_1117 : CNF.NClause := [(79,true),(2,false),(8,false),(14,true),(15,true),(21,true),(26,false)]
theorem inp_1117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1117 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1117 (by decide) v hb
def cl_1118 : CNF.NClause := [(79,true),(2,true),(8,false),(14,true),(15,true),(21,true),(26,false)]
theorem inp_1118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1118 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1118 (by decide) v hb
def cl_1119 : CNF.NClause := [(79,true),(2,false),(8,true),(14,true),(15,true),(21,true),(26,false)]
theorem inp_1119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1119 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1119 v hb
def cl_1120 : CNF.NClause := [(79,false),(2,true),(8,true),(14,true),(15,true),(21,true),(26,false)]
theorem inp_1120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1120 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1120 v hb
def cl_1121 : CNF.NClause := [(79,true),(2,false),(8,false),(14,false),(15,false),(21,false),(26,true)]
theorem inp_1121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1121 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1121 v hb
def cl_1122 : CNF.NClause := [(79,true),(2,true),(8,false),(14,false),(15,false),(21,false),(26,true)]
theorem inp_1122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1122 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1122 v hb
def cl_1123 : CNF.NClause := [(79,true),(2,false),(8,true),(14,false),(15,false),(21,false),(26,true)]
theorem inp_1123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1123 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1123 v hb
def cl_1124 : CNF.NClause := [(79,true),(2,true),(8,true),(14,false),(15,false),(21,false),(26,true)]
theorem inp_1124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1124 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1124 v hb
def cl_1125 : CNF.NClause := [(79,true),(2,false),(8,false),(14,true),(15,false),(21,false),(26,true)]
theorem inp_1125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1125 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1125 v hb
end Percolation.NReplay
