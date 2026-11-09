import Inputs011
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_1069 : CNF.NClause := [(78,true),(4,false),(6,false),(13,true),(15,true),(22,false),(27,true)]
theorem inp_1069 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1069 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1069 (by decide) v h
def cl_1070 : CNF.NClause := [(78,true),(4,true),(6,false),(13,true),(15,true),(22,false),(27,true)]
theorem inp_1070 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1070 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1070 (by decide) v h
def cl_1071 : CNF.NClause := [(78,true),(4,false),(6,true),(13,true),(15,true),(22,false),(27,true)]
theorem inp_1071 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1071 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1071 (by decide) v h
def cl_1072 : CNF.NClause := [(78,false),(4,true),(6,true),(13,true),(15,true),(22,false),(27,true)]
theorem inp_1072 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1072 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1072 (by decide) v h
def cl_1074 : CNF.NClause := [(78,true),(4,true),(6,false),(13,false),(15,false),(22,true),(27,true)]
theorem inp_1074 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1074 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1074 (by decide) v h
def cl_1075 : CNF.NClause := [(78,true),(4,false),(6,true),(13,false),(15,false),(22,true),(27,true)]
theorem inp_1075 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1075 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1075 (by decide) v h
def cl_1077 : CNF.NClause := [(78,true),(4,false),(6,false),(13,true),(15,false),(22,true),(27,true)]
theorem inp_1077 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1077 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1077 (by decide) v h
def cl_1078 : CNF.NClause := [(78,true),(4,true),(6,false),(13,true),(15,false),(22,true),(27,true)]
theorem inp_1078 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1078 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1078 (by decide) v h
def cl_1079 : CNF.NClause := [(78,true),(4,false),(6,true),(13,true),(15,false),(22,true),(27,true)]
theorem inp_1079 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1079 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1079 (by decide) v h
def cl_1080 : CNF.NClause := [(78,false),(4,true),(6,true),(13,true),(15,false),(22,true),(27,true)]
theorem inp_1080 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1080 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1080 (by decide) v h
def cl_1082 : CNF.NClause := [(78,true),(4,true),(6,false),(13,false),(15,true),(22,true),(27,true)]
theorem inp_1082 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1082 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1082 (by decide) v h
def cl_1084 : CNF.NClause := [(78,false),(4,true),(6,true),(13,false),(15,true),(22,true),(27,true)]
theorem inp_1084 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1084 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1084 (by decide) v h
def cl_1085 : CNF.NClause := [(78,true),(4,false),(6,false),(13,true),(15,true),(22,true),(27,true)]
theorem inp_1085 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1085 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1085 (by decide) v h
def cl_1086 : CNF.NClause := [(78,false),(4,true),(6,false),(13,true),(15,true),(22,true),(27,true)]
theorem inp_1086 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1086 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1086 (by decide) v h
def cl_1087 : CNF.NClause := [(78,false),(4,false),(6,true),(13,true),(15,true),(22,true),(27,true)]
theorem inp_1087 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1087 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1087 (by decide) v h
def cl_1088 : CNF.NClause := [(78,false),(4,true),(6,true),(13,true),(15,true),(22,true),(27,true)]
theorem inp_1088 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1088 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1088 (by decide) v h
def cl_1089 : CNF.NClause := [(79,true),(2,false),(8,false),(14,false),(15,false),(21,false),(26,false)]
theorem inp_1089 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1089 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1089 (by decide) v h
def cl_1090 : CNF.NClause := [(79,true),(2,true),(8,false),(14,false),(15,false),(21,false),(26,false)]
theorem inp_1090 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1090 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1090 (by decide) v h
def cl_1091 : CNF.NClause := [(79,true),(2,false),(8,true),(14,false),(15,false),(21,false),(26,false)]
theorem inp_1091 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1091 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1091 (by decide) v h
def cl_1092 : CNF.NClause := [(79,true),(2,true),(8,true),(14,false),(15,false),(21,false),(26,false)]
theorem inp_1092 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1092 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1092 (by decide) v h
def cl_1093 : CNF.NClause := [(79,true),(2,false),(8,false),(14,true),(15,false),(21,false),(26,false)]
theorem inp_1093 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1093 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1093 (by decide) v h
def cl_1095 : CNF.NClause := [(79,true),(2,false),(8,true),(14,true),(15,false),(21,false),(26,false)]
theorem inp_1095 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1095 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1095 (by decide) v h
def cl_1096 : CNF.NClause := [(79,true),(2,true),(8,true),(14,true),(15,false),(21,false),(26,false)]
theorem inp_1096 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1096 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1096 (by decide) v h
def cl_1097 : CNF.NClause := [(79,true),(2,false),(8,false),(14,false),(15,true),(21,false),(26,false)]
theorem inp_1097 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1097 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1097 (by decide) v h
def cl_1099 : CNF.NClause := [(79,true),(2,false),(8,true),(14,false),(15,true),(21,false),(26,false)]
theorem inp_1099 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1099 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1099 (by decide) v h
def cl_1101 : CNF.NClause := [(79,true),(2,false),(8,false),(14,true),(15,true),(21,false),(26,false)]
theorem inp_1101 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1101 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1101 (by decide) v h
def cl_1103 : CNF.NClause := [(79,true),(2,false),(8,true),(14,true),(15,true),(21,false),(26,false)]
theorem inp_1103 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1103 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1103 (by decide) v h
def cl_1106 : CNF.NClause := [(79,true),(2,true),(8,false),(14,false),(15,false),(21,true),(26,false)]
theorem inp_1106 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1106 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1106 (by decide) v h
def cl_1107 : CNF.NClause := [(79,true),(2,false),(8,true),(14,false),(15,false),(21,true),(26,false)]
theorem inp_1107 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1107 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1107 (by decide) v h
def cl_1110 : CNF.NClause := [(79,true),(2,true),(8,false),(14,true),(15,false),(21,true),(26,false)]
theorem inp_1110 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1110 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1110 (by decide) v h
def cl_1111 : CNF.NClause := [(79,true),(2,false),(8,true),(14,true),(15,false),(21,true),(26,false)]
theorem inp_1111 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1111 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1111 (by decide) v h
def cl_1112 : CNF.NClause := [(79,true),(2,true),(8,true),(14,true),(15,false),(21,true),(26,false)]
theorem inp_1112 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1112 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1112 (by decide) v h
def cl_1115 : CNF.NClause := [(79,true),(2,false),(8,true),(14,false),(15,true),(21,true),(26,false)]
theorem inp_1115 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1115 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1115 (by decide) v h
def cl_1119 : CNF.NClause := [(79,true),(2,false),(8,true),(14,true),(15,true),(21,true),(26,false)]
theorem inp_1119 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1119 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1119 (by decide) v h
def cl_1120 : CNF.NClause := [(79,false),(2,true),(8,true),(14,true),(15,true),(21,true),(26,false)]
theorem inp_1120 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1120 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1120 (by decide) v h
def cl_1121 : CNF.NClause := [(79,true),(2,false),(8,false),(14,false),(15,false),(21,false),(26,true)]
theorem inp_1121 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1121 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1121 (by decide) v h
def cl_1122 : CNF.NClause := [(79,true),(2,true),(8,false),(14,false),(15,false),(21,false),(26,true)]
theorem inp_1122 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1122 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1122 (by decide) v h
def cl_1123 : CNF.NClause := [(79,true),(2,false),(8,true),(14,false),(15,false),(21,false),(26,true)]
theorem inp_1123 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1123 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1123 (by decide) v h
def cl_1124 : CNF.NClause := [(79,true),(2,true),(8,true),(14,false),(15,false),(21,false),(26,true)]
theorem inp_1124 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1124 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1124 (by decide) v h
def cl_1125 : CNF.NClause := [(79,true),(2,false),(8,false),(14,true),(15,false),(21,false),(26,true)]
theorem inp_1125 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1125 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1125 (by decide) v h
def cl_1126 : CNF.NClause := [(79,true),(2,true),(8,false),(14,true),(15,false),(21,false),(26,true)]
theorem inp_1126 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1126 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1126 (by decide) v h
def cl_1127 : CNF.NClause := [(79,true),(2,false),(8,true),(14,true),(15,false),(21,false),(26,true)]
theorem inp_1127 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1127 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1127 (by decide) v h
def cl_1128 : CNF.NClause := [(79,true),(2,true),(8,true),(14,true),(15,false),(21,false),(26,true)]
theorem inp_1128 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1128 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1128 (by decide) v h
def cl_1129 : CNF.NClause := [(79,true),(2,false),(8,false),(14,false),(15,true),(21,false),(26,true)]
theorem inp_1129 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1129 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1129 (by decide) v h
def cl_1130 : CNF.NClause := [(79,true),(2,true),(8,false),(14,false),(15,true),(21,false),(26,true)]
theorem inp_1130 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1130 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1130 (by decide) v h
def cl_1131 : CNF.NClause := [(79,true),(2,false),(8,true),(14,false),(15,true),(21,false),(26,true)]
theorem inp_1131 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1131 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1131 (by decide) v h
def cl_1135 : CNF.NClause := [(79,true),(2,false),(8,true),(14,true),(15,true),(21,false),(26,true)]
theorem inp_1135 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1135 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1135 (by decide) v h
def cl_1136 : CNF.NClause := [(79,false),(2,true),(8,true),(14,true),(15,true),(21,false),(26,true)]
theorem inp_1136 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1136 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1136 (by decide) v h
def cl_1139 : CNF.NClause := [(79,true),(2,false),(8,true),(14,false),(15,false),(21,true),(26,true)]
theorem inp_1139 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1139 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1139 (by decide) v h
def cl_1140 : CNF.NClause := [(79,true),(2,true),(8,true),(14,false),(15,false),(21,true),(26,true)]
theorem inp_1140 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1140 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1140 (by decide) v h
end Percolation.Replay
