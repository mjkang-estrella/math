import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause1078 : CNF.NClause := [(78,true),(4,true),(6,false),(13,true),(15,false),(22,true),(27,true)]
theorem inputList1078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1078 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1078 (by decide) v hb
mask_input "1078|32832|302231454903657432096784"
def inputClause1079 : CNF.NClause := [(78,true),(4,false),(6,true),(13,true),(15,false),(22,true),(27,true)]
theorem inputList1079 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1079 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1079 (by decide) v hb
mask_input "1079|32784|302231454903657432096832"
def inputClause1081 : CNF.NClause := [(78,true),(4,false),(6,false),(13,false),(15,true),(22,true),(27,true)]
theorem inputList1081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1081 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1081 (by decide) v hb
mask_input "1081|8272|302231454903657432121344"
def inputClause1082 : CNF.NClause := [(78,true),(4,true),(6,false),(13,false),(15,true),(22,true),(27,true)]
theorem inputList1082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1082 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1082 (by decide) v hb
mask_input "1082|8256|302231454903657432121360"
def inputClause1083 : CNF.NClause := [(78,true),(4,false),(6,true),(13,false),(15,true),(22,true),(27,true)]
theorem inputList1083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1083 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1083 (by decide) v hb
mask_input "1083|8208|302231454903657432121408"
def inputClause1085 : CNF.NClause := [(78,true),(4,false),(6,false),(13,true),(15,true),(22,true),(27,true)]
theorem inputList1085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1085 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1085 (by decide) v hb
mask_input "1085|80|302231454903657432129536"
def inputClause1088 : CNF.NClause := [(78,false),(4,true),(6,true),(13,true),(15,true),(22,true),(27,true)]
theorem inputList1088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1088 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1088 (by decide) v hb
mask_input "1088|302231454903657293676544|138453072"
def inputClause1089 : CNF.NClause := [(79,true),(2,false),(8,false),(14,false),(15,false),(21,false),(26,false)]
theorem inputList1089 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1089 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1089 (by decide) v hb
mask_input "1089|69255428|604462909807314587353088"
def inputClause1090 : CNF.NClause := [(79,true),(2,true),(8,false),(14,false),(15,false),(21,false),(26,false)]
theorem inputList1090 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1090 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1090 (by decide) v hb
mask_input "1090|69255424|604462909807314587353092"
def inputClause1091 : CNF.NClause := [(79,true),(2,false),(8,true),(14,false),(15,false),(21,false),(26,false)]
theorem inputList1091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1091 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1091 (by decide) v hb
mask_input "1091|69255172|604462909807314587353344"
def inputClause1092 : CNF.NClause := [(79,true),(2,true),(8,true),(14,false),(15,false),(21,false),(26,false)]
theorem inputList1092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1092 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1092 (by decide) v hb
mask_input "1092|69255168|604462909807314587353348"
def inputClause1093 : CNF.NClause := [(79,true),(2,false),(8,false),(14,true),(15,false),(21,false),(26,false)]
theorem inputList1093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1093 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1093 (by decide) v hb
mask_input "1093|69239044|604462909807314587369472"
def inputClause1094 : CNF.NClause := [(79,true),(2,true),(8,false),(14,true),(15,false),(21,false),(26,false)]
theorem inputList1094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1094 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1094 (by decide) v hb
mask_input "1094|69239040|604462909807314587369476"
def inputClause1095 : CNF.NClause := [(79,true),(2,false),(8,true),(14,true),(15,false),(21,false),(26,false)]
theorem inputList1095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1095 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1095 (by decide) v hb
mask_input "1095|69238788|604462909807314587369728"
def inputClause1096 : CNF.NClause := [(79,true),(2,true),(8,true),(14,true),(15,false),(21,false),(26,false)]
theorem inputList1096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1096 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1096 (by decide) v hb
mask_input "1096|69238784|604462909807314587369732"
def inputClause1097 : CNF.NClause := [(79,true),(2,false),(8,false),(14,false),(15,true),(21,false),(26,false)]
theorem inputList1097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1097 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1097 (by decide) v hb
mask_input "1097|69222660|604462909807314587385856"
def inputClause1098 : CNF.NClause := [(79,true),(2,true),(8,false),(14,false),(15,true),(21,false),(26,false)]
theorem inputList1098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1098 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1098 (by decide) v hb
mask_input "1098|69222656|604462909807314587385860"
def inputClause1099 : CNF.NClause := [(79,true),(2,false),(8,true),(14,false),(15,true),(21,false),(26,false)]
theorem inputList1099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1099 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1099 (by decide) v hb
mask_input "1099|69222404|604462909807314587386112"
def inputClause1100 : CNF.NClause := [(79,true),(2,true),(8,true),(14,false),(15,true),(21,false),(26,false)]
theorem inputList1100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1100 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1100 (by decide) v hb
mask_input "1100|69222400|604462909807314587386116"
def inputClause1101 : CNF.NClause := [(79,true),(2,false),(8,false),(14,true),(15,true),(21,false),(26,false)]
theorem inputList1101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1101 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1101 (by decide) v hb
mask_input "1101|69206276|604462909807314587402240"
def inputClause1102 : CNF.NClause := [(79,true),(2,true),(8,false),(14,true),(15,true),(21,false),(26,false)]
theorem inputList1102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1102 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1102 (by decide) v hb
mask_input "1102|69206272|604462909807314587402244"
def inputClause1103 : CNF.NClause := [(79,true),(2,false),(8,true),(14,true),(15,true),(21,false),(26,false)]
theorem inputList1103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1103 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1103 (by decide) v hb
mask_input "1103|69206020|604462909807314587402496"
def inputClause1104 : CNF.NClause := [(79,true),(2,true),(8,true),(14,true),(15,true),(21,false),(26,false)]
theorem inputList1104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1104 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1104 (by decide) v hb
mask_input "1104|69206016|604462909807314587402500"
def inputClause1105 : CNF.NClause := [(79,true),(2,false),(8,false),(14,false),(15,false),(21,true),(26,false)]
theorem inputList1105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1105 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1105 (by decide) v hb
mask_input "1105|67158276|604462909807314589450240"
def inputClause1106 : CNF.NClause := [(79,true),(2,true),(8,false),(14,false),(15,false),(21,true),(26,false)]
theorem inputList1106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1106 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1106 (by decide) v hb
mask_input "1106|67158272|604462909807314589450244"
def inputClause1107 : CNF.NClause := [(79,true),(2,false),(8,true),(14,false),(15,false),(21,true),(26,false)]
theorem inputList1107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1107 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1107 (by decide) v hb
mask_input "1107|67158020|604462909807314589450496"
def inputClause1108 : CNF.NClause := [(79,true),(2,true),(8,true),(14,false),(15,false),(21,true),(26,false)]
theorem inputList1108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1108 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1108 (by decide) v hb
mask_input "1108|67158016|604462909807314589450500"
def inputClause1109 : CNF.NClause := [(79,true),(2,false),(8,false),(14,true),(15,false),(21,true),(26,false)]
theorem inputList1109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1109 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1109 (by decide) v hb
mask_input "1109|67141892|604462909807314589466624"
def inputClause1110 : CNF.NClause := [(79,true),(2,true),(8,false),(14,true),(15,false),(21,true),(26,false)]
theorem inputList1110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1110 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1110 (by decide) v hb
mask_input "1110|67141888|604462909807314589466628"
def inputClause1111 : CNF.NClause := [(79,true),(2,false),(8,true),(14,true),(15,false),(21,true),(26,false)]
theorem inputList1111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1111 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1111 (by decide) v hb
mask_input "1111|67141636|604462909807314589466880"
def inputClause1112 : CNF.NClause := [(79,true),(2,true),(8,true),(14,true),(15,false),(21,true),(26,false)]
theorem inputList1112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1112 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1112 (by decide) v hb
mask_input "1112|67141632|604462909807314589466884"
def inputClause1113 : CNF.NClause := [(79,true),(2,false),(8,false),(14,false),(15,true),(21,true),(26,false)]
theorem inputList1113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1113 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1113 (by decide) v hb
mask_input "1113|67125508|604462909807314589483008"
def inputClause1114 : CNF.NClause := [(79,true),(2,true),(8,false),(14,false),(15,true),(21,true),(26,false)]
theorem inputList1114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1114 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1114 (by decide) v hb
mask_input "1114|67125504|604462909807314589483012"
def inputClause1115 : CNF.NClause := [(79,true),(2,false),(8,true),(14,false),(15,true),(21,true),(26,false)]
theorem inputList1115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1115 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1115 (by decide) v hb
mask_input "1115|67125252|604462909807314589483264"
def inputClause1116 : CNF.NClause := [(79,true),(2,true),(8,true),(14,false),(15,true),(21,true),(26,false)]
theorem inputList1116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1116 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1116 (by decide) v hb
mask_input "1116|67125248|604462909807314589483268"
def inputClause1117 : CNF.NClause := [(79,true),(2,false),(8,false),(14,true),(15,true),(21,true),(26,false)]
theorem inputList1117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1117 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1117 (by decide) v hb
mask_input "1117|67109124|604462909807314589499392"
def inputClause1118 : CNF.NClause := [(79,true),(2,true),(8,false),(14,true),(15,true),(21,true),(26,false)]
theorem inputList1118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1118 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1118 (by decide) v hb
mask_input "1118|67109120|604462909807314589499396"
def inputClause1119 : CNF.NClause := [(79,true),(2,false),(8,true),(14,true),(15,true),(21,true),(26,false)]
theorem inputList1119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1119 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1119 (by decide) v hb
mask_input "1119|67108868|604462909807314589499648"
def inputClause1121 : CNF.NClause := [(79,true),(2,false),(8,false),(14,false),(15,false),(21,false),(26,true)]
theorem inputList1121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1121 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1121 (by decide) v hb
mask_input "1121|2146564|604462909807314654461952"
def inputClause1122 : CNF.NClause := [(79,true),(2,true),(8,false),(14,false),(15,false),(21,false),(26,true)]
theorem inputList1122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1122 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1122 (by decide) v hb
mask_input "1122|2146560|604462909807314654461956"
end Percolation.MaskChain
