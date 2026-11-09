import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause1123 : CNF.NClause := [(79,true),(2,false),(8,true),(14,false),(15,false),(21,false),(26,true)]
theorem inputList1123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1123 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1123 (by decide) v hb
mask_input "1123|2146308|604462909807314654462208"
def inputClause1124 : CNF.NClause := [(79,true),(2,true),(8,true),(14,false),(15,false),(21,false),(26,true)]
theorem inputList1124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1124 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1124 (by decide) v hb
mask_input "1124|2146304|604462909807314654462212"
def inputClause1125 : CNF.NClause := [(79,true),(2,false),(8,false),(14,true),(15,false),(21,false),(26,true)]
theorem inputList1125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1125 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1125 (by decide) v hb
mask_input "1125|2130180|604462909807314654478336"
def inputClause1126 : CNF.NClause := [(79,true),(2,true),(8,false),(14,true),(15,false),(21,false),(26,true)]
theorem inputList1126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1126 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1126 (by decide) v hb
mask_input "1126|2130176|604462909807314654478340"
def inputClause1127 : CNF.NClause := [(79,true),(2,false),(8,true),(14,true),(15,false),(21,false),(26,true)]
theorem inputList1127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1127 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1127 (by decide) v hb
mask_input "1127|2129924|604462909807314654478592"
def inputClause1128 : CNF.NClause := [(79,true),(2,true),(8,true),(14,true),(15,false),(21,false),(26,true)]
theorem inputList1128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1128 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1128 (by decide) v hb
mask_input "1128|2129920|604462909807314654478596"
def inputClause1129 : CNF.NClause := [(79,true),(2,false),(8,false),(14,false),(15,true),(21,false),(26,true)]
theorem inputList1129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1129 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1129 (by decide) v hb
mask_input "1129|2113796|604462909807314654494720"
def inputClause1130 : CNF.NClause := [(79,true),(2,true),(8,false),(14,false),(15,true),(21,false),(26,true)]
theorem inputList1130 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1130 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1130 (by decide) v hb
mask_input "1130|2113792|604462909807314654494724"
def inputClause1131 : CNF.NClause := [(79,true),(2,false),(8,true),(14,false),(15,true),(21,false),(26,true)]
theorem inputList1131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1131 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1131 (by decide) v hb
mask_input "1131|2113540|604462909807314654494976"
def inputClause1132 : CNF.NClause := [(79,true),(2,true),(8,true),(14,false),(15,true),(21,false),(26,true)]
theorem inputList1132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1132 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1132 (by decide) v hb
mask_input "1132|2113536|604462909807314654494980"
def inputClause1133 : CNF.NClause := [(79,true),(2,false),(8,false),(14,true),(15,true),(21,false),(26,true)]
theorem inputList1133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1133 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1133 (by decide) v hb
mask_input "1133|2097412|604462909807314654511104"
def inputClause1134 : CNF.NClause := [(79,true),(2,true),(8,false),(14,true),(15,true),(21,false),(26,true)]
theorem inputList1134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1134 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1134 (by decide) v hb
mask_input "1134|2097408|604462909807314654511108"
def inputClause1135 : CNF.NClause := [(79,true),(2,false),(8,true),(14,true),(15,true),(21,false),(26,true)]
theorem inputList1135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1135 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1135 (by decide) v hb
mask_input "1135|2097156|604462909807314654511360"
def inputClause1137 : CNF.NClause := [(79,true),(2,false),(8,false),(14,false),(15,false),(21,true),(26,true)]
theorem inputList1137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1137 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1137 (by decide) v hb
mask_input "1137|49412|604462909807314656559104"
def inputClause1138 : CNF.NClause := [(79,true),(2,true),(8,false),(14,false),(15,false),(21,true),(26,true)]
theorem inputList1138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1138 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1138 (by decide) v hb
mask_input "1138|49408|604462909807314656559108"
def inputClause1139 : CNF.NClause := [(79,true),(2,false),(8,true),(14,false),(15,false),(21,true),(26,true)]
theorem inputList1139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1139 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1139 (by decide) v hb
mask_input "1139|49156|604462909807314656559360"
def inputClause1140 : CNF.NClause := [(79,true),(2,true),(8,true),(14,false),(15,false),(21,true),(26,true)]
theorem inputList1140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1140 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1140 (by decide) v hb
mask_input "1140|49152|604462909807314656559364"
def inputClause1141 : CNF.NClause := [(79,true),(2,false),(8,false),(14,true),(15,false),(21,true),(26,true)]
theorem inputList1141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1141 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1141 (by decide) v hb
mask_input "1141|33028|604462909807314656575488"
def inputClause1142 : CNF.NClause := [(79,true),(2,true),(8,false),(14,true),(15,false),(21,true),(26,true)]
theorem inputList1142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1142 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1142 (by decide) v hb
mask_input "1142|33024|604462909807314656575492"
def inputClause1143 : CNF.NClause := [(79,true),(2,false),(8,true),(14,true),(15,false),(21,true),(26,true)]
theorem inputList1143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1143 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1143 (by decide) v hb
mask_input "1143|32772|604462909807314656575744"
def inputClause1145 : CNF.NClause := [(79,true),(2,false),(8,false),(14,false),(15,true),(21,true),(26,true)]
theorem inputList1145 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1145 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1145 (by decide) v hb
mask_input "1145|16644|604462909807314656591872"
def inputClause1146 : CNF.NClause := [(79,true),(2,true),(8,false),(14,false),(15,true),(21,true),(26,true)]
theorem inputList1146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1146 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1146 (by decide) v hb
mask_input "1146|16640|604462909807314656591876"
def inputClause1147 : CNF.NClause := [(79,true),(2,false),(8,true),(14,false),(15,true),(21,true),(26,true)]
theorem inputList1147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1147 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1147 (by decide) v hb
mask_input "1147|16388|604462909807314656592128"
def inputClause1149 : CNF.NClause := [(79,true),(2,false),(8,false),(14,true),(15,true),(21,true),(26,true)]
theorem inputList1149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1149 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) inputClause1149 (by decide) v hb
mask_input "1149|260|604462909807314656608256"
def inputClause1153 : CNF.NClause := [(80,true),(3,false),(7,false),(11,false),(15,false),(24,false),(29,false)]
theorem inputList1153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1153 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1153 (by decide) v hb
mask_input "1153|553683080|1208925819614629174706176"
def inputClause1154 : CNF.NClause := [(80,true),(3,true),(7,false),(11,false),(15,false),(24,false),(29,false)]
theorem inputList1154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1154 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1154 (by decide) v hb
mask_input "1154|553683072|1208925819614629174706184"
def inputClause1155 : CNF.NClause := [(80,true),(3,false),(7,true),(11,false),(15,false),(24,false),(29,false)]
theorem inputList1155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1155 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1155 (by decide) v hb
mask_input "1155|553682952|1208925819614629174706304"
def inputClause1156 : CNF.NClause := [(80,true),(3,true),(7,true),(11,false),(15,false),(24,false),(29,false)]
theorem inputList1156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1156 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1156 (by decide) v hb
mask_input "1156|553682944|1208925819614629174706312"
def inputClause1157 : CNF.NClause := [(80,true),(3,false),(7,false),(11,true),(15,false),(24,false),(29,false)]
theorem inputList1157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1157 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1157 (by decide) v hb
mask_input "1157|553681032|1208925819614629174708224"
def inputClause1158 : CNF.NClause := [(80,true),(3,true),(7,false),(11,true),(15,false),(24,false),(29,false)]
theorem inputList1158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1158 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1158 (by decide) v hb
mask_input "1158|553681024|1208925819614629174708232"
def inputClause1159 : CNF.NClause := [(80,true),(3,false),(7,true),(11,true),(15,false),(24,false),(29,false)]
theorem inputList1159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1159 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1159 (by decide) v hb
mask_input "1159|553680904|1208925819614629174708352"
def inputClause1160 : CNF.NClause := [(80,true),(3,true),(7,true),(11,true),(15,false),(24,false),(29,false)]
theorem inputList1160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1160 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1160 (by decide) v hb
mask_input "1160|553680896|1208925819614629174708360"
def inputClause1161 : CNF.NClause := [(80,true),(3,false),(7,false),(11,false),(15,true),(24,false),(29,false)]
theorem inputList1161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1161 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1161 (by decide) v hb
mask_input "1161|553650312|1208925819614629174738944"
def inputClause1162 : CNF.NClause := [(80,true),(3,true),(7,false),(11,false),(15,true),(24,false),(29,false)]
theorem inputList1162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1162 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1162 (by decide) v hb
mask_input "1162|553650304|1208925819614629174738952"
def inputClause1163 : CNF.NClause := [(80,true),(3,false),(7,true),(11,false),(15,true),(24,false),(29,false)]
theorem inputList1163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1163 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1163 (by decide) v hb
mask_input "1163|553650184|1208925819614629174739072"
def inputClause1164 : CNF.NClause := [(80,true),(3,true),(7,true),(11,false),(15,true),(24,false),(29,false)]
theorem inputList1164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1164 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1164 (by decide) v hb
mask_input "1164|553650176|1208925819614629174739080"
def inputClause1165 : CNF.NClause := [(80,true),(3,false),(7,false),(11,true),(15,true),(24,false),(29,false)]
theorem inputList1165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1165 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1165 (by decide) v hb
mask_input "1165|553648264|1208925819614629174740992"
def inputClause1166 : CNF.NClause := [(80,true),(3,true),(7,false),(11,true),(15,true),(24,false),(29,false)]
theorem inputList1166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1166 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1166 (by decide) v hb
mask_input "1166|553648256|1208925819614629174741000"
def inputClause1167 : CNF.NClause := [(80,true),(3,false),(7,true),(11,true),(15,true),(24,false),(29,false)]
theorem inputList1167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1167 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1167 (by decide) v hb
mask_input "1167|553648136|1208925819614629174741120"
def inputClause1168 : CNF.NClause := [(80,true),(3,true),(7,true),(11,true),(15,true),(24,false),(29,false)]
theorem inputList1168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1168 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1168 (by decide) v hb
mask_input "1168|553648128|1208925819614629174741128"
end Percolation.MaskChain
