import NInputs016
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_1126 : CNF.NClause := [(79,true),(2,true),(8,false),(14,true),(15,false),(21,false),(26,true)]
theorem inp_1126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1126 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1126 v hb
def cl_1127 : CNF.NClause := [(79,true),(2,false),(8,true),(14,true),(15,false),(21,false),(26,true)]
theorem inp_1127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1127 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1127 v hb
def cl_1128 : CNF.NClause := [(79,true),(2,true),(8,true),(14,true),(15,false),(21,false),(26,true)]
theorem inp_1128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1128 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1128 v hb
def cl_1129 : CNF.NClause := [(79,true),(2,false),(8,false),(14,false),(15,true),(21,false),(26,true)]
theorem inp_1129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1129 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1129 v hb
def cl_1130 : CNF.NClause := [(79,true),(2,true),(8,false),(14,false),(15,true),(21,false),(26,true)]
theorem inp_1130 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1130 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1130 v hb
def cl_1131 : CNF.NClause := [(79,true),(2,false),(8,true),(14,false),(15,true),(21,false),(26,true)]
theorem inp_1131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1131 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1131 v hb
def cl_1132 : CNF.NClause := [(79,true),(2,true),(8,true),(14,false),(15,true),(21,false),(26,true)]
theorem inp_1132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1132 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1132 (by decide) v hb
def cl_1133 : CNF.NClause := [(79,true),(2,false),(8,false),(14,true),(15,true),(21,false),(26,true)]
theorem inp_1133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1133 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1133 (by decide) v hb
def cl_1134 : CNF.NClause := [(79,true),(2,true),(8,false),(14,true),(15,true),(21,false),(26,true)]
theorem inp_1134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1134 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1134 (by decide) v hb
def cl_1135 : CNF.NClause := [(79,true),(2,false),(8,true),(14,true),(15,true),(21,false),(26,true)]
theorem inp_1135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1135 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1135 v hb
def cl_1136 : CNF.NClause := [(79,false),(2,true),(8,true),(14,true),(15,true),(21,false),(26,true)]
theorem inp_1136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1136 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1136 v hb
def cl_1137 : CNF.NClause := [(79,true),(2,false),(8,false),(14,false),(15,false),(21,true),(26,true)]
theorem inp_1137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1137 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1137 (by decide) v hb
def cl_1138 : CNF.NClause := [(79,true),(2,true),(8,false),(14,false),(15,false),(21,true),(26,true)]
theorem inp_1138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1138 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1138 (by decide) v hb
def cl_1139 : CNF.NClause := [(79,true),(2,false),(8,true),(14,false),(15,false),(21,true),(26,true)]
theorem inp_1139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1139 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1139 v hb
def cl_1140 : CNF.NClause := [(79,true),(2,true),(8,true),(14,false),(15,false),(21,true),(26,true)]
theorem inp_1140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1140 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1140 v hb
def cl_1141 : CNF.NClause := [(79,true),(2,false),(8,false),(14,true),(15,false),(21,true),(26,true)]
theorem inp_1141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1141 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1141 (by decide) v hb
def cl_1142 : CNF.NClause := [(79,true),(2,true),(8,false),(14,true),(15,false),(21,true),(26,true)]
theorem inp_1142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1142 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1142 (by decide) v hb
def cl_1143 : CNF.NClause := [(79,true),(2,false),(8,true),(14,true),(15,false),(21,true),(26,true)]
theorem inp_1143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1143 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1143 v hb
def cl_1144 : CNF.NClause := [(79,false),(2,true),(8,true),(14,true),(15,false),(21,true),(26,true)]
theorem inp_1144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1144 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1144 v hb
def cl_1145 : CNF.NClause := [(79,true),(2,false),(8,false),(14,false),(15,true),(21,true),(26,true)]
theorem inp_1145 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1145 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1145 (by decide) v hb
def cl_1146 : CNF.NClause := [(79,true),(2,true),(8,false),(14,false),(15,true),(21,true),(26,true)]
theorem inp_1146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1146 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1146 (by decide) v hb
def cl_1147 : CNF.NClause := [(79,true),(2,false),(8,true),(14,false),(15,true),(21,true),(26,true)]
theorem inp_1147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1147 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1147 v hb
def cl_1148 : CNF.NClause := [(79,false),(2,true),(8,true),(14,false),(15,true),(21,true),(26,true)]
theorem inp_1148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1148 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1148 v hb
def cl_1149 : CNF.NClause := [(79,true),(2,false),(8,false),(14,true),(15,true),(21,true),(26,true)]
theorem inp_1149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1149 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1149 (by decide) v hb
def cl_1150 : CNF.NClause := [(79,false),(2,true),(8,false),(14,true),(15,true),(21,true),(26,true)]
theorem inp_1150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1150 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1150 v hb
def cl_1151 : CNF.NClause := [(79,false),(2,false),(8,true),(14,true),(15,true),(21,true),(26,true)]
theorem inp_1151 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1151 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1151 v hb
def cl_1153 : CNF.NClause := [(80,true),(3,false),(7,false),(11,false),(15,false),(24,false),(29,false)]
theorem inp_1153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1153 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1153 v hb
def cl_1154 : CNF.NClause := [(80,true),(3,true),(7,false),(11,false),(15,false),(24,false),(29,false)]
theorem inp_1154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1154 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1154 v hb
def cl_1155 : CNF.NClause := [(80,true),(3,false),(7,true),(11,false),(15,false),(24,false),(29,false)]
theorem inp_1155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1155 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1155 v hb
def cl_1156 : CNF.NClause := [(80,true),(3,true),(7,true),(11,false),(15,false),(24,false),(29,false)]
theorem inp_1156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1156 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1156 v hb
def cl_1157 : CNF.NClause := [(80,true),(3,false),(7,false),(11,true),(15,false),(24,false),(29,false)]
theorem inp_1157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1157 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1157 v hb
def cl_1158 : CNF.NClause := [(80,true),(3,true),(7,false),(11,true),(15,false),(24,false),(29,false)]
theorem inp_1158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1158 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1158 v hb
def cl_1159 : CNF.NClause := [(80,true),(3,false),(7,true),(11,true),(15,false),(24,false),(29,false)]
theorem inp_1159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1159 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1159 v hb
def cl_1160 : CNF.NClause := [(80,true),(3,true),(7,true),(11,true),(15,false),(24,false),(29,false)]
theorem inp_1160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1160 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1160 v hb
def cl_1161 : CNF.NClause := [(80,true),(3,false),(7,false),(11,false),(15,true),(24,false),(29,false)]
theorem inp_1161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1161 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1161 (by decide) v hb
def cl_1162 : CNF.NClause := [(80,true),(3,true),(7,false),(11,false),(15,true),(24,false),(29,false)]
theorem inp_1162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1162 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1162 (by decide) v hb
def cl_1163 : CNF.NClause := [(80,true),(3,false),(7,true),(11,false),(15,true),(24,false),(29,false)]
theorem inp_1163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1163 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1163 v hb
def cl_1164 : CNF.NClause := [(80,true),(3,true),(7,true),(11,false),(15,true),(24,false),(29,false)]
theorem inp_1164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1164 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1164 v hb
def cl_1165 : CNF.NClause := [(80,true),(3,false),(7,false),(11,true),(15,true),(24,false),(29,false)]
theorem inp_1165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1165 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1165 (by decide) v hb
def cl_1166 : CNF.NClause := [(80,true),(3,true),(7,false),(11,true),(15,true),(24,false),(29,false)]
theorem inp_1166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1166 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1166 (by decide) v hb
def cl_1167 : CNF.NClause := [(80,true),(3,false),(7,true),(11,true),(15,true),(24,false),(29,false)]
theorem inp_1167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1167 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1167 v hb
def cl_1168 : CNF.NClause := [(80,true),(3,true),(7,true),(11,true),(15,true),(24,false),(29,false)]
theorem inp_1168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1168 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1168 v hb
def cl_1169 : CNF.NClause := [(80,true),(3,false),(7,false),(11,false),(15,false),(24,true),(29,false)]
theorem inp_1169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1169 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1169 (by decide) v hb
def cl_1170 : CNF.NClause := [(80,true),(3,true),(7,false),(11,false),(15,false),(24,true),(29,false)]
theorem inp_1170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1170 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1170 (by decide) v hb
def cl_1171 : CNF.NClause := [(80,true),(3,false),(7,true),(11,false),(15,false),(24,true),(29,false)]
theorem inp_1171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1171 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1171 v hb
def cl_1172 : CNF.NClause := [(80,true),(3,true),(7,true),(11,false),(15,false),(24,true),(29,false)]
theorem inp_1172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1172 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1172 v hb
def cl_1173 : CNF.NClause := [(80,true),(3,false),(7,false),(11,true),(15,false),(24,true),(29,false)]
theorem inp_1173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1173 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1173 (by decide) v hb
def cl_1174 : CNF.NClause := [(80,true),(3,true),(7,false),(11,true),(15,false),(24,true),(29,false)]
theorem inp_1174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1174 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1174 (by decide) v hb
def cl_1175 : CNF.NClause := [(80,true),(3,false),(7,true),(11,true),(15,false),(24,true),(29,false)]
theorem inp_1175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1175 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1175 v hb
def cl_1176 : CNF.NClause := [(80,true),(3,true),(7,true),(11,true),(15,false),(24,true),(29,false)]
theorem inp_1176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1176 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1176 v hb
end Percolation.NReplay
