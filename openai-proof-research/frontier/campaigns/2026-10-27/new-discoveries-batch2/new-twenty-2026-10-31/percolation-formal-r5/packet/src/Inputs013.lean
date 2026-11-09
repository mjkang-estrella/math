import Inputs012
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_1143 : CNF.NClause := [(79,true),(2,false),(8,true),(14,true),(15,false),(21,true),(26,true)]
theorem inp_1143 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1143 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1143 (by decide) v h
def cl_1144 : CNF.NClause := [(79,false),(2,true),(8,true),(14,true),(15,false),(21,true),(26,true)]
theorem inp_1144 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1144 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1144 (by decide) v h
def cl_1147 : CNF.NClause := [(79,true),(2,false),(8,true),(14,false),(15,true),(21,true),(26,true)]
theorem inp_1147 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1147 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1147 (by decide) v h
def cl_1148 : CNF.NClause := [(79,false),(2,true),(8,true),(14,false),(15,true),(21,true),(26,true)]
theorem inp_1148 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1148 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1148 (by decide) v h
def cl_1150 : CNF.NClause := [(79,false),(2,true),(8,false),(14,true),(15,true),(21,true),(26,true)]
theorem inp_1150 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1150 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1150 (by decide) v h
def cl_1151 : CNF.NClause := [(79,false),(2,false),(8,true),(14,true),(15,true),(21,true),(26,true)]
theorem inp_1151 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1151 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1151 (by decide) v h
def cl_1152 : CNF.NClause := [(79,false),(2,true),(8,true),(14,true),(15,true),(21,true),(26,true)]
theorem inp_1152 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1152 := by
  exact input_gate (activationGate5 SatVar.a (.i 17) 17) (activationA_mem 17) cl_1152 (by decide) v h
def cl_1153 : CNF.NClause := [(80,true),(3,false),(7,false),(11,false),(15,false),(24,false),(29,false)]
theorem inp_1153 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1153 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1153 (by decide) v h
def cl_1154 : CNF.NClause := [(80,true),(3,true),(7,false),(11,false),(15,false),(24,false),(29,false)]
theorem inp_1154 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1154 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1154 (by decide) v h
def cl_1155 : CNF.NClause := [(80,true),(3,false),(7,true),(11,false),(15,false),(24,false),(29,false)]
theorem inp_1155 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1155 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1155 (by decide) v h
def cl_1156 : CNF.NClause := [(80,true),(3,true),(7,true),(11,false),(15,false),(24,false),(29,false)]
theorem inp_1156 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1156 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1156 (by decide) v h
def cl_1157 : CNF.NClause := [(80,true),(3,false),(7,false),(11,true),(15,false),(24,false),(29,false)]
theorem inp_1157 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1157 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1157 (by decide) v h
def cl_1158 : CNF.NClause := [(80,true),(3,true),(7,false),(11,true),(15,false),(24,false),(29,false)]
theorem inp_1158 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1158 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1158 (by decide) v h
def cl_1159 : CNF.NClause := [(80,true),(3,false),(7,true),(11,true),(15,false),(24,false),(29,false)]
theorem inp_1159 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1159 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1159 (by decide) v h
def cl_1160 : CNF.NClause := [(80,true),(3,true),(7,true),(11,true),(15,false),(24,false),(29,false)]
theorem inp_1160 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1160 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1160 (by decide) v h
def cl_1163 : CNF.NClause := [(80,true),(3,false),(7,true),(11,false),(15,true),(24,false),(29,false)]
theorem inp_1163 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1163 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1163 (by decide) v h
def cl_1164 : CNF.NClause := [(80,true),(3,true),(7,true),(11,false),(15,true),(24,false),(29,false)]
theorem inp_1164 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1164 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1164 (by decide) v h
def cl_1167 : CNF.NClause := [(80,true),(3,false),(7,true),(11,true),(15,true),(24,false),(29,false)]
theorem inp_1167 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1167 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1167 (by decide) v h
def cl_1168 : CNF.NClause := [(80,true),(3,true),(7,true),(11,true),(15,true),(24,false),(29,false)]
theorem inp_1168 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1168 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1168 (by decide) v h
def cl_1171 : CNF.NClause := [(80,true),(3,false),(7,true),(11,false),(15,false),(24,true),(29,false)]
theorem inp_1171 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1171 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1171 (by decide) v h
def cl_1172 : CNF.NClause := [(80,true),(3,true),(7,true),(11,false),(15,false),(24,true),(29,false)]
theorem inp_1172 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1172 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1172 (by decide) v h
def cl_1175 : CNF.NClause := [(80,true),(3,false),(7,true),(11,true),(15,false),(24,true),(29,false)]
theorem inp_1175 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1175 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1175 (by decide) v h
def cl_1176 : CNF.NClause := [(80,true),(3,true),(7,true),(11,true),(15,false),(24,true),(29,false)]
theorem inp_1176 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1176 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1176 (by decide) v h
def cl_1179 : CNF.NClause := [(80,true),(3,false),(7,true),(11,false),(15,true),(24,true),(29,false)]
theorem inp_1179 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1179 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1179 (by decide) v h
def cl_1180 : CNF.NClause := [(80,true),(3,true),(7,true),(11,false),(15,true),(24,true),(29,false)]
theorem inp_1180 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1180 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1180 (by decide) v h
def cl_1183 : CNF.NClause := [(80,true),(3,false),(7,true),(11,true),(15,true),(24,true),(29,false)]
theorem inp_1183 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1183 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1183 (by decide) v h
def cl_1184 : CNF.NClause := [(80,false),(3,true),(7,true),(11,true),(15,true),(24,true),(29,false)]
theorem inp_1184 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1184 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1184 (by decide) v h
def cl_1185 : CNF.NClause := [(80,true),(3,false),(7,false),(11,false),(15,false),(24,false),(29,true)]
theorem inp_1185 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1185 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1185 (by decide) v h
def cl_1187 : CNF.NClause := [(80,true),(3,false),(7,true),(11,false),(15,false),(24,false),(29,true)]
theorem inp_1187 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1187 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1187 (by decide) v h
def cl_1188 : CNF.NClause := [(80,true),(3,true),(7,true),(11,false),(15,false),(24,false),(29,true)]
theorem inp_1188 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1188 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1188 (by decide) v h
def cl_1191 : CNF.NClause := [(80,true),(3,false),(7,true),(11,true),(15,false),(24,false),(29,true)]
theorem inp_1191 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1191 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1191 (by decide) v h
def cl_1192 : CNF.NClause := [(80,true),(3,true),(7,true),(11,true),(15,false),(24,false),(29,true)]
theorem inp_1192 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1192 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1192 (by decide) v h
def cl_1193 : CNF.NClause := [(80,true),(3,false),(7,false),(11,false),(15,true),(24,false),(29,true)]
theorem inp_1193 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1193 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1193 (by decide) v h
def cl_1195 : CNF.NClause := [(80,true),(3,false),(7,true),(11,false),(15,true),(24,false),(29,true)]
theorem inp_1195 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1195 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1195 (by decide) v h
def cl_1196 : CNF.NClause := [(80,true),(3,true),(7,true),(11,false),(15,true),(24,false),(29,true)]
theorem inp_1196 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1196 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1196 (by decide) v h
def cl_1199 : CNF.NClause := [(80,true),(3,false),(7,true),(11,true),(15,true),(24,false),(29,true)]
theorem inp_1199 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1199 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1199 (by decide) v h
def cl_1200 : CNF.NClause := [(80,false),(3,true),(7,true),(11,true),(15,true),(24,false),(29,true)]
theorem inp_1200 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1200 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1200 (by decide) v h
def cl_1201 : CNF.NClause := [(80,true),(3,false),(7,false),(11,false),(15,false),(24,true),(29,true)]
theorem inp_1201 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1201 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1201 (by decide) v h
def cl_1202 : CNF.NClause := [(80,true),(3,true),(7,false),(11,false),(15,false),(24,true),(29,true)]
theorem inp_1202 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1202 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1202 (by decide) v h
def cl_1203 : CNF.NClause := [(80,true),(3,false),(7,true),(11,false),(15,false),(24,true),(29,true)]
theorem inp_1203 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1203 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1203 (by decide) v h
def cl_1204 : CNF.NClause := [(80,true),(3,true),(7,true),(11,false),(15,false),(24,true),(29,true)]
theorem inp_1204 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1204 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1204 (by decide) v h
def cl_1207 : CNF.NClause := [(80,true),(3,false),(7,true),(11,true),(15,false),(24,true),(29,true)]
theorem inp_1207 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1207 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1207 (by decide) v h
def cl_1208 : CNF.NClause := [(80,false),(3,true),(7,true),(11,true),(15,false),(24,true),(29,true)]
theorem inp_1208 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1208 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1208 (by decide) v h
def cl_1209 : CNF.NClause := [(80,true),(3,false),(7,false),(11,false),(15,true),(24,true),(29,true)]
theorem inp_1209 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1209 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1209 (by decide) v h
def cl_1210 : CNF.NClause := [(80,true),(3,true),(7,false),(11,false),(15,true),(24,true),(29,true)]
theorem inp_1210 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1210 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1210 (by decide) v h
def cl_1211 : CNF.NClause := [(80,true),(3,false),(7,true),(11,false),(15,true),(24,true),(29,true)]
theorem inp_1211 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1211 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1211 (by decide) v h
def cl_1212 : CNF.NClause := [(80,false),(3,true),(7,true),(11,false),(15,true),(24,true),(29,true)]
theorem inp_1212 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1212 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1212 (by decide) v h
def cl_1214 : CNF.NClause := [(80,false),(3,true),(7,false),(11,true),(15,true),(24,true),(29,true)]
theorem inp_1214 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1214 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1214 (by decide) v h
def cl_1215 : CNF.NClause := [(80,false),(3,false),(7,true),(11,true),(15,true),(24,true),(29,true)]
theorem inp_1215 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1215 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1215 (by decide) v h
def cl_1216 : CNF.NClause := [(80,false),(3,true),(7,true),(11,true),(15,true),(24,true),(29,true)]
theorem inp_1216 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1216 := by
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1216 (by decide) v h
end Percolation.Replay
