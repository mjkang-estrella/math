import NInputs017
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_1177 : CNF.NClause := [(80,true),(3,false),(7,false),(11,false),(15,true),(24,true),(29,false)]
theorem inp_1177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1177 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1177 (by decide) v hb
def cl_1178 : CNF.NClause := [(80,true),(3,true),(7,false),(11,false),(15,true),(24,true),(29,false)]
theorem inp_1178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1178 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1178 (by decide) v hb
def cl_1179 : CNF.NClause := [(80,true),(3,false),(7,true),(11,false),(15,true),(24,true),(29,false)]
theorem inp_1179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1179 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1179 v hb
def cl_1180 : CNF.NClause := [(80,true),(3,true),(7,true),(11,false),(15,true),(24,true),(29,false)]
theorem inp_1180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1180 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1180 v hb
def cl_1181 : CNF.NClause := [(80,true),(3,false),(7,false),(11,true),(15,true),(24,true),(29,false)]
theorem inp_1181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1181 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1181 (by decide) v hb
def cl_1182 : CNF.NClause := [(80,true),(3,true),(7,false),(11,true),(15,true),(24,true),(29,false)]
theorem inp_1182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1182 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1182 (by decide) v hb
def cl_1183 : CNF.NClause := [(80,true),(3,false),(7,true),(11,true),(15,true),(24,true),(29,false)]
theorem inp_1183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1183 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1183 v hb
def cl_1184 : CNF.NClause := [(80,false),(3,true),(7,true),(11,true),(15,true),(24,true),(29,false)]
theorem inp_1184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1184 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1184 v hb
def cl_1185 : CNF.NClause := [(80,true),(3,false),(7,false),(11,false),(15,false),(24,false),(29,true)]
theorem inp_1185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1185 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1185 v hb
def cl_1186 : CNF.NClause := [(80,true),(3,true),(7,false),(11,false),(15,false),(24,false),(29,true)]
theorem inp_1186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1186 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1186 (by decide) v hb
def cl_1187 : CNF.NClause := [(80,true),(3,false),(7,true),(11,false),(15,false),(24,false),(29,true)]
theorem inp_1187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1187 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1187 v hb
def cl_1188 : CNF.NClause := [(80,true),(3,true),(7,true),(11,false),(15,false),(24,false),(29,true)]
theorem inp_1188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1188 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1188 v hb
def cl_1189 : CNF.NClause := [(80,true),(3,false),(7,false),(11,true),(15,false),(24,false),(29,true)]
theorem inp_1189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1189 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1189 (by decide) v hb
def cl_1190 : CNF.NClause := [(80,true),(3,true),(7,false),(11,true),(15,false),(24,false),(29,true)]
theorem inp_1190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1190 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1190 (by decide) v hb
def cl_1191 : CNF.NClause := [(80,true),(3,false),(7,true),(11,true),(15,false),(24,false),(29,true)]
theorem inp_1191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1191 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1191 v hb
def cl_1192 : CNF.NClause := [(80,true),(3,true),(7,true),(11,true),(15,false),(24,false),(29,true)]
theorem inp_1192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1192 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1192 v hb
def cl_1193 : CNF.NClause := [(80,true),(3,false),(7,false),(11,false),(15,true),(24,false),(29,true)]
theorem inp_1193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1193 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1193 v hb
def cl_1194 : CNF.NClause := [(80,true),(3,true),(7,false),(11,false),(15,true),(24,false),(29,true)]
theorem inp_1194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1194 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1194 (by decide) v hb
def cl_1195 : CNF.NClause := [(80,true),(3,false),(7,true),(11,false),(15,true),(24,false),(29,true)]
theorem inp_1195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1195 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1195 v hb
def cl_1196 : CNF.NClause := [(80,true),(3,true),(7,true),(11,false),(15,true),(24,false),(29,true)]
theorem inp_1196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1196 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1196 v hb
def cl_1197 : CNF.NClause := [(80,true),(3,false),(7,false),(11,true),(15,true),(24,false),(29,true)]
theorem inp_1197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1197 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1197 (by decide) v hb
def cl_1198 : CNF.NClause := [(80,true),(3,true),(7,false),(11,true),(15,true),(24,false),(29,true)]
theorem inp_1198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1198 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1198 (by decide) v hb
def cl_1199 : CNF.NClause := [(80,true),(3,false),(7,true),(11,true),(15,true),(24,false),(29,true)]
theorem inp_1199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1199 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1199 v hb
def cl_1200 : CNF.NClause := [(80,false),(3,true),(7,true),(11,true),(15,true),(24,false),(29,true)]
theorem inp_1200 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1200 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1200 v hb
def cl_1201 : CNF.NClause := [(80,true),(3,false),(7,false),(11,false),(15,false),(24,true),(29,true)]
theorem inp_1201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1201 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1201 v hb
def cl_1202 : CNF.NClause := [(80,true),(3,true),(7,false),(11,false),(15,false),(24,true),(29,true)]
theorem inp_1202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1202 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1202 v hb
def cl_1203 : CNF.NClause := [(80,true),(3,false),(7,true),(11,false),(15,false),(24,true),(29,true)]
theorem inp_1203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1203 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1203 v hb
def cl_1204 : CNF.NClause := [(80,true),(3,true),(7,true),(11,false),(15,false),(24,true),(29,true)]
theorem inp_1204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1204 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1204 v hb
def cl_1205 : CNF.NClause := [(80,true),(3,false),(7,false),(11,true),(15,false),(24,true),(29,true)]
theorem inp_1205 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1205 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1205 (by decide) v hb
def cl_1206 : CNF.NClause := [(80,true),(3,true),(7,false),(11,true),(15,false),(24,true),(29,true)]
theorem inp_1206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1206 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1206 (by decide) v hb
def cl_1207 : CNF.NClause := [(80,true),(3,false),(7,true),(11,true),(15,false),(24,true),(29,true)]
theorem inp_1207 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1207 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1207 v hb
def cl_1208 : CNF.NClause := [(80,false),(3,true),(7,true),(11,true),(15,false),(24,true),(29,true)]
theorem inp_1208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1208 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1208 v hb
def cl_1209 : CNF.NClause := [(80,true),(3,false),(7,false),(11,false),(15,true),(24,true),(29,true)]
theorem inp_1209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1209 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1209 v hb
def cl_1210 : CNF.NClause := [(80,true),(3,true),(7,false),(11,false),(15,true),(24,true),(29,true)]
theorem inp_1210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1210 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1210 v hb
def cl_1211 : CNF.NClause := [(80,true),(3,false),(7,true),(11,false),(15,true),(24,true),(29,true)]
theorem inp_1211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1211 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1211 v hb
def cl_1212 : CNF.NClause := [(80,false),(3,true),(7,true),(11,false),(15,true),(24,true),(29,true)]
theorem inp_1212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1212 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1212 v hb
def cl_1213 : CNF.NClause := [(80,true),(3,false),(7,false),(11,true),(15,true),(24,true),(29,true)]
theorem inp_1213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1213 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) cl_1213 (by decide) v hb
def cl_1214 : CNF.NClause := [(80,false),(3,true),(7,false),(11,true),(15,true),(24,true),(29,true)]
theorem inp_1214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1214 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1214 v hb
def cl_1215 : CNF.NClause := [(80,false),(3,false),(7,true),(11,true),(15,true),(24,true),(29,true)]
theorem inp_1215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1215 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1215 v hb
def cl_1216 : CNF.NClause := [(80,false),(3,true),(7,true),(11,true),(15,true),(24,true),(29,true)]
theorem inp_1216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1216 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1216 v hb
def cl_1217 : CNF.NClause := [(81,true),(1,false),(9,false),(12,false),(15,false),(23,false),(28,false)]
theorem inp_1217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1217 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1217 v hb
def cl_1218 : CNF.NClause := [(81,true),(1,true),(9,false),(12,false),(15,false),(23,false),(28,false)]
theorem inp_1218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1218 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1218 v hb
def cl_1219 : CNF.NClause := [(81,true),(1,false),(9,true),(12,false),(15,false),(23,false),(28,false)]
theorem inp_1219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1219 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1219 v hb
def cl_1220 : CNF.NClause := [(81,true),(1,true),(9,true),(12,false),(15,false),(23,false),(28,false)]
theorem inp_1220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1220 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1220 v hb
def cl_1221 : CNF.NClause := [(81,true),(1,false),(9,false),(12,true),(15,false),(23,false),(28,false)]
theorem inp_1221 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1221 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1221 v hb
def cl_1222 : CNF.NClause := [(81,true),(1,true),(9,false),(12,true),(15,false),(23,false),(28,false)]
theorem inp_1222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1222 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1222 v hb
def cl_1223 : CNF.NClause := [(81,true),(1,false),(9,true),(12,true),(15,false),(23,false),(28,false)]
theorem inp_1223 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1223 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1223 v hb
def cl_1224 : CNF.NClause := [(81,true),(1,true),(9,true),(12,true),(15,false),(23,false),(28,false)]
theorem inp_1224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1224 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1224 v hb
def cl_1225 : CNF.NClause := [(81,true),(1,false),(9,false),(12,false),(15,true),(23,false),(28,false)]
theorem inp_1225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1225 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1225 v hb
def cl_1226 : CNF.NClause := [(81,true),(1,true),(9,false),(12,false),(15,true),(23,false),(28,false)]
theorem inp_1226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1226 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1226 v hb
end Percolation.NReplay
