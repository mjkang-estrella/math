import Inputs013
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_1217 : CNF.NClause := [(81,true),(1,false),(9,false),(12,false),(15,false),(23,false),(28,false)]
theorem inp_1217 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1217 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1217 (by decide) v h
def cl_1218 : CNF.NClause := [(81,true),(1,true),(9,false),(12,false),(15,false),(23,false),(28,false)]
theorem inp_1218 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1218 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1218 (by decide) v h
def cl_1219 : CNF.NClause := [(81,true),(1,false),(9,true),(12,false),(15,false),(23,false),(28,false)]
theorem inp_1219 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1219 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1219 (by decide) v h
def cl_1220 : CNF.NClause := [(81,true),(1,true),(9,true),(12,false),(15,false),(23,false),(28,false)]
theorem inp_1220 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1220 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1220 (by decide) v h
def cl_1221 : CNF.NClause := [(81,true),(1,false),(9,false),(12,true),(15,false),(23,false),(28,false)]
theorem inp_1221 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1221 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1221 (by decide) v h
def cl_1222 : CNF.NClause := [(81,true),(1,true),(9,false),(12,true),(15,false),(23,false),(28,false)]
theorem inp_1222 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1222 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1222 (by decide) v h
def cl_1223 : CNF.NClause := [(81,true),(1,false),(9,true),(12,true),(15,false),(23,false),(28,false)]
theorem inp_1223 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1223 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1223 (by decide) v h
def cl_1224 : CNF.NClause := [(81,true),(1,true),(9,true),(12,true),(15,false),(23,false),(28,false)]
theorem inp_1224 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1224 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1224 (by decide) v h
def cl_1225 : CNF.NClause := [(81,true),(1,false),(9,false),(12,false),(15,true),(23,false),(28,false)]
theorem inp_1225 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1225 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1225 (by decide) v h
def cl_1226 : CNF.NClause := [(81,true),(1,true),(9,false),(12,false),(15,true),(23,false),(28,false)]
theorem inp_1226 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1226 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1226 (by decide) v h
def cl_1227 : CNF.NClause := [(81,true),(1,false),(9,true),(12,false),(15,true),(23,false),(28,false)]
theorem inp_1227 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1227 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1227 (by decide) v h
def cl_1228 : CNF.NClause := [(81,true),(1,true),(9,true),(12,false),(15,true),(23,false),(28,false)]
theorem inp_1228 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1228 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1228 (by decide) v h
def cl_1229 : CNF.NClause := [(81,true),(1,false),(9,false),(12,true),(15,true),(23,false),(28,false)]
theorem inp_1229 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1229 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1229 (by decide) v h
def cl_1230 : CNF.NClause := [(81,true),(1,true),(9,false),(12,true),(15,true),(23,false),(28,false)]
theorem inp_1230 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1230 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1230 (by decide) v h
def cl_1231 : CNF.NClause := [(81,true),(1,false),(9,true),(12,true),(15,true),(23,false),(28,false)]
theorem inp_1231 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1231 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1231 (by decide) v h
def cl_1232 : CNF.NClause := [(81,true),(1,true),(9,true),(12,true),(15,true),(23,false),(28,false)]
theorem inp_1232 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1232 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1232 (by decide) v h
def cl_1233 : CNF.NClause := [(81,true),(1,false),(9,false),(12,false),(15,false),(23,true),(28,false)]
theorem inp_1233 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1233 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1233 (by decide) v h
def cl_1234 : CNF.NClause := [(81,true),(1,true),(9,false),(12,false),(15,false),(23,true),(28,false)]
theorem inp_1234 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1234 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1234 (by decide) v h
def cl_1235 : CNF.NClause := [(81,true),(1,false),(9,true),(12,false),(15,false),(23,true),(28,false)]
theorem inp_1235 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1235 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1235 (by decide) v h
def cl_1236 : CNF.NClause := [(81,true),(1,true),(9,true),(12,false),(15,false),(23,true),(28,false)]
theorem inp_1236 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1236 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1236 (by decide) v h
def cl_1237 : CNF.NClause := [(81,true),(1,false),(9,false),(12,true),(15,false),(23,true),(28,false)]
theorem inp_1237 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1237 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1237 (by decide) v h
def cl_1238 : CNF.NClause := [(81,true),(1,true),(9,false),(12,true),(15,false),(23,true),(28,false)]
theorem inp_1238 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1238 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1238 (by decide) v h
def cl_1239 : CNF.NClause := [(81,true),(1,false),(9,true),(12,true),(15,false),(23,true),(28,false)]
theorem inp_1239 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1239 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1239 (by decide) v h
def cl_1240 : CNF.NClause := [(81,true),(1,true),(9,true),(12,true),(15,false),(23,true),(28,false)]
theorem inp_1240 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1240 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1240 (by decide) v h
def cl_1241 : CNF.NClause := [(81,true),(1,false),(9,false),(12,false),(15,true),(23,true),(28,false)]
theorem inp_1241 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1241 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1241 (by decide) v h
def cl_1242 : CNF.NClause := [(81,true),(1,true),(9,false),(12,false),(15,true),(23,true),(28,false)]
theorem inp_1242 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1242 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1242 (by decide) v h
def cl_1243 : CNF.NClause := [(81,true),(1,false),(9,true),(12,false),(15,true),(23,true),(28,false)]
theorem inp_1243 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1243 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1243 (by decide) v h
def cl_1244 : CNF.NClause := [(81,true),(1,true),(9,true),(12,false),(15,true),(23,true),(28,false)]
theorem inp_1244 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1244 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1244 (by decide) v h
def cl_1245 : CNF.NClause := [(81,true),(1,false),(9,false),(12,true),(15,true),(23,true),(28,false)]
theorem inp_1245 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1245 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1245 (by decide) v h
def cl_1246 : CNF.NClause := [(81,true),(1,true),(9,false),(12,true),(15,true),(23,true),(28,false)]
theorem inp_1246 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1246 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1246 (by decide) v h
def cl_1247 : CNF.NClause := [(81,true),(1,false),(9,true),(12,true),(15,true),(23,true),(28,false)]
theorem inp_1247 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1247 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1247 (by decide) v h
def cl_1249 : CNF.NClause := [(81,true),(1,false),(9,false),(12,false),(15,false),(23,false),(28,true)]
theorem inp_1249 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1249 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1249 (by decide) v h
def cl_1250 : CNF.NClause := [(81,true),(1,true),(9,false),(12,false),(15,false),(23,false),(28,true)]
theorem inp_1250 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1250 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1250 (by decide) v h
def cl_1251 : CNF.NClause := [(81,true),(1,false),(9,true),(12,false),(15,false),(23,false),(28,true)]
theorem inp_1251 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1251 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1251 (by decide) v h
def cl_1252 : CNF.NClause := [(81,true),(1,true),(9,true),(12,false),(15,false),(23,false),(28,true)]
theorem inp_1252 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1252 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1252 (by decide) v h
def cl_1253 : CNF.NClause := [(81,true),(1,false),(9,false),(12,true),(15,false),(23,false),(28,true)]
theorem inp_1253 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1253 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1253 (by decide) v h
def cl_1254 : CNF.NClause := [(81,true),(1,true),(9,false),(12,true),(15,false),(23,false),(28,true)]
theorem inp_1254 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1254 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1254 (by decide) v h
def cl_1255 : CNF.NClause := [(81,true),(1,false),(9,true),(12,true),(15,false),(23,false),(28,true)]
theorem inp_1255 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1255 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1255 (by decide) v h
def cl_1256 : CNF.NClause := [(81,true),(1,true),(9,true),(12,true),(15,false),(23,false),(28,true)]
theorem inp_1256 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1256 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1256 (by decide) v h
def cl_1257 : CNF.NClause := [(81,true),(1,false),(9,false),(12,false),(15,true),(23,false),(28,true)]
theorem inp_1257 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1257 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1257 (by decide) v h
def cl_1258 : CNF.NClause := [(81,true),(1,true),(9,false),(12,false),(15,true),(23,false),(28,true)]
theorem inp_1258 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1258 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1258 (by decide) v h
def cl_1259 : CNF.NClause := [(81,true),(1,false),(9,true),(12,false),(15,true),(23,false),(28,true)]
theorem inp_1259 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1259 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1259 (by decide) v h
def cl_1260 : CNF.NClause := [(81,true),(1,true),(9,true),(12,false),(15,true),(23,false),(28,true)]
theorem inp_1260 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1260 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1260 (by decide) v h
def cl_1261 : CNF.NClause := [(81,true),(1,false),(9,false),(12,true),(15,true),(23,false),(28,true)]
theorem inp_1261 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1261 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1261 (by decide) v h
def cl_1262 : CNF.NClause := [(81,true),(1,true),(9,false),(12,true),(15,true),(23,false),(28,true)]
theorem inp_1262 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1262 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1262 (by decide) v h
def cl_1263 : CNF.NClause := [(81,true),(1,false),(9,true),(12,true),(15,true),(23,false),(28,true)]
theorem inp_1263 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1263 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1263 (by decide) v h
def cl_1265 : CNF.NClause := [(81,true),(1,false),(9,false),(12,false),(15,false),(23,true),(28,true)]
theorem inp_1265 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1265 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1265 (by decide) v h
def cl_1266 : CNF.NClause := [(81,true),(1,true),(9,false),(12,false),(15,false),(23,true),(28,true)]
theorem inp_1266 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1266 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1266 (by decide) v h
def cl_1267 : CNF.NClause := [(81,true),(1,false),(9,true),(12,false),(15,false),(23,true),(28,true)]
theorem inp_1267 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1267 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1267 (by decide) v h
def cl_1268 : CNF.NClause := [(81,true),(1,true),(9,true),(12,false),(15,false),(23,true),(28,true)]
theorem inp_1268 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1268 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1268 (by decide) v h
end Percolation.Replay
