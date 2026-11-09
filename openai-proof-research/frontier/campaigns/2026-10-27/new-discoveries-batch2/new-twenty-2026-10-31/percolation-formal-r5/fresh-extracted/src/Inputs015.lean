import Inputs014
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_1269 : CNF.NClause := [(81,true),(1,false),(9,false),(12,true),(15,false),(23,true),(28,true)]
theorem inp_1269 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1269 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1269 (by decide) v h
def cl_1270 : CNF.NClause := [(81,true),(1,true),(9,false),(12,true),(15,false),(23,true),(28,true)]
theorem inp_1270 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1270 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1270 (by decide) v h
def cl_1271 : CNF.NClause := [(81,true),(1,false),(9,true),(12,true),(15,false),(23,true),(28,true)]
theorem inp_1271 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1271 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1271 (by decide) v h
def cl_1272 : CNF.NClause := [(81,false),(1,true),(9,true),(12,true),(15,false),(23,true),(28,true)]
theorem inp_1272 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1272 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1272 (by decide) v h
def cl_1273 : CNF.NClause := [(81,true),(1,false),(9,false),(12,false),(15,true),(23,true),(28,true)]
theorem inp_1273 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1273 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1273 (by decide) v h
def cl_1274 : CNF.NClause := [(81,true),(1,true),(9,false),(12,false),(15,true),(23,true),(28,true)]
theorem inp_1274 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1274 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1274 (by decide) v h
def cl_1275 : CNF.NClause := [(81,true),(1,false),(9,true),(12,false),(15,true),(23,true),(28,true)]
theorem inp_1275 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1275 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1275 (by decide) v h
def cl_1277 : CNF.NClause := [(81,true),(1,false),(9,false),(12,true),(15,true),(23,true),(28,true)]
theorem inp_1277 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1277 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1277 (by decide) v h
def cl_1279 : CNF.NClause := [(81,false),(1,false),(9,true),(12,true),(15,true),(23,true),(28,true)]
theorem inp_1279 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1279 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1279 (by decide) v h
def cl_1280 : CNF.NClause := [(81,false),(1,true),(9,true),(12,true),(15,true),(23,true),(28,true)]
theorem inp_1280 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1280 := by
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1280 (by decide) v h
def cl_1281 : CNF.NClause := [(82,true),(5,false),(6,false),(7,false),(8,false),(9,false),(30,false)]
theorem inp_1281 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1281 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1281 (by decide) v h
def cl_1282 : CNF.NClause := [(82,true),(5,true),(6,false),(7,false),(8,false),(9,false),(30,false)]
theorem inp_1282 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1282 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1282 (by decide) v h
def cl_1283 : CNF.NClause := [(82,true),(5,false),(6,true),(7,false),(8,false),(9,false),(30,false)]
theorem inp_1283 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1283 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1283 (by decide) v h
def cl_1284 : CNF.NClause := [(82,true),(5,true),(6,true),(7,false),(8,false),(9,false),(30,false)]
theorem inp_1284 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1284 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1284 (by decide) v h
def cl_1285 : CNF.NClause := [(82,true),(5,false),(6,false),(7,true),(8,false),(9,false),(30,false)]
theorem inp_1285 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1285 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1285 (by decide) v h
def cl_1286 : CNF.NClause := [(82,true),(5,true),(6,false),(7,true),(8,false),(9,false),(30,false)]
theorem inp_1286 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1286 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1286 (by decide) v h
def cl_1287 : CNF.NClause := [(82,true),(5,false),(6,true),(7,true),(8,false),(9,false),(30,false)]
theorem inp_1287 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1287 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1287 (by decide) v h
def cl_1288 : CNF.NClause := [(82,true),(5,true),(6,true),(7,true),(8,false),(9,false),(30,false)]
theorem inp_1288 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1288 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1288 (by decide) v h
def cl_1289 : CNF.NClause := [(82,true),(5,false),(6,false),(7,false),(8,true),(9,false),(30,false)]
theorem inp_1289 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1289 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1289 (by decide) v h
def cl_1290 : CNF.NClause := [(82,true),(5,true),(6,false),(7,false),(8,true),(9,false),(30,false)]
theorem inp_1290 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1290 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1290 (by decide) v h
def cl_1291 : CNF.NClause := [(82,true),(5,false),(6,true),(7,false),(8,true),(9,false),(30,false)]
theorem inp_1291 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1291 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1291 (by decide) v h
def cl_1292 : CNF.NClause := [(82,true),(5,true),(6,true),(7,false),(8,true),(9,false),(30,false)]
theorem inp_1292 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1292 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1292 (by decide) v h
def cl_1293 : CNF.NClause := [(82,true),(5,false),(6,false),(7,true),(8,true),(9,false),(30,false)]
theorem inp_1293 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1293 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1293 (by decide) v h
def cl_1294 : CNF.NClause := [(82,true),(5,true),(6,false),(7,true),(8,true),(9,false),(30,false)]
theorem inp_1294 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1294 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1294 (by decide) v h
def cl_1295 : CNF.NClause := [(82,true),(5,false),(6,true),(7,true),(8,true),(9,false),(30,false)]
theorem inp_1295 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1295 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1295 (by decide) v h
def cl_1296 : CNF.NClause := [(82,true),(5,true),(6,true),(7,true),(8,true),(9,false),(30,false)]
theorem inp_1296 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1296 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1296 (by decide) v h
def cl_1297 : CNF.NClause := [(82,true),(5,false),(6,false),(7,false),(8,false),(9,true),(30,false)]
theorem inp_1297 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1297 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1297 (by decide) v h
def cl_1298 : CNF.NClause := [(82,true),(5,true),(6,false),(7,false),(8,false),(9,true),(30,false)]
theorem inp_1298 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1298 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1298 (by decide) v h
def cl_1299 : CNF.NClause := [(82,true),(5,false),(6,true),(7,false),(8,false),(9,true),(30,false)]
theorem inp_1299 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1299 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1299 (by decide) v h
def cl_1300 : CNF.NClause := [(82,true),(5,true),(6,true),(7,false),(8,false),(9,true),(30,false)]
theorem inp_1300 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1300 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1300 (by decide) v h
def cl_1301 : CNF.NClause := [(82,true),(5,false),(6,false),(7,true),(8,false),(9,true),(30,false)]
theorem inp_1301 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1301 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1301 (by decide) v h
def cl_1302 : CNF.NClause := [(82,true),(5,true),(6,false),(7,true),(8,false),(9,true),(30,false)]
theorem inp_1302 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1302 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1302 (by decide) v h
def cl_1303 : CNF.NClause := [(82,true),(5,false),(6,true),(7,true),(8,false),(9,true),(30,false)]
theorem inp_1303 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1303 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1303 (by decide) v h
def cl_1304 : CNF.NClause := [(82,true),(5,true),(6,true),(7,true),(8,false),(9,true),(30,false)]
theorem inp_1304 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1304 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1304 (by decide) v h
def cl_1305 : CNF.NClause := [(82,true),(5,false),(6,false),(7,false),(8,true),(9,true),(30,false)]
theorem inp_1305 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1305 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1305 (by decide) v h
def cl_1306 : CNF.NClause := [(82,true),(5,true),(6,false),(7,false),(8,true),(9,true),(30,false)]
theorem inp_1306 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1306 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1306 (by decide) v h
def cl_1307 : CNF.NClause := [(82,true),(5,false),(6,true),(7,false),(8,true),(9,true),(30,false)]
theorem inp_1307 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1307 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1307 (by decide) v h
def cl_1308 : CNF.NClause := [(82,true),(5,true),(6,true),(7,false),(8,true),(9,true),(30,false)]
theorem inp_1308 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1308 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1308 (by decide) v h
def cl_1309 : CNF.NClause := [(82,true),(5,false),(6,false),(7,true),(8,true),(9,true),(30,false)]
theorem inp_1309 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1309 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1309 (by decide) v h
def cl_1310 : CNF.NClause := [(82,true),(5,true),(6,false),(7,true),(8,true),(9,true),(30,false)]
theorem inp_1310 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1310 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1310 (by decide) v h
def cl_1311 : CNF.NClause := [(82,true),(5,false),(6,true),(7,true),(8,true),(9,true),(30,false)]
theorem inp_1311 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1311 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1311 (by decide) v h
def cl_1312 : CNF.NClause := [(82,false),(5,true),(6,true),(7,true),(8,true),(9,true),(30,false)]
theorem inp_1312 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1312 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1312 (by decide) v h
def cl_1313 : CNF.NClause := [(82,true),(5,false),(6,false),(7,false),(8,false),(9,false),(30,true)]
theorem inp_1313 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1313 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1313 (by decide) v h
def cl_1314 : CNF.NClause := [(82,true),(5,true),(6,false),(7,false),(8,false),(9,false),(30,true)]
theorem inp_1314 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1314 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1314 (by decide) v h
def cl_1317 : CNF.NClause := [(82,true),(5,false),(6,false),(7,true),(8,false),(9,false),(30,true)]
theorem inp_1317 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1317 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1317 (by decide) v h
def cl_1318 : CNF.NClause := [(82,true),(5,true),(6,false),(7,true),(8,false),(9,false),(30,true)]
theorem inp_1318 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1318 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1318 (by decide) v h
def cl_1320 : CNF.NClause := [(82,true),(5,true),(6,true),(7,true),(8,false),(9,false),(30,true)]
theorem inp_1320 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1320 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1320 (by decide) v h
def cl_1321 : CNF.NClause := [(82,true),(5,false),(6,false),(7,false),(8,true),(9,false),(30,true)]
theorem inp_1321 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1321 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1321 (by decide) v h
def cl_1322 : CNF.NClause := [(82,true),(5,true),(6,false),(7,false),(8,true),(9,false),(30,true)]
theorem inp_1322 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1322 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1322 (by decide) v h
def cl_1325 : CNF.NClause := [(82,true),(5,false),(6,false),(7,true),(8,true),(9,false),(30,true)]
theorem inp_1325 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1325 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1325 (by decide) v h
end Percolation.Replay
