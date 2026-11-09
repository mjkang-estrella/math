import NInputs018
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_1227 : CNF.NClause := [(81,true),(1,false),(9,true),(12,false),(15,true),(23,false),(28,false)]
theorem inp_1227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1227 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1227 v hb
def cl_1228 : CNF.NClause := [(81,true),(1,true),(9,true),(12,false),(15,true),(23,false),(28,false)]
theorem inp_1228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1228 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1228 v hb
def cl_1229 : CNF.NClause := [(81,true),(1,false),(9,false),(12,true),(15,true),(23,false),(28,false)]
theorem inp_1229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1229 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1229 v hb
def cl_1230 : CNF.NClause := [(81,true),(1,true),(9,false),(12,true),(15,true),(23,false),(28,false)]
theorem inp_1230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1230 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1230 v hb
def cl_1231 : CNF.NClause := [(81,true),(1,false),(9,true),(12,true),(15,true),(23,false),(28,false)]
theorem inp_1231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1231 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1231 v hb
def cl_1232 : CNF.NClause := [(81,true),(1,true),(9,true),(12,true),(15,true),(23,false),(28,false)]
theorem inp_1232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1232 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1232 v hb
def cl_1233 : CNF.NClause := [(81,true),(1,false),(9,false),(12,false),(15,false),(23,true),(28,false)]
theorem inp_1233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1233 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1233 v hb
def cl_1234 : CNF.NClause := [(81,true),(1,true),(9,false),(12,false),(15,false),(23,true),(28,false)]
theorem inp_1234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1234 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1234 v hb
def cl_1235 : CNF.NClause := [(81,true),(1,false),(9,true),(12,false),(15,false),(23,true),(28,false)]
theorem inp_1235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1235 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1235 v hb
def cl_1236 : CNF.NClause := [(81,true),(1,true),(9,true),(12,false),(15,false),(23,true),(28,false)]
theorem inp_1236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1236 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1236 v hb
def cl_1237 : CNF.NClause := [(81,true),(1,false),(9,false),(12,true),(15,false),(23,true),(28,false)]
theorem inp_1237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1237 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1237 v hb
def cl_1238 : CNF.NClause := [(81,true),(1,true),(9,false),(12,true),(15,false),(23,true),(28,false)]
theorem inp_1238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1238 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1238 v hb
def cl_1239 : CNF.NClause := [(81,true),(1,false),(9,true),(12,true),(15,false),(23,true),(28,false)]
theorem inp_1239 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1239 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1239 v hb
def cl_1240 : CNF.NClause := [(81,true),(1,true),(9,true),(12,true),(15,false),(23,true),(28,false)]
theorem inp_1240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1240 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1240 v hb
def cl_1241 : CNF.NClause := [(81,true),(1,false),(9,false),(12,false),(15,true),(23,true),(28,false)]
theorem inp_1241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1241 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1241 v hb
def cl_1242 : CNF.NClause := [(81,true),(1,true),(9,false),(12,false),(15,true),(23,true),(28,false)]
theorem inp_1242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1242 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1242 v hb
def cl_1243 : CNF.NClause := [(81,true),(1,false),(9,true),(12,false),(15,true),(23,true),(28,false)]
theorem inp_1243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1243 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1243 v hb
def cl_1244 : CNF.NClause := [(81,true),(1,true),(9,true),(12,false),(15,true),(23,true),(28,false)]
theorem inp_1244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1244 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1244 v hb
def cl_1245 : CNF.NClause := [(81,true),(1,false),(9,false),(12,true),(15,true),(23,true),(28,false)]
theorem inp_1245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1245 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1245 v hb
def cl_1246 : CNF.NClause := [(81,true),(1,true),(9,false),(12,true),(15,true),(23,true),(28,false)]
theorem inp_1246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1246 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1246 v hb
def cl_1247 : CNF.NClause := [(81,true),(1,false),(9,true),(12,true),(15,true),(23,true),(28,false)]
theorem inp_1247 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1247 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1247 v hb
def cl_1248 : CNF.NClause := [(81,false),(1,true),(9,true),(12,true),(15,true),(23,true),(28,false)]
theorem inp_1248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1248 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1248 (by decide) v hb
def cl_1249 : CNF.NClause := [(81,true),(1,false),(9,false),(12,false),(15,false),(23,false),(28,true)]
theorem inp_1249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1249 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1249 v hb
def cl_1250 : CNF.NClause := [(81,true),(1,true),(9,false),(12,false),(15,false),(23,false),(28,true)]
theorem inp_1250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1250 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1250 v hb
def cl_1251 : CNF.NClause := [(81,true),(1,false),(9,true),(12,false),(15,false),(23,false),(28,true)]
theorem inp_1251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1251 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1251 v hb
def cl_1252 : CNF.NClause := [(81,true),(1,true),(9,true),(12,false),(15,false),(23,false),(28,true)]
theorem inp_1252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1252 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1252 v hb
def cl_1253 : CNF.NClause := [(81,true),(1,false),(9,false),(12,true),(15,false),(23,false),(28,true)]
theorem inp_1253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1253 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1253 v hb
def cl_1254 : CNF.NClause := [(81,true),(1,true),(9,false),(12,true),(15,false),(23,false),(28,true)]
theorem inp_1254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1254 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1254 v hb
def cl_1255 : CNF.NClause := [(81,true),(1,false),(9,true),(12,true),(15,false),(23,false),(28,true)]
theorem inp_1255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1255 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1255 v hb
def cl_1256 : CNF.NClause := [(81,true),(1,true),(9,true),(12,true),(15,false),(23,false),(28,true)]
theorem inp_1256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1256 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1256 v hb
def cl_1257 : CNF.NClause := [(81,true),(1,false),(9,false),(12,false),(15,true),(23,false),(28,true)]
theorem inp_1257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1257 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1257 v hb
def cl_1258 : CNF.NClause := [(81,true),(1,true),(9,false),(12,false),(15,true),(23,false),(28,true)]
theorem inp_1258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1258 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1258 v hb
def cl_1259 : CNF.NClause := [(81,true),(1,false),(9,true),(12,false),(15,true),(23,false),(28,true)]
theorem inp_1259 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1259 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1259 v hb
def cl_1260 : CNF.NClause := [(81,true),(1,true),(9,true),(12,false),(15,true),(23,false),(28,true)]
theorem inp_1260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1260 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1260 v hb
def cl_1261 : CNF.NClause := [(81,true),(1,false),(9,false),(12,true),(15,true),(23,false),(28,true)]
theorem inp_1261 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1261 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1261 v hb
def cl_1262 : CNF.NClause := [(81,true),(1,true),(9,false),(12,true),(15,true),(23,false),(28,true)]
theorem inp_1262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1262 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1262 v hb
def cl_1263 : CNF.NClause := [(81,true),(1,false),(9,true),(12,true),(15,true),(23,false),(28,true)]
theorem inp_1263 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1263 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1263 v hb
def cl_1264 : CNF.NClause := [(81,false),(1,true),(9,true),(12,true),(15,true),(23,false),(28,true)]
theorem inp_1264 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1264 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1264 (by decide) v hb
def cl_1265 : CNF.NClause := [(81,true),(1,false),(9,false),(12,false),(15,false),(23,true),(28,true)]
theorem inp_1265 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1265 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1265 v hb
def cl_1266 : CNF.NClause := [(81,true),(1,true),(9,false),(12,false),(15,false),(23,true),(28,true)]
theorem inp_1266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1266 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1266 v hb
def cl_1267 : CNF.NClause := [(81,true),(1,false),(9,true),(12,false),(15,false),(23,true),(28,true)]
theorem inp_1267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1267 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1267 v hb
def cl_1268 : CNF.NClause := [(81,true),(1,true),(9,true),(12,false),(15,false),(23,true),(28,true)]
theorem inp_1268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1268 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1268 v hb
def cl_1269 : CNF.NClause := [(81,true),(1,false),(9,false),(12,true),(15,false),(23,true),(28,true)]
theorem inp_1269 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1269 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1269 v hb
def cl_1270 : CNF.NClause := [(81,true),(1,true),(9,false),(12,true),(15,false),(23,true),(28,true)]
theorem inp_1270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1270 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1270 v hb
def cl_1271 : CNF.NClause := [(81,true),(1,false),(9,true),(12,true),(15,false),(23,true),(28,true)]
theorem inp_1271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1271 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1271 v hb
def cl_1272 : CNF.NClause := [(81,false),(1,true),(9,true),(12,true),(15,false),(23,true),(28,true)]
theorem inp_1272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1272 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1272 v hb
def cl_1273 : CNF.NClause := [(81,true),(1,false),(9,false),(12,false),(15,true),(23,true),(28,true)]
theorem inp_1273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1273 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1273 v hb
def cl_1274 : CNF.NClause := [(81,true),(1,true),(9,false),(12,false),(15,true),(23,true),(28,true)]
theorem inp_1274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1274 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1274 v hb
def cl_1275 : CNF.NClause := [(81,true),(1,false),(9,true),(12,false),(15,true),(23,true),(28,true)]
theorem inp_1275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1275 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1275 v hb
def cl_1276 : CNF.NClause := [(81,false),(1,true),(9,true),(12,false),(15,true),(23,true),(28,true)]
theorem inp_1276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1276 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1276 (by decide) v hb
end Percolation.NReplay
