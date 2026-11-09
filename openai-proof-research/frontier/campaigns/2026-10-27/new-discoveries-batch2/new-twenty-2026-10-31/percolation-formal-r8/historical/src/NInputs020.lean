import NInputs019
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_1277 : CNF.NClause := [(81,true),(1,false),(9,false),(12,true),(15,true),(23,true),(28,true)]
theorem inp_1277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1277 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1277 v hb
def cl_1278 : CNF.NClause := [(81,false),(1,true),(9,false),(12,true),(15,true),(23,true),(28,true)]
theorem inp_1278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1278 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) cl_1278 (by decide) v hb
def cl_1279 : CNF.NClause := [(81,false),(1,false),(9,true),(12,true),(15,true),(23,true),(28,true)]
theorem inp_1279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1279 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1279 v hb
def cl_1280 : CNF.NClause := [(81,false),(1,true),(9,true),(12,true),(15,true),(23,true),(28,true)]
theorem inp_1280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1280 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1280 v hb
def cl_1313 : CNF.NClause := [(82,true),(5,false),(6,false),(7,false),(8,false),(9,false),(30,true)]
theorem inp_1313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1313 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1313 v hb
def cl_1314 : CNF.NClause := [(82,true),(5,true),(6,false),(7,false),(8,false),(9,false),(30,true)]
theorem inp_1314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1314 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1314 v hb
def cl_1315 : CNF.NClause := [(82,true),(5,false),(6,true),(7,false),(8,false),(9,false),(30,true)]
theorem inp_1315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1315 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1315 (by decide) v hb
def cl_1316 : CNF.NClause := [(82,true),(5,true),(6,true),(7,false),(8,false),(9,false),(30,true)]
theorem inp_1316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1316 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1316 (by decide) v hb
def cl_1317 : CNF.NClause := [(82,true),(5,false),(6,false),(7,true),(8,false),(9,false),(30,true)]
theorem inp_1317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1317 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1317 v hb
def cl_1318 : CNF.NClause := [(82,true),(5,true),(6,false),(7,true),(8,false),(9,false),(30,true)]
theorem inp_1318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1318 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1318 v hb
def cl_1319 : CNF.NClause := [(82,true),(5,false),(6,true),(7,true),(8,false),(9,false),(30,true)]
theorem inp_1319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1319 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1319 (by decide) v hb
def cl_1320 : CNF.NClause := [(82,true),(5,true),(6,true),(7,true),(8,false),(9,false),(30,true)]
theorem inp_1320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1320 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1320 v hb
def cl_1321 : CNF.NClause := [(82,true),(5,false),(6,false),(7,false),(8,true),(9,false),(30,true)]
theorem inp_1321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1321 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1321 v hb
def cl_1322 : CNF.NClause := [(82,true),(5,true),(6,false),(7,false),(8,true),(9,false),(30,true)]
theorem inp_1322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1322 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1322 v hb
def cl_1323 : CNF.NClause := [(82,true),(5,false),(6,true),(7,false),(8,true),(9,false),(30,true)]
theorem inp_1323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1323 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1323 (by decide) v hb
def cl_1324 : CNF.NClause := [(82,true),(5,true),(6,true),(7,false),(8,true),(9,false),(30,true)]
theorem inp_1324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1324 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1324 (by decide) v hb
def cl_1325 : CNF.NClause := [(82,true),(5,false),(6,false),(7,true),(8,true),(9,false),(30,true)]
theorem inp_1325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1325 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1325 v hb
def cl_1326 : CNF.NClause := [(82,true),(5,true),(6,false),(7,true),(8,true),(9,false),(30,true)]
theorem inp_1326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1326 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1326 v hb
def cl_1327 : CNF.NClause := [(82,true),(5,false),(6,true),(7,true),(8,true),(9,false),(30,true)]
theorem inp_1327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1327 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1327 v hb
def cl_1328 : CNF.NClause := [(82,false),(5,true),(6,true),(7,true),(8,true),(9,false),(30,true)]
theorem inp_1328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1328 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1328 v hb
def cl_1329 : CNF.NClause := [(82,true),(5,false),(6,false),(7,false),(8,false),(9,true),(30,true)]
theorem inp_1329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1329 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1329 v hb
def cl_1330 : CNF.NClause := [(82,true),(5,true),(6,false),(7,false),(8,false),(9,true),(30,true)]
theorem inp_1330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1330 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1330 v hb
def cl_1331 : CNF.NClause := [(82,true),(5,false),(6,true),(7,false),(8,false),(9,true),(30,true)]
theorem inp_1331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1331 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1331 v hb
def cl_1332 : CNF.NClause := [(82,true),(5,true),(6,true),(7,false),(8,false),(9,true),(30,true)]
theorem inp_1332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1332 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1332 (by decide) v hb
def cl_1333 : CNF.NClause := [(82,true),(5,false),(6,false),(7,true),(8,false),(9,true),(30,true)]
theorem inp_1333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1333 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1333 v hb
def cl_1334 : CNF.NClause := [(82,true),(5,true),(6,false),(7,true),(8,false),(9,true),(30,true)]
theorem inp_1334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1334 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1334 v hb
def cl_1335 : CNF.NClause := [(82,true),(5,false),(6,true),(7,true),(8,false),(9,true),(30,true)]
theorem inp_1335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1335 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1335 v hb
def cl_1336 : CNF.NClause := [(82,false),(5,true),(6,true),(7,true),(8,false),(9,true),(30,true)]
theorem inp_1336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1336 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1336 v hb
def cl_1337 : CNF.NClause := [(82,true),(5,false),(6,false),(7,false),(8,true),(9,true),(30,true)]
theorem inp_1337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1337 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1337 (by decide) v hb
def cl_1338 : CNF.NClause := [(82,true),(5,true),(6,false),(7,false),(8,true),(9,true),(30,true)]
theorem inp_1338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1338 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1338 v hb
def cl_1339 : CNF.NClause := [(82,true),(5,false),(6,true),(7,false),(8,true),(9,true),(30,true)]
theorem inp_1339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1339 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1339 (by decide) v hb
def cl_1340 : CNF.NClause := [(82,false),(5,true),(6,true),(7,false),(8,true),(9,true),(30,true)]
theorem inp_1340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1340 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1340 v hb
def cl_1341 : CNF.NClause := [(82,true),(5,false),(6,false),(7,true),(8,true),(9,true),(30,true)]
theorem inp_1341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1341 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1341 v hb
def cl_1342 : CNF.NClause := [(82,false),(5,true),(6,false),(7,true),(8,true),(9,true),(30,true)]
theorem inp_1342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1342 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1342 v hb
def cl_1343 : CNF.NClause := [(82,false),(5,false),(6,true),(7,true),(8,true),(9,true),(30,true)]
theorem inp_1343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1343 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1343 v hb
def cl_1345 : CNF.NClause := [(83,true),(4,false),(5,false),(11,false),(17,false),(23,false),(26,false)]
theorem inp_1345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1345 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1345 v hb
def cl_1346 : CNF.NClause := [(83,true),(4,true),(5,false),(11,false),(17,false),(23,false),(26,false)]
theorem inp_1346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1346 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1346 v hb
def cl_1347 : CNF.NClause := [(83,true),(4,false),(5,true),(11,false),(17,false),(23,false),(26,false)]
theorem inp_1347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1347 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1347 v hb
def cl_1348 : CNF.NClause := [(83,true),(4,true),(5,true),(11,false),(17,false),(23,false),(26,false)]
theorem inp_1348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1348 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1348 v hb
def cl_1349 : CNF.NClause := [(83,true),(4,false),(5,false),(11,true),(17,false),(23,false),(26,false)]
theorem inp_1349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1349 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1349 v hb
def cl_1350 : CNF.NClause := [(83,true),(4,true),(5,false),(11,true),(17,false),(23,false),(26,false)]
theorem inp_1350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1350 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1350 v hb
def cl_1351 : CNF.NClause := [(83,true),(4,false),(5,true),(11,true),(17,false),(23,false),(26,false)]
theorem inp_1351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1351 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1351 v hb
def cl_1352 : CNF.NClause := [(83,true),(4,true),(5,true),(11,true),(17,false),(23,false),(26,false)]
theorem inp_1352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1352 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1352 v hb
def cl_1353 : CNF.NClause := [(83,true),(4,false),(5,false),(11,false),(17,true),(23,false),(26,false)]
theorem inp_1353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1353 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1353 v hb
def cl_1354 : CNF.NClause := [(83,true),(4,true),(5,false),(11,false),(17,true),(23,false),(26,false)]
theorem inp_1354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1354 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1354 (by decide) v hb
def cl_1355 : CNF.NClause := [(83,true),(4,false),(5,true),(11,false),(17,true),(23,false),(26,false)]
theorem inp_1355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1355 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1355 v hb
def cl_1356 : CNF.NClause := [(83,true),(4,true),(5,true),(11,false),(17,true),(23,false),(26,false)]
theorem inp_1356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1356 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1356 v hb
def cl_1357 : CNF.NClause := [(83,true),(4,false),(5,false),(11,true),(17,true),(23,false),(26,false)]
theorem inp_1357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1357 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1357 (by decide) v hb
def cl_1358 : CNF.NClause := [(83,true),(4,true),(5,false),(11,true),(17,true),(23,false),(26,false)]
theorem inp_1358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1358 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1358 (by decide) v hb
def cl_1359 : CNF.NClause := [(83,true),(4,false),(5,true),(11,true),(17,true),(23,false),(26,false)]
theorem inp_1359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1359 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1359 v hb
end Percolation.NReplay
