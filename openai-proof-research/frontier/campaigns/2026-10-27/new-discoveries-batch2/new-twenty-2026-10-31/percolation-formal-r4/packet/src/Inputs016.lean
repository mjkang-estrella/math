import Inputs015
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_1326 : CNF.NClause := [(82,true),(5,true),(6,false),(7,true),(8,true),(9,false),(30,true)]
theorem inp_1326 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1326 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1326 (by decide) v h
def cl_1327 : CNF.NClause := [(82,true),(5,false),(6,true),(7,true),(8,true),(9,false),(30,true)]
theorem inp_1327 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1327 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1327 (by decide) v h
def cl_1328 : CNF.NClause := [(82,false),(5,true),(6,true),(7,true),(8,true),(9,false),(30,true)]
theorem inp_1328 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1328 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1328 (by decide) v h
def cl_1329 : CNF.NClause := [(82,true),(5,false),(6,false),(7,false),(8,false),(9,true),(30,true)]
theorem inp_1329 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1329 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1329 (by decide) v h
def cl_1330 : CNF.NClause := [(82,true),(5,true),(6,false),(7,false),(8,false),(9,true),(30,true)]
theorem inp_1330 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1330 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1330 (by decide) v h
def cl_1331 : CNF.NClause := [(82,true),(5,false),(6,true),(7,false),(8,false),(9,true),(30,true)]
theorem inp_1331 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1331 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1331 (by decide) v h
def cl_1333 : CNF.NClause := [(82,true),(5,false),(6,false),(7,true),(8,false),(9,true),(30,true)]
theorem inp_1333 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1333 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1333 (by decide) v h
def cl_1334 : CNF.NClause := [(82,true),(5,true),(6,false),(7,true),(8,false),(9,true),(30,true)]
theorem inp_1334 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1334 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1334 (by decide) v h
def cl_1335 : CNF.NClause := [(82,true),(5,false),(6,true),(7,true),(8,false),(9,true),(30,true)]
theorem inp_1335 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1335 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1335 (by decide) v h
def cl_1336 : CNF.NClause := [(82,false),(5,true),(6,true),(7,true),(8,false),(9,true),(30,true)]
theorem inp_1336 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1336 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1336 (by decide) v h
def cl_1338 : CNF.NClause := [(82,true),(5,true),(6,false),(7,false),(8,true),(9,true),(30,true)]
theorem inp_1338 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1338 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1338 (by decide) v h
def cl_1340 : CNF.NClause := [(82,false),(5,true),(6,true),(7,false),(8,true),(9,true),(30,true)]
theorem inp_1340 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1340 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1340 (by decide) v h
def cl_1341 : CNF.NClause := [(82,true),(5,false),(6,false),(7,true),(8,true),(9,true),(30,true)]
theorem inp_1341 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1341 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1341 (by decide) v h
def cl_1342 : CNF.NClause := [(82,false),(5,true),(6,false),(7,true),(8,true),(9,true),(30,true)]
theorem inp_1342 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1342 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1342 (by decide) v h
def cl_1343 : CNF.NClause := [(82,false),(5,false),(6,true),(7,true),(8,true),(9,true),(30,true)]
theorem inp_1343 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1343 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1343 (by decide) v h
def cl_1344 : CNF.NClause := [(82,false),(5,true),(6,true),(7,true),(8,true),(9,true),(30,true)]
theorem inp_1344 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1344 := by
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) cl_1344 (by decide) v h
def cl_1345 : CNF.NClause := [(83,true),(4,false),(5,false),(11,false),(17,false),(23,false),(26,false)]
theorem inp_1345 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1345 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1345 (by decide) v h
def cl_1346 : CNF.NClause := [(83,true),(4,true),(5,false),(11,false),(17,false),(23,false),(26,false)]
theorem inp_1346 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1346 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1346 (by decide) v h
def cl_1347 : CNF.NClause := [(83,true),(4,false),(5,true),(11,false),(17,false),(23,false),(26,false)]
theorem inp_1347 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1347 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1347 (by decide) v h
def cl_1348 : CNF.NClause := [(83,true),(4,true),(5,true),(11,false),(17,false),(23,false),(26,false)]
theorem inp_1348 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1348 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1348 (by decide) v h
def cl_1349 : CNF.NClause := [(83,true),(4,false),(5,false),(11,true),(17,false),(23,false),(26,false)]
theorem inp_1349 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1349 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1349 (by decide) v h
def cl_1350 : CNF.NClause := [(83,true),(4,true),(5,false),(11,true),(17,false),(23,false),(26,false)]
theorem inp_1350 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1350 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1350 (by decide) v h
def cl_1351 : CNF.NClause := [(83,true),(4,false),(5,true),(11,true),(17,false),(23,false),(26,false)]
theorem inp_1351 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1351 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1351 (by decide) v h
def cl_1352 : CNF.NClause := [(83,true),(4,true),(5,true),(11,true),(17,false),(23,false),(26,false)]
theorem inp_1352 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1352 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1352 (by decide) v h
def cl_1353 : CNF.NClause := [(83,true),(4,false),(5,false),(11,false),(17,true),(23,false),(26,false)]
theorem inp_1353 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1353 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1353 (by decide) v h
def cl_1355 : CNF.NClause := [(83,true),(4,false),(5,true),(11,false),(17,true),(23,false),(26,false)]
theorem inp_1355 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1355 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1355 (by decide) v h
def cl_1356 : CNF.NClause := [(83,true),(4,true),(5,true),(11,false),(17,true),(23,false),(26,false)]
theorem inp_1356 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1356 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1356 (by decide) v h
def cl_1359 : CNF.NClause := [(83,true),(4,false),(5,true),(11,true),(17,true),(23,false),(26,false)]
theorem inp_1359 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1359 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1359 (by decide) v h
def cl_1360 : CNF.NClause := [(83,true),(4,true),(5,true),(11,true),(17,true),(23,false),(26,false)]
theorem inp_1360 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1360 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1360 (by decide) v h
def cl_1363 : CNF.NClause := [(83,true),(4,false),(5,true),(11,false),(17,false),(23,true),(26,false)]
theorem inp_1363 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1363 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1363 (by decide) v h
def cl_1364 : CNF.NClause := [(83,true),(4,true),(5,true),(11,false),(17,false),(23,true),(26,false)]
theorem inp_1364 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1364 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1364 (by decide) v h
def cl_1367 : CNF.NClause := [(83,true),(4,false),(5,true),(11,true),(17,false),(23,true),(26,false)]
theorem inp_1367 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1367 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1367 (by decide) v h
def cl_1368 : CNF.NClause := [(83,true),(4,true),(5,true),(11,true),(17,false),(23,true),(26,false)]
theorem inp_1368 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1368 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1368 (by decide) v h
def cl_1369 : CNF.NClause := [(83,true),(4,false),(5,false),(11,false),(17,true),(23,true),(26,false)]
theorem inp_1369 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1369 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1369 (by decide) v h
def cl_1371 : CNF.NClause := [(83,true),(4,false),(5,true),(11,false),(17,true),(23,true),(26,false)]
theorem inp_1371 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1371 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1371 (by decide) v h
def cl_1372 : CNF.NClause := [(83,true),(4,true),(5,true),(11,false),(17,true),(23,true),(26,false)]
theorem inp_1372 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1372 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1372 (by decide) v h
def cl_1375 : CNF.NClause := [(83,true),(4,false),(5,true),(11,true),(17,true),(23,true),(26,false)]
theorem inp_1375 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1375 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1375 (by decide) v h
def cl_1376 : CNF.NClause := [(83,false),(4,true),(5,true),(11,true),(17,true),(23,true),(26,false)]
theorem inp_1376 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1376 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1376 (by decide) v h
def cl_1377 : CNF.NClause := [(83,true),(4,false),(5,false),(11,false),(17,false),(23,false),(26,true)]
theorem inp_1377 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1377 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1377 (by decide) v h
def cl_1379 : CNF.NClause := [(83,true),(4,false),(5,true),(11,false),(17,false),(23,false),(26,true)]
theorem inp_1379 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1379 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1379 (by decide) v h
def cl_1380 : CNF.NClause := [(83,true),(4,true),(5,true),(11,false),(17,false),(23,false),(26,true)]
theorem inp_1380 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1380 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1380 (by decide) v h
def cl_1383 : CNF.NClause := [(83,true),(4,false),(5,true),(11,true),(17,false),(23,false),(26,true)]
theorem inp_1383 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1383 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1383 (by decide) v h
def cl_1385 : CNF.NClause := [(83,true),(4,false),(5,false),(11,false),(17,true),(23,false),(26,true)]
theorem inp_1385 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1385 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1385 (by decide) v h
def cl_1387 : CNF.NClause := [(83,true),(4,false),(5,true),(11,false),(17,true),(23,false),(26,true)]
theorem inp_1387 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1387 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1387 (by decide) v h
def cl_1388 : CNF.NClause := [(83,true),(4,true),(5,true),(11,false),(17,true),(23,false),(26,true)]
theorem inp_1388 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1388 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1388 (by decide) v h
def cl_1391 : CNF.NClause := [(83,true),(4,false),(5,true),(11,true),(17,true),(23,false),(26,true)]
theorem inp_1391 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1391 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1391 (by decide) v h
def cl_1392 : CNF.NClause := [(83,false),(4,true),(5,true),(11,true),(17,true),(23,false),(26,true)]
theorem inp_1392 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1392 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1392 (by decide) v h
def cl_1395 : CNF.NClause := [(83,true),(4,false),(5,true),(11,false),(17,false),(23,true),(26,true)]
theorem inp_1395 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1395 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1395 (by decide) v h
def cl_1396 : CNF.NClause := [(83,true),(4,true),(5,true),(11,false),(17,false),(23,true),(26,true)]
theorem inp_1396 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1396 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1396 (by decide) v h
def cl_1399 : CNF.NClause := [(83,true),(4,false),(5,true),(11,true),(17,false),(23,true),(26,true)]
theorem inp_1399 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1399 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1399 (by decide) v h
end Percolation.Replay
