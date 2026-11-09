import NInputs020
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_1360 : CNF.NClause := [(83,true),(4,true),(5,true),(11,true),(17,true),(23,false),(26,false)]
theorem inp_1360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1360 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1360 v hb
def cl_1361 : CNF.NClause := [(83,true),(4,false),(5,false),(11,false),(17,false),(23,true),(26,false)]
theorem inp_1361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1361 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1361 (by decide) v hb
def cl_1362 : CNF.NClause := [(83,true),(4,true),(5,false),(11,false),(17,false),(23,true),(26,false)]
theorem inp_1362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1362 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1362 (by decide) v hb
def cl_1363 : CNF.NClause := [(83,true),(4,false),(5,true),(11,false),(17,false),(23,true),(26,false)]
theorem inp_1363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1363 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1363 v hb
def cl_1364 : CNF.NClause := [(83,true),(4,true),(5,true),(11,false),(17,false),(23,true),(26,false)]
theorem inp_1364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1364 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1364 v hb
def cl_1365 : CNF.NClause := [(83,true),(4,false),(5,false),(11,true),(17,false),(23,true),(26,false)]
theorem inp_1365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1365 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1365 (by decide) v hb
def cl_1366 : CNF.NClause := [(83,true),(4,true),(5,false),(11,true),(17,false),(23,true),(26,false)]
theorem inp_1366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1366 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1366 (by decide) v hb
def cl_1367 : CNF.NClause := [(83,true),(4,false),(5,true),(11,true),(17,false),(23,true),(26,false)]
theorem inp_1367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1367 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1367 v hb
def cl_1368 : CNF.NClause := [(83,true),(4,true),(5,true),(11,true),(17,false),(23,true),(26,false)]
theorem inp_1368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1368 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1368 v hb
def cl_1369 : CNF.NClause := [(83,true),(4,false),(5,false),(11,false),(17,true),(23,true),(26,false)]
theorem inp_1369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1369 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1369 v hb
def cl_1370 : CNF.NClause := [(83,true),(4,true),(5,false),(11,false),(17,true),(23,true),(26,false)]
theorem inp_1370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1370 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1370 (by decide) v hb
def cl_1371 : CNF.NClause := [(83,true),(4,false),(5,true),(11,false),(17,true),(23,true),(26,false)]
theorem inp_1371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1371 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1371 v hb
def cl_1372 : CNF.NClause := [(83,true),(4,true),(5,true),(11,false),(17,true),(23,true),(26,false)]
theorem inp_1372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1372 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1372 v hb
def cl_1373 : CNF.NClause := [(83,true),(4,false),(5,false),(11,true),(17,true),(23,true),(26,false)]
theorem inp_1373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1373 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1373 (by decide) v hb
def cl_1374 : CNF.NClause := [(83,true),(4,true),(5,false),(11,true),(17,true),(23,true),(26,false)]
theorem inp_1374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1374 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1374 (by decide) v hb
def cl_1375 : CNF.NClause := [(83,true),(4,false),(5,true),(11,true),(17,true),(23,true),(26,false)]
theorem inp_1375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1375 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1375 v hb
def cl_1376 : CNF.NClause := [(83,false),(4,true),(5,true),(11,true),(17,true),(23,true),(26,false)]
theorem inp_1376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1376 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1376 v hb
def cl_1377 : CNF.NClause := [(83,true),(4,false),(5,false),(11,false),(17,false),(23,false),(26,true)]
theorem inp_1377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1377 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1377 v hb
def cl_1378 : CNF.NClause := [(83,true),(4,true),(5,false),(11,false),(17,false),(23,false),(26,true)]
theorem inp_1378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1378 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1378 (by decide) v hb
def cl_1379 : CNF.NClause := [(83,true),(4,false),(5,true),(11,false),(17,false),(23,false),(26,true)]
theorem inp_1379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1379 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1379 v hb
def cl_1380 : CNF.NClause := [(83,true),(4,true),(5,true),(11,false),(17,false),(23,false),(26,true)]
theorem inp_1380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1380 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1380 v hb
def cl_1381 : CNF.NClause := [(83,true),(4,false),(5,false),(11,true),(17,false),(23,false),(26,true)]
theorem inp_1381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1381 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1381 (by decide) v hb
def cl_1382 : CNF.NClause := [(83,true),(4,true),(5,false),(11,true),(17,false),(23,false),(26,true)]
theorem inp_1382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1382 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1382 (by decide) v hb
def cl_1383 : CNF.NClause := [(83,true),(4,false),(5,true),(11,true),(17,false),(23,false),(26,true)]
theorem inp_1383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1383 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1383 v hb
def cl_1384 : CNF.NClause := [(83,true),(4,true),(5,true),(11,true),(17,false),(23,false),(26,true)]
theorem inp_1384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1384 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1384 (by decide) v hb
def cl_1385 : CNF.NClause := [(83,true),(4,false),(5,false),(11,false),(17,true),(23,false),(26,true)]
theorem inp_1385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1385 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1385 v hb
def cl_1386 : CNF.NClause := [(83,true),(4,true),(5,false),(11,false),(17,true),(23,false),(26,true)]
theorem inp_1386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1386 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1386 (by decide) v hb
def cl_1387 : CNF.NClause := [(83,true),(4,false),(5,true),(11,false),(17,true),(23,false),(26,true)]
theorem inp_1387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1387 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1387 v hb
def cl_1388 : CNF.NClause := [(83,true),(4,true),(5,true),(11,false),(17,true),(23,false),(26,true)]
theorem inp_1388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1388 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1388 v hb
def cl_1389 : CNF.NClause := [(83,true),(4,false),(5,false),(11,true),(17,true),(23,false),(26,true)]
theorem inp_1389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1389 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1389 (by decide) v hb
def cl_1390 : CNF.NClause := [(83,true),(4,true),(5,false),(11,true),(17,true),(23,false),(26,true)]
theorem inp_1390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1390 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1390 (by decide) v hb
def cl_1391 : CNF.NClause := [(83,true),(4,false),(5,true),(11,true),(17,true),(23,false),(26,true)]
theorem inp_1391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1391 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1391 v hb
def cl_1392 : CNF.NClause := [(83,false),(4,true),(5,true),(11,true),(17,true),(23,false),(26,true)]
theorem inp_1392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1392 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1392 v hb
def cl_1393 : CNF.NClause := [(83,true),(4,false),(5,false),(11,false),(17,false),(23,true),(26,true)]
theorem inp_1393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1393 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1393 (by decide) v hb
def cl_1394 : CNF.NClause := [(83,true),(4,true),(5,false),(11,false),(17,false),(23,true),(26,true)]
theorem inp_1394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1394 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1394 (by decide) v hb
def cl_1395 : CNF.NClause := [(83,true),(4,false),(5,true),(11,false),(17,false),(23,true),(26,true)]
theorem inp_1395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1395 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1395 v hb
def cl_1396 : CNF.NClause := [(83,true),(4,true),(5,true),(11,false),(17,false),(23,true),(26,true)]
theorem inp_1396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1396 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1396 v hb
def cl_1397 : CNF.NClause := [(83,true),(4,false),(5,false),(11,true),(17,false),(23,true),(26,true)]
theorem inp_1397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1397 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1397 (by decide) v hb
def cl_1398 : CNF.NClause := [(83,true),(4,true),(5,false),(11,true),(17,false),(23,true),(26,true)]
theorem inp_1398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1398 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1398 (by decide) v hb
def cl_1399 : CNF.NClause := [(83,true),(4,false),(5,true),(11,true),(17,false),(23,true),(26,true)]
theorem inp_1399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1399 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1399 v hb
def cl_1400 : CNF.NClause := [(83,false),(4,true),(5,true),(11,true),(17,false),(23,true),(26,true)]
theorem inp_1400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1400 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1400 v hb
def cl_1401 : CNF.NClause := [(83,true),(4,false),(5,false),(11,false),(17,true),(23,true),(26,true)]
theorem inp_1401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1401 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1401 v hb
def cl_1402 : CNF.NClause := [(83,true),(4,true),(5,false),(11,false),(17,true),(23,true),(26,true)]
theorem inp_1402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1402 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1402 (by decide) v hb
def cl_1403 : CNF.NClause := [(83,true),(4,false),(5,true),(11,false),(17,true),(23,true),(26,true)]
theorem inp_1403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1403 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1403 v hb
def cl_1404 : CNF.NClause := [(83,false),(4,true),(5,true),(11,false),(17,true),(23,true),(26,true)]
theorem inp_1404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1404 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1404 v hb
def cl_1405 : CNF.NClause := [(83,true),(4,false),(5,false),(11,true),(17,true),(23,true),(26,true)]
theorem inp_1405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1405 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1405 (by decide) v hb
def cl_1406 : CNF.NClause := [(83,false),(4,true),(5,false),(11,true),(17,true),(23,true),(26,true)]
theorem inp_1406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1406 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1406 v hb
def cl_1407 : CNF.NClause := [(83,false),(4,false),(5,true),(11,true),(17,true),(23,true),(26,true)]
theorem inp_1407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1407 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1407 v hb
def cl_1408 : CNF.NClause := [(83,false),(4,true),(5,true),(11,true),(17,true),(23,true),(26,true)]
theorem inp_1408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1408 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1408 v hb
def cl_1409 : CNF.NClause := [(84,true),(2,false),(5,false),(13,false),(16,false),(24,false),(28,false)]
theorem inp_1409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1409 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1409 v hb
end Percolation.NReplay
