import NInputs021
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_1410 : CNF.NClause := [(84,true),(2,true),(5,false),(13,false),(16,false),(24,false),(28,false)]
theorem inp_1410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1410 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1410 v hb
def cl_1411 : CNF.NClause := [(84,true),(2,false),(5,true),(13,false),(16,false),(24,false),(28,false)]
theorem inp_1411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1411 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1411 v hb
def cl_1412 : CNF.NClause := [(84,true),(2,true),(5,true),(13,false),(16,false),(24,false),(28,false)]
theorem inp_1412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1412 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1412 v hb
def cl_1413 : CNF.NClause := [(84,true),(2,false),(5,false),(13,true),(16,false),(24,false),(28,false)]
theorem inp_1413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1413 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1413 (by decide) v hb
def cl_1414 : CNF.NClause := [(84,true),(2,true),(5,false),(13,true),(16,false),(24,false),(28,false)]
theorem inp_1414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1414 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1414 (by decide) v hb
def cl_1415 : CNF.NClause := [(84,true),(2,false),(5,true),(13,true),(16,false),(24,false),(28,false)]
theorem inp_1415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1415 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1415 v hb
def cl_1416 : CNF.NClause := [(84,true),(2,true),(5,true),(13,true),(16,false),(24,false),(28,false)]
theorem inp_1416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1416 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1416 v hb
def cl_1417 : CNF.NClause := [(84,true),(2,false),(5,false),(13,false),(16,true),(24,false),(28,false)]
theorem inp_1417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1417 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1417 (by decide) v hb
def cl_1418 : CNF.NClause := [(84,true),(2,true),(5,false),(13,false),(16,true),(24,false),(28,false)]
theorem inp_1418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1418 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1418 (by decide) v hb
def cl_1419 : CNF.NClause := [(84,true),(2,false),(5,true),(13,false),(16,true),(24,false),(28,false)]
theorem inp_1419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1419 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1419 v hb
def cl_1420 : CNF.NClause := [(84,true),(2,true),(5,true),(13,false),(16,true),(24,false),(28,false)]
theorem inp_1420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1420 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1420 v hb
def cl_1421 : CNF.NClause := [(84,true),(2,false),(5,false),(13,true),(16,true),(24,false),(28,false)]
theorem inp_1421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1421 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1421 (by decide) v hb
def cl_1422 : CNF.NClause := [(84,true),(2,true),(5,false),(13,true),(16,true),(24,false),(28,false)]
theorem inp_1422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1422 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1422 (by decide) v hb
def cl_1423 : CNF.NClause := [(84,true),(2,false),(5,true),(13,true),(16,true),(24,false),(28,false)]
theorem inp_1423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1423 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1423 v hb
def cl_1424 : CNF.NClause := [(84,true),(2,true),(5,true),(13,true),(16,true),(24,false),(28,false)]
theorem inp_1424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1424 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1424 v hb
def cl_1425 : CNF.NClause := [(84,true),(2,false),(5,false),(13,false),(16,false),(24,true),(28,false)]
theorem inp_1425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1425 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1425 (by decide) v hb
def cl_1426 : CNF.NClause := [(84,true),(2,true),(5,false),(13,false),(16,false),(24,true),(28,false)]
theorem inp_1426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1426 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1426 (by decide) v hb
def cl_1427 : CNF.NClause := [(84,true),(2,false),(5,true),(13,false),(16,false),(24,true),(28,false)]
theorem inp_1427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1427 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1427 v hb
def cl_1428 : CNF.NClause := [(84,true),(2,true),(5,true),(13,false),(16,false),(24,true),(28,false)]
theorem inp_1428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1428 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1428 v hb
def cl_1429 : CNF.NClause := [(84,true),(2,false),(5,false),(13,true),(16,false),(24,true),(28,false)]
theorem inp_1429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1429 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1429 (by decide) v hb
def cl_1430 : CNF.NClause := [(84,true),(2,true),(5,false),(13,true),(16,false),(24,true),(28,false)]
theorem inp_1430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1430 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1430 (by decide) v hb
def cl_1431 : CNF.NClause := [(84,true),(2,false),(5,true),(13,true),(16,false),(24,true),(28,false)]
theorem inp_1431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1431 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1431 v hb
def cl_1432 : CNF.NClause := [(84,true),(2,true),(5,true),(13,true),(16,false),(24,true),(28,false)]
theorem inp_1432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1432 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1432 (by decide) v hb
def cl_1433 : CNF.NClause := [(84,true),(2,false),(5,false),(13,false),(16,true),(24,true),(28,false)]
theorem inp_1433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1433 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1433 (by decide) v hb
def cl_1434 : CNF.NClause := [(84,true),(2,true),(5,false),(13,false),(16,true),(24,true),(28,false)]
theorem inp_1434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1434 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1434 (by decide) v hb
def cl_1435 : CNF.NClause := [(84,true),(2,false),(5,true),(13,false),(16,true),(24,true),(28,false)]
theorem inp_1435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1435 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1435 v hb
def cl_1436 : CNF.NClause := [(84,true),(2,true),(5,true),(13,false),(16,true),(24,true),(28,false)]
theorem inp_1436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1436 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1436 v hb
def cl_1437 : CNF.NClause := [(84,true),(2,false),(5,false),(13,true),(16,true),(24,true),(28,false)]
theorem inp_1437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1437 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1437 (by decide) v hb
def cl_1438 : CNF.NClause := [(84,true),(2,true),(5,false),(13,true),(16,true),(24,true),(28,false)]
theorem inp_1438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1438 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1438 (by decide) v hb
def cl_1439 : CNF.NClause := [(84,true),(2,false),(5,true),(13,true),(16,true),(24,true),(28,false)]
theorem inp_1439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1439 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1439 v hb
def cl_1440 : CNF.NClause := [(84,false),(2,true),(5,true),(13,true),(16,true),(24,true),(28,false)]
theorem inp_1440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1440 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1440 v hb
def cl_1441 : CNF.NClause := [(84,true),(2,false),(5,false),(13,false),(16,false),(24,false),(28,true)]
theorem inp_1441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1441 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1441 v hb
def cl_1442 : CNF.NClause := [(84,true),(2,true),(5,false),(13,false),(16,false),(24,false),(28,true)]
theorem inp_1442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1442 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1442 (by decide) v hb
def cl_1443 : CNF.NClause := [(84,true),(2,false),(5,true),(13,false),(16,false),(24,false),(28,true)]
theorem inp_1443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1443 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1443 v hb
def cl_1444 : CNF.NClause := [(84,true),(2,true),(5,true),(13,false),(16,false),(24,false),(28,true)]
theorem inp_1444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1444 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1444 v hb
def cl_1445 : CNF.NClause := [(84,true),(2,false),(5,false),(13,true),(16,false),(24,false),(28,true)]
theorem inp_1445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1445 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1445 (by decide) v hb
def cl_1446 : CNF.NClause := [(84,true),(2,true),(5,false),(13,true),(16,false),(24,false),(28,true)]
theorem inp_1446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1446 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1446 (by decide) v hb
def cl_1447 : CNF.NClause := [(84,true),(2,false),(5,true),(13,true),(16,false),(24,false),(28,true)]
theorem inp_1447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1447 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1447 v hb
def cl_1448 : CNF.NClause := [(84,true),(2,true),(5,true),(13,true),(16,false),(24,false),(28,true)]
theorem inp_1448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1448 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1448 v hb
def cl_1449 : CNF.NClause := [(84,true),(2,false),(5,false),(13,false),(16,true),(24,false),(28,true)]
theorem inp_1449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1449 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1449 (by decide) v hb
def cl_1450 : CNF.NClause := [(84,true),(2,true),(5,false),(13,false),(16,true),(24,false),(28,true)]
theorem inp_1450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1450 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1450 (by decide) v hb
def cl_1451 : CNF.NClause := [(84,true),(2,false),(5,true),(13,false),(16,true),(24,false),(28,true)]
theorem inp_1451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1451 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1451 v hb
def cl_1452 : CNF.NClause := [(84,true),(2,true),(5,true),(13,false),(16,true),(24,false),(28,true)]
theorem inp_1452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1452 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1452 v hb
def cl_1453 : CNF.NClause := [(84,true),(2,false),(5,false),(13,true),(16,true),(24,false),(28,true)]
theorem inp_1453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1453 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1453 (by decide) v hb
def cl_1454 : CNF.NClause := [(84,true),(2,true),(5,false),(13,true),(16,true),(24,false),(28,true)]
theorem inp_1454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1454 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1454 (by decide) v hb
def cl_1455 : CNF.NClause := [(84,true),(2,false),(5,true),(13,true),(16,true),(24,false),(28,true)]
theorem inp_1455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1455 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1455 v hb
def cl_1456 : CNF.NClause := [(84,false),(2,true),(5,true),(13,true),(16,true),(24,false),(28,true)]
theorem inp_1456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1456 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1456 v hb
def cl_1457 : CNF.NClause := [(84,true),(2,false),(5,false),(13,false),(16,false),(24,true),(28,true)]
theorem inp_1457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1457 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1457 (by decide) v hb
def cl_1458 : CNF.NClause := [(84,true),(2,true),(5,false),(13,false),(16,false),(24,true),(28,true)]
theorem inp_1458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1458 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1458 (by decide) v hb
def cl_1459 : CNF.NClause := [(84,true),(2,false),(5,true),(13,false),(16,false),(24,true),(28,true)]
theorem inp_1459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1459 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1459 v hb
end Percolation.NReplay
