import NInputs022
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_1460 : CNF.NClause := [(84,true),(2,true),(5,true),(13,false),(16,false),(24,true),(28,true)]
theorem inp_1460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1460 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1460 v hb
def cl_1461 : CNF.NClause := [(84,true),(2,false),(5,false),(13,true),(16,false),(24,true),(28,true)]
theorem inp_1461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1461 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1461 (by decide) v hb
def cl_1462 : CNF.NClause := [(84,true),(2,true),(5,false),(13,true),(16,false),(24,true),(28,true)]
theorem inp_1462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1462 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1462 (by decide) v hb
def cl_1463 : CNF.NClause := [(84,true),(2,false),(5,true),(13,true),(16,false),(24,true),(28,true)]
theorem inp_1463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1463 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1463 v hb
def cl_1464 : CNF.NClause := [(84,false),(2,true),(5,true),(13,true),(16,false),(24,true),(28,true)]
theorem inp_1464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1464 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1464 v hb
def cl_1465 : CNF.NClause := [(84,true),(2,false),(5,false),(13,false),(16,true),(24,true),(28,true)]
theorem inp_1465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1465 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1465 (by decide) v hb
def cl_1466 : CNF.NClause := [(84,true),(2,true),(5,false),(13,false),(16,true),(24,true),(28,true)]
theorem inp_1466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1466 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1466 (by decide) v hb
def cl_1467 : CNF.NClause := [(84,true),(2,false),(5,true),(13,false),(16,true),(24,true),(28,true)]
theorem inp_1467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1467 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1467 v hb
def cl_1468 : CNF.NClause := [(84,false),(2,true),(5,true),(13,false),(16,true),(24,true),(28,true)]
theorem inp_1468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1468 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1468 v hb
def cl_1469 : CNF.NClause := [(84,true),(2,false),(5,false),(13,true),(16,true),(24,true),(28,true)]
theorem inp_1469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1469 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1469 (by decide) v hb
def cl_1470 : CNF.NClause := [(84,false),(2,true),(5,false),(13,true),(16,true),(24,true),(28,true)]
theorem inp_1470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1470 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1470 v hb
def cl_1471 : CNF.NClause := [(84,false),(2,false),(5,true),(13,true),(16,true),(24,true),(28,true)]
theorem inp_1471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1471 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1471 v hb
def cl_1472 : CNF.NClause := [(84,false),(2,true),(5,true),(13,true),(16,true),(24,true),(28,true)]
theorem inp_1472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1472 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1472 v hb
def cl_1473 : CNF.NClause := [(85,true),(3,false),(5,false),(12,false),(19,false),(21,false),(27,false)]
theorem inp_1473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1473 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1473 v hb
def cl_1474 : CNF.NClause := [(85,true),(3,true),(5,false),(12,false),(19,false),(21,false),(27,false)]
theorem inp_1474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1474 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1474 v hb
def cl_1475 : CNF.NClause := [(85,true),(3,false),(5,true),(12,false),(19,false),(21,false),(27,false)]
theorem inp_1475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1475 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1475 v hb
def cl_1476 : CNF.NClause := [(85,true),(3,true),(5,true),(12,false),(19,false),(21,false),(27,false)]
theorem inp_1476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1476 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1476 v hb
def cl_1477 : CNF.NClause := [(85,true),(3,false),(5,false),(12,true),(19,false),(21,false),(27,false)]
theorem inp_1477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1477 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1477 v hb
def cl_1478 : CNF.NClause := [(85,true),(3,true),(5,false),(12,true),(19,false),(21,false),(27,false)]
theorem inp_1478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1478 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1478 v hb
def cl_1479 : CNF.NClause := [(85,true),(3,false),(5,true),(12,true),(19,false),(21,false),(27,false)]
theorem inp_1479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1479 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1479 v hb
def cl_1480 : CNF.NClause := [(85,true),(3,true),(5,true),(12,true),(19,false),(21,false),(27,false)]
theorem inp_1480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1480 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1480 (by decide) v hb
def cl_1481 : CNF.NClause := [(85,true),(3,false),(5,false),(12,false),(19,true),(21,false),(27,false)]
theorem inp_1481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1481 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1481 (by decide) v hb
def cl_1482 : CNF.NClause := [(85,true),(3,true),(5,false),(12,false),(19,true),(21,false),(27,false)]
theorem inp_1482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1482 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1482 (by decide) v hb
def cl_1483 : CNF.NClause := [(85,true),(3,false),(5,true),(12,false),(19,true),(21,false),(27,false)]
theorem inp_1483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1483 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1483 v hb
def cl_1484 : CNF.NClause := [(85,true),(3,true),(5,true),(12,false),(19,true),(21,false),(27,false)]
theorem inp_1484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1484 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1484 v hb
def cl_1485 : CNF.NClause := [(85,true),(3,false),(5,false),(12,true),(19,true),(21,false),(27,false)]
theorem inp_1485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1485 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1485 (by decide) v hb
def cl_1486 : CNF.NClause := [(85,true),(3,true),(5,false),(12,true),(19,true),(21,false),(27,false)]
theorem inp_1486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1486 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1486 (by decide) v hb
def cl_1487 : CNF.NClause := [(85,true),(3,false),(5,true),(12,true),(19,true),(21,false),(27,false)]
theorem inp_1487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1487 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1487 v hb
def cl_1488 : CNF.NClause := [(85,true),(3,true),(5,true),(12,true),(19,true),(21,false),(27,false)]
theorem inp_1488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1488 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1488 (by decide) v hb
def cl_1489 : CNF.NClause := [(85,true),(3,false),(5,false),(12,false),(19,false),(21,true),(27,false)]
theorem inp_1489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1489 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1489 (by decide) v hb
def cl_1490 : CNF.NClause := [(85,true),(3,true),(5,false),(12,false),(19,false),(21,true),(27,false)]
theorem inp_1490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1490 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1490 (by decide) v hb
def cl_1491 : CNF.NClause := [(85,true),(3,false),(5,true),(12,false),(19,false),(21,true),(27,false)]
theorem inp_1491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1491 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1491 v hb
def cl_1492 : CNF.NClause := [(85,true),(3,true),(5,true),(12,false),(19,false),(21,true),(27,false)]
theorem inp_1492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1492 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1492 v hb
def cl_1493 : CNF.NClause := [(85,true),(3,false),(5,false),(12,true),(19,false),(21,true),(27,false)]
theorem inp_1493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1493 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1493 (by decide) v hb
def cl_1494 : CNF.NClause := [(85,true),(3,true),(5,false),(12,true),(19,false),(21,true),(27,false)]
theorem inp_1494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1494 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1494 (by decide) v hb
def cl_1495 : CNF.NClause := [(85,true),(3,false),(5,true),(12,true),(19,false),(21,true),(27,false)]
theorem inp_1495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1495 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1495 v hb
def cl_1496 : CNF.NClause := [(85,true),(3,true),(5,true),(12,true),(19,false),(21,true),(27,false)]
theorem inp_1496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1496 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1496 (by decide) v hb
def cl_1497 : CNF.NClause := [(85,true),(3,false),(5,false),(12,false),(19,true),(21,true),(27,false)]
theorem inp_1497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1497 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1497 (by decide) v hb
def cl_1498 : CNF.NClause := [(85,true),(3,true),(5,false),(12,false),(19,true),(21,true),(27,false)]
theorem inp_1498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1498 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1498 (by decide) v hb
def cl_1499 : CNF.NClause := [(85,true),(3,false),(5,true),(12,false),(19,true),(21,true),(27,false)]
theorem inp_1499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1499 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1499 v hb
def cl_1500 : CNF.NClause := [(85,true),(3,true),(5,true),(12,false),(19,true),(21,true),(27,false)]
theorem inp_1500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1500 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1500 v hb
def cl_1501 : CNF.NClause := [(85,true),(3,false),(5,false),(12,true),(19,true),(21,true),(27,false)]
theorem inp_1501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1501 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1501 (by decide) v hb
def cl_1502 : CNF.NClause := [(85,true),(3,true),(5,false),(12,true),(19,true),(21,true),(27,false)]
theorem inp_1502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1502 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1502 (by decide) v hb
def cl_1503 : CNF.NClause := [(85,true),(3,false),(5,true),(12,true),(19,true),(21,true),(27,false)]
theorem inp_1503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1503 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1503 v hb
def cl_1504 : CNF.NClause := [(85,false),(3,true),(5,true),(12,true),(19,true),(21,true),(27,false)]
theorem inp_1504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1504 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1504 (by decide) v hb
def cl_1505 : CNF.NClause := [(85,true),(3,false),(5,false),(12,false),(19,false),(21,false),(27,true)]
theorem inp_1505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1505 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1505 v hb
def cl_1506 : CNF.NClause := [(85,true),(3,true),(5,false),(12,false),(19,false),(21,false),(27,true)]
theorem inp_1506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1506 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1506 (by decide) v hb
def cl_1507 : CNF.NClause := [(85,true),(3,false),(5,true),(12,false),(19,false),(21,false),(27,true)]
theorem inp_1507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1507 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1507 v hb
def cl_1508 : CNF.NClause := [(85,true),(3,true),(5,true),(12,false),(19,false),(21,false),(27,true)]
theorem inp_1508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1508 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1508 v hb
def cl_1509 : CNF.NClause := [(85,true),(3,false),(5,false),(12,true),(19,false),(21,false),(27,true)]
theorem inp_1509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1509 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1509 (by decide) v hb
end Percolation.NReplay
