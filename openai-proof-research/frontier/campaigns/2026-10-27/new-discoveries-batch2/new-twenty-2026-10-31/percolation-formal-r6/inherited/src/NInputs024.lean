import NInputs023
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_1510 : CNF.NClause := [(85,true),(3,true),(5,false),(12,true),(19,false),(21,false),(27,true)]
theorem inp_1510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1510 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1510 (by decide) v hb
def cl_1511 : CNF.NClause := [(85,true),(3,false),(5,true),(12,true),(19,false),(21,false),(27,true)]
theorem inp_1511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1511 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1511 v hb
def cl_1512 : CNF.NClause := [(85,true),(3,true),(5,true),(12,true),(19,false),(21,false),(27,true)]
theorem inp_1512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1512 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1512 v hb
def cl_1513 : CNF.NClause := [(85,true),(3,false),(5,false),(12,false),(19,true),(21,false),(27,true)]
theorem inp_1513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1513 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1513 (by decide) v hb
def cl_1514 : CNF.NClause := [(85,true),(3,true),(5,false),(12,false),(19,true),(21,false),(27,true)]
theorem inp_1514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1514 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1514 (by decide) v hb
def cl_1515 : CNF.NClause := [(85,true),(3,false),(5,true),(12,false),(19,true),(21,false),(27,true)]
theorem inp_1515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1515 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1515 v hb
def cl_1516 : CNF.NClause := [(85,true),(3,true),(5,true),(12,false),(19,true),(21,false),(27,true)]
theorem inp_1516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1516 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1516 v hb
def cl_1517 : CNF.NClause := [(85,true),(3,false),(5,false),(12,true),(19,true),(21,false),(27,true)]
theorem inp_1517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1517 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1517 (by decide) v hb
def cl_1518 : CNF.NClause := [(85,true),(3,true),(5,false),(12,true),(19,true),(21,false),(27,true)]
theorem inp_1518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1518 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1518 (by decide) v hb
def cl_1519 : CNF.NClause := [(85,true),(3,false),(5,true),(12,true),(19,true),(21,false),(27,true)]
theorem inp_1519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1519 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1519 v hb
def cl_1520 : CNF.NClause := [(85,false),(3,true),(5,true),(12,true),(19,true),(21,false),(27,true)]
theorem inp_1520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1520 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1520 (by decide) v hb
def cl_1521 : CNF.NClause := [(85,true),(3,false),(5,false),(12,false),(19,false),(21,true),(27,true)]
theorem inp_1521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1521 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1521 (by decide) v hb
def cl_1522 : CNF.NClause := [(85,true),(3,true),(5,false),(12,false),(19,false),(21,true),(27,true)]
theorem inp_1522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1522 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1522 (by decide) v hb
def cl_1523 : CNF.NClause := [(85,true),(3,false),(5,true),(12,false),(19,false),(21,true),(27,true)]
theorem inp_1523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1523 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1523 v hb
def cl_1524 : CNF.NClause := [(85,true),(3,true),(5,true),(12,false),(19,false),(21,true),(27,true)]
theorem inp_1524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1524 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1524 v hb
def cl_1525 : CNF.NClause := [(85,true),(3,false),(5,false),(12,true),(19,false),(21,true),(27,true)]
theorem inp_1525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1525 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1525 (by decide) v hb
def cl_1526 : CNF.NClause := [(85,true),(3,true),(5,false),(12,true),(19,false),(21,true),(27,true)]
theorem inp_1526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1526 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1526 (by decide) v hb
def cl_1527 : CNF.NClause := [(85,true),(3,false),(5,true),(12,true),(19,false),(21,true),(27,true)]
theorem inp_1527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1527 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1527 v hb
def cl_1528 : CNF.NClause := [(85,false),(3,true),(5,true),(12,true),(19,false),(21,true),(27,true)]
theorem inp_1528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1528 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1528 (by decide) v hb
def cl_1529 : CNF.NClause := [(85,true),(3,false),(5,false),(12,false),(19,true),(21,true),(27,true)]
theorem inp_1529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1529 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1529 (by decide) v hb
def cl_1530 : CNF.NClause := [(85,true),(3,true),(5,false),(12,false),(19,true),(21,true),(27,true)]
theorem inp_1530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1530 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1530 (by decide) v hb
def cl_1531 : CNF.NClause := [(85,true),(3,false),(5,true),(12,false),(19,true),(21,true),(27,true)]
theorem inp_1531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1531 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1531 v hb
def cl_1532 : CNF.NClause := [(85,false),(3,true),(5,true),(12,false),(19,true),(21,true),(27,true)]
theorem inp_1532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1532 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1532 (by decide) v hb
def cl_1533 : CNF.NClause := [(85,true),(3,false),(5,false),(12,true),(19,true),(21,true),(27,true)]
theorem inp_1533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1533 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1533 (by decide) v hb
def cl_1534 : CNF.NClause := [(85,false),(3,true),(5,false),(12,true),(19,true),(21,true),(27,true)]
theorem inp_1534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1534 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1534 (by decide) v hb
def cl_1535 : CNF.NClause := [(85,false),(3,false),(5,true),(12,true),(19,true),(21,true),(27,true)]
theorem inp_1535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1535 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1535 (by decide) v hb
def cl_1536 : CNF.NClause := [(85,false),(3,true),(5,true),(12,true),(19,true),(21,true),(27,true)]
theorem inp_1536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1536 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1536 (by decide) v hb
def cl_1537 : CNF.NClause := [(86,true),(1,false),(5,false),(14,false),(18,false),(22,false),(29,false)]
theorem inp_1537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1537 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1537 v hb
def cl_1538 : CNF.NClause := [(86,true),(1,true),(5,false),(14,false),(18,false),(22,false),(29,false)]
theorem inp_1538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1538 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1538 v hb
def cl_1539 : CNF.NClause := [(86,true),(1,false),(5,true),(14,false),(18,false),(22,false),(29,false)]
theorem inp_1539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1539 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1539 v hb
def cl_1540 : CNF.NClause := [(86,true),(1,true),(5,true),(14,false),(18,false),(22,false),(29,false)]
theorem inp_1540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1540 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1540 v hb
def cl_1541 : CNF.NClause := [(86,true),(1,false),(5,false),(14,true),(18,false),(22,false),(29,false)]
theorem inp_1541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1541 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1541 (by decide) v hb
def cl_1542 : CNF.NClause := [(86,true),(1,true),(5,false),(14,true),(18,false),(22,false),(29,false)]
theorem inp_1542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1542 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1542 (by decide) v hb
def cl_1543 : CNF.NClause := [(86,true),(1,false),(5,true),(14,true),(18,false),(22,false),(29,false)]
theorem inp_1543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1543 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1543 v hb
def cl_1544 : CNF.NClause := [(86,true),(1,true),(5,true),(14,true),(18,false),(22,false),(29,false)]
theorem inp_1544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1544 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1544 v hb
def cl_1545 : CNF.NClause := [(86,true),(1,false),(5,false),(14,false),(18,true),(22,false),(29,false)]
theorem inp_1545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1545 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1545 (by decide) v hb
def cl_1546 : CNF.NClause := [(86,true),(1,true),(5,false),(14,false),(18,true),(22,false),(29,false)]
theorem inp_1546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1546 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1546 (by decide) v hb
def cl_1547 : CNF.NClause := [(86,true),(1,false),(5,true),(14,false),(18,true),(22,false),(29,false)]
theorem inp_1547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1547 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1547 v hb
def cl_1548 : CNF.NClause := [(86,true),(1,true),(5,true),(14,false),(18,true),(22,false),(29,false)]
theorem inp_1548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1548 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1548 v hb
def cl_1549 : CNF.NClause := [(86,true),(1,false),(5,false),(14,true),(18,true),(22,false),(29,false)]
theorem inp_1549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1549 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1549 (by decide) v hb
def cl_1550 : CNF.NClause := [(86,true),(1,true),(5,false),(14,true),(18,true),(22,false),(29,false)]
theorem inp_1550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1550 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1550 (by decide) v hb
def cl_1551 : CNF.NClause := [(86,true),(1,false),(5,true),(14,true),(18,true),(22,false),(29,false)]
theorem inp_1551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1551 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1551 v hb
def cl_1552 : CNF.NClause := [(86,true),(1,true),(5,true),(14,true),(18,true),(22,false),(29,false)]
theorem inp_1552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1552 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1552 v hb
def cl_1553 : CNF.NClause := [(86,true),(1,false),(5,false),(14,false),(18,false),(22,true),(29,false)]
theorem inp_1553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1553 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1553 (by decide) v hb
def cl_1554 : CNF.NClause := [(86,true),(1,true),(5,false),(14,false),(18,false),(22,true),(29,false)]
theorem inp_1554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1554 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1554 (by decide) v hb
def cl_1555 : CNF.NClause := [(86,true),(1,false),(5,true),(14,false),(18,false),(22,true),(29,false)]
theorem inp_1555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1555 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1555 v hb
def cl_1556 : CNF.NClause := [(86,true),(1,true),(5,true),(14,false),(18,false),(22,true),(29,false)]
theorem inp_1556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1556 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1556 (by decide) v hb
def cl_1557 : CNF.NClause := [(86,true),(1,false),(5,false),(14,true),(18,false),(22,true),(29,false)]
theorem inp_1557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1557 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1557 (by decide) v hb
def cl_1558 : CNF.NClause := [(86,true),(1,true),(5,false),(14,true),(18,false),(22,true),(29,false)]
theorem inp_1558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1558 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1558 (by decide) v hb
def cl_1559 : CNF.NClause := [(86,true),(1,false),(5,true),(14,true),(18,false),(22,true),(29,false)]
theorem inp_1559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1559 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1559 v hb
end Percolation.NReplay
