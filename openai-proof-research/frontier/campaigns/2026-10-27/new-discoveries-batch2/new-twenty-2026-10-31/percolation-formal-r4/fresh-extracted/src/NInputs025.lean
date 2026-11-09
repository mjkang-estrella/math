import NInputs024
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_1560 : CNF.NClause := [(86,true),(1,true),(5,true),(14,true),(18,false),(22,true),(29,false)]
theorem inp_1560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1560 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1560 v hb
def cl_1561 : CNF.NClause := [(86,true),(1,false),(5,false),(14,false),(18,true),(22,true),(29,false)]
theorem inp_1561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1561 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1561 (by decide) v hb
def cl_1562 : CNF.NClause := [(86,true),(1,true),(5,false),(14,false),(18,true),(22,true),(29,false)]
theorem inp_1562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1562 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1562 (by decide) v hb
def cl_1563 : CNF.NClause := [(86,true),(1,false),(5,true),(14,false),(18,true),(22,true),(29,false)]
theorem inp_1563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1563 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1563 v hb
def cl_1564 : CNF.NClause := [(86,true),(1,true),(5,true),(14,false),(18,true),(22,true),(29,false)]
theorem inp_1564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1564 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1564 (by decide) v hb
def cl_1565 : CNF.NClause := [(86,true),(1,false),(5,false),(14,true),(18,true),(22,true),(29,false)]
theorem inp_1565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1565 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1565 (by decide) v hb
def cl_1566 : CNF.NClause := [(86,true),(1,true),(5,false),(14,true),(18,true),(22,true),(29,false)]
theorem inp_1566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1566 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1566 (by decide) v hb
def cl_1567 : CNF.NClause := [(86,true),(1,false),(5,true),(14,true),(18,true),(22,true),(29,false)]
theorem inp_1567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1567 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1567 v hb
def cl_1568 : CNF.NClause := [(86,false),(1,true),(5,true),(14,true),(18,true),(22,true),(29,false)]
theorem inp_1568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1568 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1568 (by decide) v hb
def cl_1569 : CNF.NClause := [(86,true),(1,false),(5,false),(14,false),(18,false),(22,false),(29,true)]
theorem inp_1569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1569 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1569 v hb
def cl_1570 : CNF.NClause := [(86,true),(1,true),(5,false),(14,false),(18,false),(22,false),(29,true)]
theorem inp_1570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1570 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1570 (by decide) v hb
def cl_1571 : CNF.NClause := [(86,true),(1,false),(5,true),(14,false),(18,false),(22,false),(29,true)]
theorem inp_1571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1571 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1571 v hb
def cl_1572 : CNF.NClause := [(86,true),(1,true),(5,true),(14,false),(18,false),(22,false),(29,true)]
theorem inp_1572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1572 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1572 v hb
def cl_1573 : CNF.NClause := [(86,true),(1,false),(5,false),(14,true),(18,false),(22,false),(29,true)]
theorem inp_1573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1573 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1573 (by decide) v hb
def cl_1574 : CNF.NClause := [(86,true),(1,true),(5,false),(14,true),(18,false),(22,false),(29,true)]
theorem inp_1574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1574 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1574 (by decide) v hb
def cl_1575 : CNF.NClause := [(86,true),(1,false),(5,true),(14,true),(18,false),(22,false),(29,true)]
theorem inp_1575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1575 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1575 v hb
def cl_1576 : CNF.NClause := [(86,true),(1,true),(5,true),(14,true),(18,false),(22,false),(29,true)]
theorem inp_1576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1576 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1576 v hb
def cl_1577 : CNF.NClause := [(86,true),(1,false),(5,false),(14,false),(18,true),(22,false),(29,true)]
theorem inp_1577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1577 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1577 (by decide) v hb
def cl_1578 : CNF.NClause := [(86,true),(1,true),(5,false),(14,false),(18,true),(22,false),(29,true)]
theorem inp_1578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1578 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1578 (by decide) v hb
def cl_1579 : CNF.NClause := [(86,true),(1,false),(5,true),(14,false),(18,true),(22,false),(29,true)]
theorem inp_1579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1579 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1579 v hb
def cl_1580 : CNF.NClause := [(86,true),(1,true),(5,true),(14,false),(18,true),(22,false),(29,true)]
theorem inp_1580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1580 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1580 v hb
def cl_1581 : CNF.NClause := [(86,true),(1,false),(5,false),(14,true),(18,true),(22,false),(29,true)]
theorem inp_1581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1581 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1581 (by decide) v hb
def cl_1582 : CNF.NClause := [(86,true),(1,true),(5,false),(14,true),(18,true),(22,false),(29,true)]
theorem inp_1582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1582 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1582 (by decide) v hb
def cl_1583 : CNF.NClause := [(86,true),(1,false),(5,true),(14,true),(18,true),(22,false),(29,true)]
theorem inp_1583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1583 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1583 v hb
def cl_1584 : CNF.NClause := [(86,false),(1,true),(5,true),(14,true),(18,true),(22,false),(29,true)]
theorem inp_1584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1584 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1584 (by decide) v hb
def cl_1585 : CNF.NClause := [(86,true),(1,false),(5,false),(14,false),(18,false),(22,true),(29,true)]
theorem inp_1585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1585 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1585 (by decide) v hb
def cl_1586 : CNF.NClause := [(86,true),(1,true),(5,false),(14,false),(18,false),(22,true),(29,true)]
theorem inp_1586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1586 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1586 (by decide) v hb
def cl_1587 : CNF.NClause := [(86,true),(1,false),(5,true),(14,false),(18,false),(22,true),(29,true)]
theorem inp_1587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1587 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1587 v hb
def cl_1588 : CNF.NClause := [(86,true),(1,true),(5,true),(14,false),(18,false),(22,true),(29,true)]
theorem inp_1588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1588 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1588 (by decide) v hb
def cl_1589 : CNF.NClause := [(86,true),(1,false),(5,false),(14,true),(18,false),(22,true),(29,true)]
theorem inp_1589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1589 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1589 (by decide) v hb
def cl_1590 : CNF.NClause := [(86,true),(1,true),(5,false),(14,true),(18,false),(22,true),(29,true)]
theorem inp_1590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1590 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1590 (by decide) v hb
def cl_1591 : CNF.NClause := [(86,true),(1,false),(5,true),(14,true),(18,false),(22,true),(29,true)]
theorem inp_1591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1591 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1591 v hb
def cl_1592 : CNF.NClause := [(86,false),(1,true),(5,true),(14,true),(18,false),(22,true),(29,true)]
theorem inp_1592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1592 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1592 (by decide) v hb
def cl_1593 : CNF.NClause := [(86,true),(1,false),(5,false),(14,false),(18,true),(22,true),(29,true)]
theorem inp_1593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1593 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1593 (by decide) v hb
def cl_1594 : CNF.NClause := [(86,true),(1,true),(5,false),(14,false),(18,true),(22,true),(29,true)]
theorem inp_1594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1594 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1594 (by decide) v hb
def cl_1595 : CNF.NClause := [(86,true),(1,false),(5,true),(14,false),(18,true),(22,true),(29,true)]
theorem inp_1595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1595 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1595 v hb
def cl_1596 : CNF.NClause := [(86,false),(1,true),(5,true),(14,false),(18,true),(22,true),(29,true)]
theorem inp_1596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1596 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1596 (by decide) v hb
def cl_1597 : CNF.NClause := [(86,true),(1,false),(5,false),(14,true),(18,true),(22,true),(29,true)]
theorem inp_1597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1597 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1597 (by decide) v hb
def cl_1598 : CNF.NClause := [(86,false),(1,true),(5,false),(14,true),(18,true),(22,true),(29,true)]
theorem inp_1598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1598 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1598 (by decide) v hb
def cl_1599 : CNF.NClause := [(86,false),(1,false),(5,true),(14,true),(18,true),(22,true),(29,true)]
theorem inp_1599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1599 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) cl_1599 (by decide) v hb
def cl_1634 : CNF.NClause := [(87,true),(0,true),(1,false),(2,false),(3,false),(4,false),(30,true)]
theorem inp_1634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1634 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1634 v hb
def cl_1636 : CNF.NClause := [(87,true),(0,true),(1,true),(2,false),(3,false),(4,false),(30,true)]
theorem inp_1636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1636 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1636 (by decide) v hb
def cl_1638 : CNF.NClause := [(87,true),(0,true),(1,false),(2,true),(3,false),(4,false),(30,true)]
theorem inp_1638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1638 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1638 v hb
def cl_1640 : CNF.NClause := [(87,true),(0,true),(1,true),(2,true),(3,false),(4,false),(30,true)]
theorem inp_1640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1640 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1640 (by decide) v hb
def cl_1642 : CNF.NClause := [(87,true),(0,true),(1,false),(2,false),(3,true),(4,false),(30,true)]
theorem inp_1642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1642 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1642 v hb
def cl_1644 : CNF.NClause := [(87,true),(0,true),(1,true),(2,false),(3,true),(4,false),(30,true)]
theorem inp_1644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1644 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1644 v hb
def cl_1646 : CNF.NClause := [(87,true),(0,true),(1,false),(2,true),(3,true),(4,false),(30,true)]
theorem inp_1646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1646 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1646 v hb
def cl_1648 : CNF.NClause := [(87,false),(0,true),(1,true),(2,true),(3,true),(4,false),(30,true)]
theorem inp_1648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1648 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1648 v hb
def cl_1650 : CNF.NClause := [(87,true),(0,true),(1,false),(2,false),(3,false),(4,true),(30,true)]
theorem inp_1650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1650 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1650 v hb
def cl_1652 : CNF.NClause := [(87,true),(0,true),(1,true),(2,false),(3,false),(4,true),(30,true)]
theorem inp_1652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1652 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) cl_1652 (by decide) v hb
end Percolation.NReplay
