import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause1543 : CNF.NClause := [(86,true),(1,false),(5,true),(14,true),(18,false),(22,false),(29,false)]
theorem inputList1543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1543 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1543 (by decide) v hb
mask_input "1543|541327362|77371252455336267181211680"
def inputClause1544 : CNF.NClause := [(86,true),(1,true),(5,true),(14,true),(18,false),(22,false),(29,false)]
theorem inputList1544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1544 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1544 (by decide) v hb
mask_input "1544|541327360|77371252455336267181211682"
def inputClause1545 : CNF.NClause := [(86,true),(1,false),(5,false),(14,false),(18,true),(22,false),(29,false)]
theorem inputList1545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1545 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1545 (by decide) v hb
mask_input "1545|541081634|77371252455336267181457408"
def inputClause1546 : CNF.NClause := [(86,true),(1,true),(5,false),(14,false),(18,true),(22,false),(29,false)]
theorem inputList1546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1546 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1546 (by decide) v hb
mask_input "1546|541081632|77371252455336267181457410"
def inputClause1547 : CNF.NClause := [(86,true),(1,false),(5,true),(14,false),(18,true),(22,false),(29,false)]
theorem inputList1547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1547 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1547 (by decide) v hb
mask_input "1547|541081602|77371252455336267181457440"
def inputClause1548 : CNF.NClause := [(86,true),(1,true),(5,true),(14,false),(18,true),(22,false),(29,false)]
theorem inputList1548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1548 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1548 (by decide) v hb
mask_input "1548|541081600|77371252455336267181457442"
def inputClause1549 : CNF.NClause := [(86,true),(1,false),(5,false),(14,true),(18,true),(22,false),(29,false)]
theorem inputList1549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1549 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1549 (by decide) v hb
mask_input "1549|541065250|77371252455336267181473792"
def inputClause1550 : CNF.NClause := [(86,true),(1,true),(5,false),(14,true),(18,true),(22,false),(29,false)]
theorem inputList1550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1550 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1550 (by decide) v hb
mask_input "1550|541065248|77371252455336267181473794"
def inputClause1551 : CNF.NClause := [(86,true),(1,false),(5,true),(14,true),(18,true),(22,false),(29,false)]
theorem inputList1551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1551 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1551 (by decide) v hb
mask_input "1551|541065218|77371252455336267181473824"
def inputClause1552 : CNF.NClause := [(86,true),(1,true),(5,true),(14,true),(18,true),(22,false),(29,false)]
theorem inputList1552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1552 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1552 (by decide) v hb
mask_input "1552|541065216|77371252455336267181473826"
def inputClause1553 : CNF.NClause := [(86,true),(1,false),(5,false),(14,false),(18,false),(22,true),(29,false)]
theorem inputList1553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1553 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1553 (by decide) v hb
mask_input "1553|537149474|77371252455336267185389568"
def inputClause1554 : CNF.NClause := [(86,true),(1,true),(5,false),(14,false),(18,false),(22,true),(29,false)]
theorem inputList1554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1554 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1554 (by decide) v hb
mask_input "1554|537149472|77371252455336267185389570"
def inputClause1555 : CNF.NClause := [(86,true),(1,false),(5,true),(14,false),(18,false),(22,true),(29,false)]
theorem inputList1555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1555 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1555 (by decide) v hb
mask_input "1555|537149442|77371252455336267185389600"
def inputClause1556 : CNF.NClause := [(86,true),(1,true),(5,true),(14,false),(18,false),(22,true),(29,false)]
theorem inputList1556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1556 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1556 (by decide) v hb
mask_input "1556|537149440|77371252455336267185389602"
def inputClause1557 : CNF.NClause := [(86,true),(1,false),(5,false),(14,true),(18,false),(22,true),(29,false)]
theorem inputList1557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1557 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1557 (by decide) v hb
mask_input "1557|537133090|77371252455336267185405952"
def inputClause1558 : CNF.NClause := [(86,true),(1,true),(5,false),(14,true),(18,false),(22,true),(29,false)]
theorem inputList1558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1558 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1558 (by decide) v hb
mask_input "1558|537133088|77371252455336267185405954"
def inputClause1559 : CNF.NClause := [(86,true),(1,false),(5,true),(14,true),(18,false),(22,true),(29,false)]
theorem inputList1559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1559 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1559 (by decide) v hb
mask_input "1559|537133058|77371252455336267185405984"
def inputClause1560 : CNF.NClause := [(86,true),(1,true),(5,true),(14,true),(18,false),(22,true),(29,false)]
theorem inputList1560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1560 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1560 (by decide) v hb
mask_input "1560|537133056|77371252455336267185405986"
def inputClause1561 : CNF.NClause := [(86,true),(1,false),(5,false),(14,false),(18,true),(22,true),(29,false)]
theorem inputList1561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1561 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1561 (by decide) v hb
mask_input "1561|536887330|77371252455336267185651712"
def inputClause1562 : CNF.NClause := [(86,true),(1,true),(5,false),(14,false),(18,true),(22,true),(29,false)]
theorem inputList1562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1562 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1562 (by decide) v hb
mask_input "1562|536887328|77371252455336267185651714"
def inputClause1563 : CNF.NClause := [(86,true),(1,false),(5,true),(14,false),(18,true),(22,true),(29,false)]
theorem inputList1563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1563 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1563 (by decide) v hb
mask_input "1563|536887298|77371252455336267185651744"
def inputClause1564 : CNF.NClause := [(86,true),(1,true),(5,true),(14,false),(18,true),(22,true),(29,false)]
theorem inputList1564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1564 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1564 (by decide) v hb
mask_input "1564|536887296|77371252455336267185651746"
def inputClause1565 : CNF.NClause := [(86,true),(1,false),(5,false),(14,true),(18,true),(22,true),(29,false)]
theorem inputList1565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1565 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1565 (by decide) v hb
mask_input "1565|536870946|77371252455336267185668096"
def inputClause1566 : CNF.NClause := [(86,true),(1,true),(5,false),(14,true),(18,true),(22,true),(29,false)]
theorem inputList1566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1566 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1566 (by decide) v hb
mask_input "1566|536870944|77371252455336267185668098"
def inputClause1567 : CNF.NClause := [(86,true),(1,false),(5,true),(14,true),(18,true),(22,true),(29,false)]
theorem inputList1567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1567 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1567 (by decide) v hb
mask_input "1567|536870914|77371252455336267185668128"
def inputClause1569 : CNF.NClause := [(86,true),(1,false),(5,false),(14,false),(18,false),(22,false),(29,true)]
theorem inputList1569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1569 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1569 (by decide) v hb
mask_input "1569|4472866|77371252455336267718066176"
def inputClause1570 : CNF.NClause := [(86,true),(1,true),(5,false),(14,false),(18,false),(22,false),(29,true)]
theorem inputList1570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1570 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1570 (by decide) v hb
mask_input "1570|4472864|77371252455336267718066178"
def inputClause1571 : CNF.NClause := [(86,true),(1,false),(5,true),(14,false),(18,false),(22,false),(29,true)]
theorem inputList1571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1571 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1571 (by decide) v hb
mask_input "1571|4472834|77371252455336267718066208"
def inputClause1572 : CNF.NClause := [(86,true),(1,true),(5,true),(14,false),(18,false),(22,false),(29,true)]
theorem inputList1572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1572 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1572 (by decide) v hb
mask_input "1572|4472832|77371252455336267718066210"
def inputClause1573 : CNF.NClause := [(86,true),(1,false),(5,false),(14,true),(18,false),(22,false),(29,true)]
theorem inputList1573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1573 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1573 (by decide) v hb
mask_input "1573|4456482|77371252455336267718082560"
def inputClause1574 : CNF.NClause := [(86,true),(1,true),(5,false),(14,true),(18,false),(22,false),(29,true)]
theorem inputList1574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1574 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1574 (by decide) v hb
mask_input "1574|4456480|77371252455336267718082562"
def inputClause1575 : CNF.NClause := [(86,true),(1,false),(5,true),(14,true),(18,false),(22,false),(29,true)]
theorem inputList1575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1575 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1575 (by decide) v hb
mask_input "1575|4456450|77371252455336267718082592"
def inputClause1576 : CNF.NClause := [(86,true),(1,true),(5,true),(14,true),(18,false),(22,false),(29,true)]
theorem inputList1576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1576 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1576 (by decide) v hb
mask_input "1576|4456448|77371252455336267718082594"
def inputClause1577 : CNF.NClause := [(86,true),(1,false),(5,false),(14,false),(18,true),(22,false),(29,true)]
theorem inputList1577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1577 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1577 (by decide) v hb
mask_input "1577|4210722|77371252455336267718328320"
def inputClause1578 : CNF.NClause := [(86,true),(1,true),(5,false),(14,false),(18,true),(22,false),(29,true)]
theorem inputList1578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1578 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1578 (by decide) v hb
mask_input "1578|4210720|77371252455336267718328322"
def inputClause1579 : CNF.NClause := [(86,true),(1,false),(5,true),(14,false),(18,true),(22,false),(29,true)]
theorem inputList1579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1579 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1579 (by decide) v hb
mask_input "1579|4210690|77371252455336267718328352"
def inputClause1580 : CNF.NClause := [(86,true),(1,true),(5,true),(14,false),(18,true),(22,false),(29,true)]
theorem inputList1580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1580 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1580 (by decide) v hb
mask_input "1580|4210688|77371252455336267718328354"
def inputClause1581 : CNF.NClause := [(86,true),(1,false),(5,false),(14,true),(18,true),(22,false),(29,true)]
theorem inputList1581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1581 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1581 (by decide) v hb
mask_input "1581|4194338|77371252455336267718344704"
def inputClause1582 : CNF.NClause := [(86,true),(1,true),(5,false),(14,true),(18,true),(22,false),(29,true)]
theorem inputList1582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1582 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1582 (by decide) v hb
mask_input "1582|4194336|77371252455336267718344706"
def inputClause1583 : CNF.NClause := [(86,true),(1,false),(5,true),(14,true),(18,true),(22,false),(29,true)]
theorem inputList1583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1583 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1583 (by decide) v hb
mask_input "1583|4194306|77371252455336267718344736"
end Percolation.MaskChain
