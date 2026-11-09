import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause1502 : CNF.NClause := [(85,true),(3,true),(5,false),(12,true),(19,true),(21,true),(27,false)]
theorem inputList1502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1502 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1502 (by decide) v hb
mask_input "1502|134217760|38685626227668133593223176"
def inputClause1503 : CNF.NClause := [(85,true),(3,false),(5,true),(12,true),(19,true),(21,true),(27,false)]
theorem inputList1503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1503 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1503 (by decide) v hb
mask_input "1503|134217736|38685626227668133593223200"
def inputClause1505 : CNF.NClause := [(85,true),(3,false),(5,false),(12,false),(19,false),(21,false),(27,true)]
theorem inputList1505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1505 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1505 (by decide) v hb
mask_input "1505|2625576|38685626227668133724815360"
def inputClause1506 : CNF.NClause := [(85,true),(3,true),(5,false),(12,false),(19,false),(21,false),(27,true)]
theorem inputList1506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1506 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1506 (by decide) v hb
mask_input "1506|2625568|38685626227668133724815368"
def inputClause1507 : CNF.NClause := [(85,true),(3,false),(5,true),(12,false),(19,false),(21,false),(27,true)]
theorem inputList1507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1507 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1507 (by decide) v hb
mask_input "1507|2625544|38685626227668133724815392"
def inputClause1508 : CNF.NClause := [(85,true),(3,true),(5,true),(12,false),(19,false),(21,false),(27,true)]
theorem inputList1508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1508 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1508 (by decide) v hb
mask_input "1508|2625536|38685626227668133724815400"
def inputClause1509 : CNF.NClause := [(85,true),(3,false),(5,false),(12,true),(19,false),(21,false),(27,true)]
theorem inputList1509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1509 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1509 (by decide) v hb
mask_input "1509|2621480|38685626227668133724819456"
def inputClause1510 : CNF.NClause := [(85,true),(3,true),(5,false),(12,true),(19,false),(21,false),(27,true)]
theorem inputList1510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1510 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1510 (by decide) v hb
mask_input "1510|2621472|38685626227668133724819464"
def inputClause1511 : CNF.NClause := [(85,true),(3,false),(5,true),(12,true),(19,false),(21,false),(27,true)]
theorem inputList1511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1511 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1511 (by decide) v hb
mask_input "1511|2621448|38685626227668133724819488"
def inputClause1512 : CNF.NClause := [(85,true),(3,true),(5,true),(12,true),(19,false),(21,false),(27,true)]
theorem inputList1512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1512 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1512 (by decide) v hb
mask_input "1512|2621440|38685626227668133724819496"
def inputClause1513 : CNF.NClause := [(85,true),(3,false),(5,false),(12,false),(19,true),(21,false),(27,true)]
theorem inputList1513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1513 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1513 (by decide) v hb
mask_input "1513|2101288|38685626227668133725339648"
def inputClause1514 : CNF.NClause := [(85,true),(3,true),(5,false),(12,false),(19,true),(21,false),(27,true)]
theorem inputList1514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1514 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1514 (by decide) v hb
mask_input "1514|2101280|38685626227668133725339656"
def inputClause1515 : CNF.NClause := [(85,true),(3,false),(5,true),(12,false),(19,true),(21,false),(27,true)]
theorem inputList1515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1515 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1515 (by decide) v hb
mask_input "1515|2101256|38685626227668133725339680"
def inputClause1516 : CNF.NClause := [(85,true),(3,true),(5,true),(12,false),(19,true),(21,false),(27,true)]
theorem inputList1516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1516 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1516 (by decide) v hb
mask_input "1516|2101248|38685626227668133725339688"
def inputClause1517 : CNF.NClause := [(85,true),(3,false),(5,false),(12,true),(19,true),(21,false),(27,true)]
theorem inputList1517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1517 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1517 (by decide) v hb
mask_input "1517|2097192|38685626227668133725343744"
def inputClause1518 : CNF.NClause := [(85,true),(3,true),(5,false),(12,true),(19,true),(21,false),(27,true)]
theorem inputList1518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1518 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1518 (by decide) v hb
mask_input "1518|2097184|38685626227668133725343752"
def inputClause1519 : CNF.NClause := [(85,true),(3,false),(5,true),(12,true),(19,true),(21,false),(27,true)]
theorem inputList1519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1519 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1519 (by decide) v hb
mask_input "1519|2097160|38685626227668133725343776"
def inputClause1520 : CNF.NClause := [(85,false),(3,true),(5,true),(12,true),(19,true),(21,false),(27,true)]
theorem inputList1520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1520 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1520 (by decide) v hb
mask_input "1520|38685626227668133592694784|134746152"
def inputClause1521 : CNF.NClause := [(85,true),(3,false),(5,false),(12,false),(19,false),(21,true),(27,true)]
theorem inputList1521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1521 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1521 (by decide) v hb
mask_input "1521|528424|38685626227668133726912512"
def inputClause1522 : CNF.NClause := [(85,true),(3,true),(5,false),(12,false),(19,false),(21,true),(27,true)]
theorem inputList1522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1522 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1522 (by decide) v hb
mask_input "1522|528416|38685626227668133726912520"
def inputClause1523 : CNF.NClause := [(85,true),(3,false),(5,true),(12,false),(19,false),(21,true),(27,true)]
theorem inputList1523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1523 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1523 (by decide) v hb
mask_input "1523|528392|38685626227668133726912544"
def inputClause1524 : CNF.NClause := [(85,true),(3,true),(5,true),(12,false),(19,false),(21,true),(27,true)]
theorem inputList1524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1524 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1524 (by decide) v hb
mask_input "1524|528384|38685626227668133726912552"
def inputClause1525 : CNF.NClause := [(85,true),(3,false),(5,false),(12,true),(19,false),(21,true),(27,true)]
theorem inputList1525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1525 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1525 (by decide) v hb
mask_input "1525|524328|38685626227668133726916608"
def inputClause1526 : CNF.NClause := [(85,true),(3,true),(5,false),(12,true),(19,false),(21,true),(27,true)]
theorem inputList1526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1526 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1526 (by decide) v hb
mask_input "1526|524320|38685626227668133726916616"
def inputClause1527 : CNF.NClause := [(85,true),(3,false),(5,true),(12,true),(19,false),(21,true),(27,true)]
theorem inputList1527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1527 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1527 (by decide) v hb
mask_input "1527|524296|38685626227668133726916640"
def inputClause1528 : CNF.NClause := [(85,false),(3,true),(5,true),(12,true),(19,false),(21,true),(27,true)]
theorem inputList1528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1528 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1528 (by decide) v hb
mask_input "1528|38685626227668133591121920|136319016"
def inputClause1529 : CNF.NClause := [(85,true),(3,false),(5,false),(12,false),(19,true),(21,true),(27,true)]
theorem inputList1529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1529 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1529 (by decide) v hb
mask_input "1529|4136|38685626227668133727436800"
def inputClause1530 : CNF.NClause := [(85,true),(3,true),(5,false),(12,false),(19,true),(21,true),(27,true)]
theorem inputList1530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1530 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1530 (by decide) v hb
mask_input "1530|4128|38685626227668133727436808"
def inputClause1531 : CNF.NClause := [(85,true),(3,false),(5,true),(12,false),(19,true),(21,true),(27,true)]
theorem inputList1531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1531 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1531 (by decide) v hb
mask_input "1531|4104|38685626227668133727436832"
def inputClause1532 : CNF.NClause := [(85,false),(3,true),(5,true),(12,false),(19,true),(21,true),(27,true)]
theorem inputList1532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1532 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1532 (by decide) v hb
mask_input "1532|38685626227668133590601728|136839208"
def inputClause1533 : CNF.NClause := [(85,true),(3,false),(5,false),(12,true),(19,true),(21,true),(27,true)]
theorem inputList1533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1533 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1533 (by decide) v hb
mask_input "1533|40|38685626227668133727440896"
def inputClause1534 : CNF.NClause := [(85,false),(3,true),(5,false),(12,true),(19,true),(21,true),(27,true)]
theorem inputList1534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1534 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1534 (by decide) v hb
mask_input "1534|38685626227668133590597664|136843272"
def inputClause1535 : CNF.NClause := [(85,false),(3,false),(5,true),(12,true),(19,true),(21,true),(27,true)]
theorem inputList1535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1535 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1535 (by decide) v hb
mask_input "1535|38685626227668133590597640|136843296"
def inputClause1536 : CNF.NClause := [(85,false),(3,true),(5,true),(12,true),(19,true),(21,true),(27,true)]
theorem inputList1536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1536 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1536 (by decide) v hb
mask_input "1536|38685626227668133590597632|136843304"
def inputClause1537 : CNF.NClause := [(86,true),(1,false),(5,false),(14,false),(18,false),(22,false),(29,false)]
theorem inputList1537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1537 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1537 (by decide) v hb
mask_input "1537|541343778|77371252455336267181195264"
def inputClause1538 : CNF.NClause := [(86,true),(1,true),(5,false),(14,false),(18,false),(22,false),(29,false)]
theorem inputList1538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1538 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1538 (by decide) v hb
mask_input "1538|541343776|77371252455336267181195266"
def inputClause1539 : CNF.NClause := [(86,true),(1,false),(5,true),(14,false),(18,false),(22,false),(29,false)]
theorem inputList1539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1539 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1539 (by decide) v hb
mask_input "1539|541343746|77371252455336267181195296"
def inputClause1540 : CNF.NClause := [(86,true),(1,true),(5,true),(14,false),(18,false),(22,false),(29,false)]
theorem inputList1540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1540 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1540 (by decide) v hb
mask_input "1540|541343744|77371252455336267181195298"
def inputClause1541 : CNF.NClause := [(86,true),(1,false),(5,false),(14,true),(18,false),(22,false),(29,false)]
theorem inputList1541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1541 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1541 (by decide) v hb
mask_input "1541|541327394|77371252455336267181211648"
def inputClause1542 : CNF.NClause := [(86,true),(1,true),(5,false),(14,true),(18,false),(22,false),(29,false)]
theorem inputList1542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1542 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1542 (by decide) v hb
mask_input "1542|541327392|77371252455336267181211650"
end Percolation.MaskChain
