import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause1458 : CNF.NClause := [(84,true),(2,true),(5,false),(13,false),(16,false),(24,true),(28,true)]
theorem inputList1458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1458 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1458 (by decide) v hb
mask_input "1458|73760|19342813113834067080511492"
def inputClause1459 : CNF.NClause := [(84,true),(2,false),(5,true),(13,false),(16,false),(24,true),(28,true)]
theorem inputList1459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1459 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1459 (by decide) v hb
mask_input "1459|73732|19342813113834067080511520"
def inputClause1460 : CNF.NClause := [(84,true),(2,true),(5,true),(13,false),(16,false),(24,true),(28,true)]
theorem inputList1460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1460 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1460 (by decide) v hb
mask_input "1460|73728|19342813113834067080511524"
def inputClause1461 : CNF.NClause := [(84,true),(2,false),(5,false),(13,true),(16,false),(24,true),(28,true)]
theorem inputList1461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1461 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1461 (by decide) v hb
mask_input "1461|65572|19342813113834067080519680"
def inputClause1462 : CNF.NClause := [(84,true),(2,true),(5,false),(13,true),(16,false),(24,true),(28,true)]
theorem inputList1462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1462 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1462 (by decide) v hb
mask_input "1462|65568|19342813113834067080519684"
def inputClause1463 : CNF.NClause := [(84,true),(2,false),(5,true),(13,true),(16,false),(24,true),(28,true)]
theorem inputList1463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1463 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1463 (by decide) v hb
mask_input "1463|65540|19342813113834067080519712"
def inputClause1465 : CNF.NClause := [(84,true),(2,false),(5,false),(13,false),(16,true),(24,true),(28,true)]
theorem inputList1465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1465 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1465 (by decide) v hb
mask_input "1465|8228|19342813113834067080577024"
def inputClause1466 : CNF.NClause := [(84,true),(2,true),(5,false),(13,false),(16,true),(24,true),(28,true)]
theorem inputList1466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1466 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1466 (by decide) v hb
mask_input "1466|8224|19342813113834067080577028"
def inputClause1467 : CNF.NClause := [(84,true),(2,false),(5,true),(13,false),(16,true),(24,true),(28,true)]
theorem inputList1467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1467 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1467 (by decide) v hb
mask_input "1467|8196|19342813113834067080577056"
def inputClause1469 : CNF.NClause := [(84,true),(2,false),(5,false),(13,true),(16,true),(24,true),(28,true)]
theorem inputList1469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1469 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1469 (by decide) v hb
mask_input "1469|36|19342813113834067080585216"
def inputClause1472 : CNF.NClause := [(84,false),(2,true),(5,true),(13,true),(16,true),(24,true),(28,true)]
theorem inputList1472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1472 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1472 (by decide) v hb
mask_input "1472|19342813113834066795298816|285286436"
def inputClause1473 : CNF.NClause := [(85,true),(3,false),(5,false),(12,false),(19,false),(21,false),(27,false)]
theorem inputList1473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1473 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1473 (by decide) v hb
mask_input "1473|136843304|38685626227668133590597632"
def inputClause1474 : CNF.NClause := [(85,true),(3,true),(5,false),(12,false),(19,false),(21,false),(27,false)]
theorem inputList1474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1474 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1474 (by decide) v hb
mask_input "1474|136843296|38685626227668133590597640"
def inputClause1475 : CNF.NClause := [(85,true),(3,false),(5,true),(12,false),(19,false),(21,false),(27,false)]
theorem inputList1475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1475 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1475 (by decide) v hb
mask_input "1475|136843272|38685626227668133590597664"
def inputClause1476 : CNF.NClause := [(85,true),(3,true),(5,true),(12,false),(19,false),(21,false),(27,false)]
theorem inputList1476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1476 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1476 (by decide) v hb
mask_input "1476|136843264|38685626227668133590597672"
def inputClause1477 : CNF.NClause := [(85,true),(3,false),(5,false),(12,true),(19,false),(21,false),(27,false)]
theorem inputList1477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1477 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1477 (by decide) v hb
mask_input "1477|136839208|38685626227668133590601728"
def inputClause1478 : CNF.NClause := [(85,true),(3,true),(5,false),(12,true),(19,false),(21,false),(27,false)]
theorem inputList1478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1478 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1478 (by decide) v hb
mask_input "1478|136839200|38685626227668133590601736"
def inputClause1479 : CNF.NClause := [(85,true),(3,false),(5,true),(12,true),(19,false),(21,false),(27,false)]
theorem inputList1479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1479 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1479 (by decide) v hb
mask_input "1479|136839176|38685626227668133590601760"
def inputClause1480 : CNF.NClause := [(85,true),(3,true),(5,true),(12,true),(19,false),(21,false),(27,false)]
theorem inputList1480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1480 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1480 (by decide) v hb
mask_input "1480|136839168|38685626227668133590601768"
def inputClause1481 : CNF.NClause := [(85,true),(3,false),(5,false),(12,false),(19,true),(21,false),(27,false)]
theorem inputList1481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1481 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1481 (by decide) v hb
mask_input "1481|136319016|38685626227668133591121920"
def inputClause1482 : CNF.NClause := [(85,true),(3,true),(5,false),(12,false),(19,true),(21,false),(27,false)]
theorem inputList1482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1482 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1482 (by decide) v hb
mask_input "1482|136319008|38685626227668133591121928"
def inputClause1483 : CNF.NClause := [(85,true),(3,false),(5,true),(12,false),(19,true),(21,false),(27,false)]
theorem inputList1483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1483 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1483 (by decide) v hb
mask_input "1483|136318984|38685626227668133591121952"
def inputClause1484 : CNF.NClause := [(85,true),(3,true),(5,true),(12,false),(19,true),(21,false),(27,false)]
theorem inputList1484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1484 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1484 (by decide) v hb
mask_input "1484|136318976|38685626227668133591121960"
def inputClause1485 : CNF.NClause := [(85,true),(3,false),(5,false),(12,true),(19,true),(21,false),(27,false)]
theorem inputList1485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1485 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1485 (by decide) v hb
mask_input "1485|136314920|38685626227668133591126016"
def inputClause1486 : CNF.NClause := [(85,true),(3,true),(5,false),(12,true),(19,true),(21,false),(27,false)]
theorem inputList1486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1486 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1486 (by decide) v hb
mask_input "1486|136314912|38685626227668133591126024"
def inputClause1487 : CNF.NClause := [(85,true),(3,false),(5,true),(12,true),(19,true),(21,false),(27,false)]
theorem inputList1487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1487 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1487 (by decide) v hb
mask_input "1487|136314888|38685626227668133591126048"
def inputClause1488 : CNF.NClause := [(85,true),(3,true),(5,true),(12,true),(19,true),(21,false),(27,false)]
theorem inputList1488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1488 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1488 (by decide) v hb
mask_input "1488|136314880|38685626227668133591126056"
def inputClause1489 : CNF.NClause := [(85,true),(3,false),(5,false),(12,false),(19,false),(21,true),(27,false)]
theorem inputList1489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1489 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1489 (by decide) v hb
mask_input "1489|134746152|38685626227668133592694784"
def inputClause1490 : CNF.NClause := [(85,true),(3,true),(5,false),(12,false),(19,false),(21,true),(27,false)]
theorem inputList1490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1490 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1490 (by decide) v hb
mask_input "1490|134746144|38685626227668133592694792"
def inputClause1491 : CNF.NClause := [(85,true),(3,false),(5,true),(12,false),(19,false),(21,true),(27,false)]
theorem inputList1491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1491 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1491 (by decide) v hb
mask_input "1491|134746120|38685626227668133592694816"
def inputClause1492 : CNF.NClause := [(85,true),(3,true),(5,true),(12,false),(19,false),(21,true),(27,false)]
theorem inputList1492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1492 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1492 (by decide) v hb
mask_input "1492|134746112|38685626227668133592694824"
def inputClause1493 : CNF.NClause := [(85,true),(3,false),(5,false),(12,true),(19,false),(21,true),(27,false)]
theorem inputList1493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1493 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1493 (by decide) v hb
mask_input "1493|134742056|38685626227668133592698880"
def inputClause1494 : CNF.NClause := [(85,true),(3,true),(5,false),(12,true),(19,false),(21,true),(27,false)]
theorem inputList1494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1494 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1494 (by decide) v hb
mask_input "1494|134742048|38685626227668133592698888"
def inputClause1495 : CNF.NClause := [(85,true),(3,false),(5,true),(12,true),(19,false),(21,true),(27,false)]
theorem inputList1495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1495 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1495 (by decide) v hb
mask_input "1495|134742024|38685626227668133592698912"
def inputClause1496 : CNF.NClause := [(85,true),(3,true),(5,true),(12,true),(19,false),(21,true),(27,false)]
theorem inputList1496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1496 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1496 (by decide) v hb
mask_input "1496|134742016|38685626227668133592698920"
def inputClause1497 : CNF.NClause := [(85,true),(3,false),(5,false),(12,false),(19,true),(21,true),(27,false)]
theorem inputList1497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1497 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1497 (by decide) v hb
mask_input "1497|134221864|38685626227668133593219072"
def inputClause1498 : CNF.NClause := [(85,true),(3,true),(5,false),(12,false),(19,true),(21,true),(27,false)]
theorem inputList1498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1498 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1498 (by decide) v hb
mask_input "1498|134221856|38685626227668133593219080"
def inputClause1499 : CNF.NClause := [(85,true),(3,false),(5,true),(12,false),(19,true),(21,true),(27,false)]
theorem inputList1499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1499 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1499 (by decide) v hb
mask_input "1499|134221832|38685626227668133593219104"
def inputClause1500 : CNF.NClause := [(85,true),(3,true),(5,true),(12,false),(19,true),(21,true),(27,false)]
theorem inputList1500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1500 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1500 (by decide) v hb
mask_input "1500|134221824|38685626227668133593219112"
def inputClause1501 : CNF.NClause := [(85,true),(3,false),(5,false),(12,true),(19,true),(21,true),(27,false)]
theorem inputList1501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1501 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1501 (by decide) v hb
mask_input "1501|134217768|38685626227668133593223168"
end Percolation.MaskChain
