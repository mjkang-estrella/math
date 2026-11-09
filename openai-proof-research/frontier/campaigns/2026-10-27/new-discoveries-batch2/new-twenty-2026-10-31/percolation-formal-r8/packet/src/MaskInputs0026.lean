import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause1417 : CNF.NClause := [(84,true),(2,false),(5,false),(13,false),(16,true),(24,false),(28,false)]
theorem inputList1417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1417 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1417 (by decide) v hb
mask_input "1417|285220900|19342813113834066795364352"
def inputClause1418 : CNF.NClause := [(84,true),(2,true),(5,false),(13,false),(16,true),(24,false),(28,false)]
theorem inputList1418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1418 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1418 (by decide) v hb
mask_input "1418|285220896|19342813113834066795364356"
def inputClause1419 : CNF.NClause := [(84,true),(2,false),(5,true),(13,false),(16,true),(24,false),(28,false)]
theorem inputList1419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1419 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1419 (by decide) v hb
mask_input "1419|285220868|19342813113834066795364384"
def inputClause1420 : CNF.NClause := [(84,true),(2,true),(5,true),(13,false),(16,true),(24,false),(28,false)]
theorem inputList1420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1420 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1420 (by decide) v hb
mask_input "1420|285220864|19342813113834066795364388"
def inputClause1421 : CNF.NClause := [(84,true),(2,false),(5,false),(13,true),(16,true),(24,false),(28,false)]
theorem inputList1421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1421 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1421 (by decide) v hb
mask_input "1421|285212708|19342813113834066795372544"
def inputClause1422 : CNF.NClause := [(84,true),(2,true),(5,false),(13,true),(16,true),(24,false),(28,false)]
theorem inputList1422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1422 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1422 (by decide) v hb
mask_input "1422|285212704|19342813113834066795372548"
def inputClause1423 : CNF.NClause := [(84,true),(2,false),(5,true),(13,true),(16,true),(24,false),(28,false)]
theorem inputList1423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1423 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1423 (by decide) v hb
mask_input "1423|285212676|19342813113834066795372576"
def inputClause1424 : CNF.NClause := [(84,true),(2,true),(5,true),(13,true),(16,true),(24,false),(28,false)]
theorem inputList1424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1424 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1424 (by decide) v hb
mask_input "1424|285212672|19342813113834066795372580"
def inputClause1425 : CNF.NClause := [(84,true),(2,false),(5,false),(13,false),(16,false),(24,true),(28,false)]
theorem inputList1425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1425 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1425 (by decide) v hb
mask_input "1425|268509220|19342813113834066812076032"
def inputClause1426 : CNF.NClause := [(84,true),(2,true),(5,false),(13,false),(16,false),(24,true),(28,false)]
theorem inputList1426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1426 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1426 (by decide) v hb
mask_input "1426|268509216|19342813113834066812076036"
def inputClause1427 : CNF.NClause := [(84,true),(2,false),(5,true),(13,false),(16,false),(24,true),(28,false)]
theorem inputList1427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1427 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1427 (by decide) v hb
mask_input "1427|268509188|19342813113834066812076064"
def inputClause1428 : CNF.NClause := [(84,true),(2,true),(5,true),(13,false),(16,false),(24,true),(28,false)]
theorem inputList1428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1428 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1428 (by decide) v hb
mask_input "1428|268509184|19342813113834066812076068"
def inputClause1429 : CNF.NClause := [(84,true),(2,false),(5,false),(13,true),(16,false),(24,true),(28,false)]
theorem inputList1429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1429 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1429 (by decide) v hb
mask_input "1429|268501028|19342813113834066812084224"
def inputClause1430 : CNF.NClause := [(84,true),(2,true),(5,false),(13,true),(16,false),(24,true),(28,false)]
theorem inputList1430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1430 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1430 (by decide) v hb
mask_input "1430|268501024|19342813113834066812084228"
def inputClause1431 : CNF.NClause := [(84,true),(2,false),(5,true),(13,true),(16,false),(24,true),(28,false)]
theorem inputList1431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1431 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1431 (by decide) v hb
mask_input "1431|268500996|19342813113834066812084256"
def inputClause1432 : CNF.NClause := [(84,true),(2,true),(5,true),(13,true),(16,false),(24,true),(28,false)]
theorem inputList1432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1432 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1432 (by decide) v hb
mask_input "1432|268500992|19342813113834066812084260"
def inputClause1433 : CNF.NClause := [(84,true),(2,false),(5,false),(13,false),(16,true),(24,true),(28,false)]
theorem inputList1433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1433 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1433 (by decide) v hb
mask_input "1433|268443684|19342813113834066812141568"
def inputClause1434 : CNF.NClause := [(84,true),(2,true),(5,false),(13,false),(16,true),(24,true),(28,false)]
theorem inputList1434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1434 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1434 (by decide) v hb
mask_input "1434|268443680|19342813113834066812141572"
def inputClause1435 : CNF.NClause := [(84,true),(2,false),(5,true),(13,false),(16,true),(24,true),(28,false)]
theorem inputList1435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1435 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1435 (by decide) v hb
mask_input "1435|268443652|19342813113834066812141600"
def inputClause1436 : CNF.NClause := [(84,true),(2,true),(5,true),(13,false),(16,true),(24,true),(28,false)]
theorem inputList1436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1436 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1436 (by decide) v hb
mask_input "1436|268443648|19342813113834066812141604"
def inputClause1437 : CNF.NClause := [(84,true),(2,false),(5,false),(13,true),(16,true),(24,true),(28,false)]
theorem inputList1437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1437 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1437 (by decide) v hb
mask_input "1437|268435492|19342813113834066812149760"
def inputClause1438 : CNF.NClause := [(84,true),(2,true),(5,false),(13,true),(16,true),(24,true),(28,false)]
theorem inputList1438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1438 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1438 (by decide) v hb
mask_input "1438|268435488|19342813113834066812149764"
def inputClause1439 : CNF.NClause := [(84,true),(2,false),(5,true),(13,true),(16,true),(24,true),(28,false)]
theorem inputList1439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1439 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1439 (by decide) v hb
mask_input "1439|268435460|19342813113834066812149792"
def inputClause1440 : CNF.NClause := [(84,false),(2,true),(5,true),(13,true),(16,true),(24,true),(28,false)]
theorem inputList1440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1440 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1440 (by decide) v hb
mask_input "1440|19342813113834067063734272|16850980"
def inputClause1441 : CNF.NClause := [(84,true),(2,false),(5,false),(13,false),(16,false),(24,false),(28,true)]
theorem inputList1441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1441 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1441 (by decide) v hb
mask_input "1441|16850980|19342813113834067063734272"
def inputClause1442 : CNF.NClause := [(84,true),(2,true),(5,false),(13,false),(16,false),(24,false),(28,true)]
theorem inputList1442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1442 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1442 (by decide) v hb
mask_input "1442|16850976|19342813113834067063734276"
def inputClause1443 : CNF.NClause := [(84,true),(2,false),(5,true),(13,false),(16,false),(24,false),(28,true)]
theorem inputList1443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1443 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1443 (by decide) v hb
mask_input "1443|16850948|19342813113834067063734304"
def inputClause1444 : CNF.NClause := [(84,true),(2,true),(5,true),(13,false),(16,false),(24,false),(28,true)]
theorem inputList1444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1444 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1444 (by decide) v hb
mask_input "1444|16850944|19342813113834067063734308"
def inputClause1445 : CNF.NClause := [(84,true),(2,false),(5,false),(13,true),(16,false),(24,false),(28,true)]
theorem inputList1445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1445 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1445 (by decide) v hb
mask_input "1445|16842788|19342813113834067063742464"
def inputClause1446 : CNF.NClause := [(84,true),(2,true),(5,false),(13,true),(16,false),(24,false),(28,true)]
theorem inputList1446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1446 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1446 (by decide) v hb
mask_input "1446|16842784|19342813113834067063742468"
def inputClause1447 : CNF.NClause := [(84,true),(2,false),(5,true),(13,true),(16,false),(24,false),(28,true)]
theorem inputList1447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1447 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1447 (by decide) v hb
mask_input "1447|16842756|19342813113834067063742496"
def inputClause1448 : CNF.NClause := [(84,true),(2,true),(5,true),(13,true),(16,false),(24,false),(28,true)]
theorem inputList1448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1448 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1448 (by decide) v hb
mask_input "1448|16842752|19342813113834067063742500"
def inputClause1449 : CNF.NClause := [(84,true),(2,false),(5,false),(13,false),(16,true),(24,false),(28,true)]
theorem inputList1449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1449 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1449 (by decide) v hb
mask_input "1449|16785444|19342813113834067063799808"
def inputClause1450 : CNF.NClause := [(84,true),(2,true),(5,false),(13,false),(16,true),(24,false),(28,true)]
theorem inputList1450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1450 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1450 (by decide) v hb
mask_input "1450|16785440|19342813113834067063799812"
def inputClause1451 : CNF.NClause := [(84,true),(2,false),(5,true),(13,false),(16,true),(24,false),(28,true)]
theorem inputList1451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1451 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1451 (by decide) v hb
mask_input "1451|16785412|19342813113834067063799840"
def inputClause1452 : CNF.NClause := [(84,true),(2,true),(5,true),(13,false),(16,true),(24,false),(28,true)]
theorem inputList1452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1452 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1452 (by decide) v hb
mask_input "1452|16785408|19342813113834067063799844"
def inputClause1453 : CNF.NClause := [(84,true),(2,false),(5,false),(13,true),(16,true),(24,false),(28,true)]
theorem inputList1453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1453 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1453 (by decide) v hb
mask_input "1453|16777252|19342813113834067063808000"
def inputClause1454 : CNF.NClause := [(84,true),(2,true),(5,false),(13,true),(16,true),(24,false),(28,true)]
theorem inputList1454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1454 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1454 (by decide) v hb
mask_input "1454|16777248|19342813113834067063808004"
def inputClause1455 : CNF.NClause := [(84,true),(2,false),(5,true),(13,true),(16,true),(24,false),(28,true)]
theorem inputList1455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1455 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1455 (by decide) v hb
mask_input "1455|16777220|19342813113834067063808032"
def inputClause1457 : CNF.NClause := [(84,true),(2,false),(5,false),(13,false),(16,false),(24,true),(28,true)]
theorem inputList1457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1457 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1457 (by decide) v hb
mask_input "1457|73764|19342813113834067080511488"
end Percolation.MaskChain
