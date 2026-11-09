import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause1372 : CNF.NClause := [(83,true),(4,true),(5,true),(11,false),(17,true),(23,true),(26,false)]
theorem inputList1372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1372 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1372 (by decide) v hb
mask_input "1372|67110912|9671406556917033406169136"
def inputClause1373 : CNF.NClause := [(83,true),(4,false),(5,false),(11,true),(17,true),(23,true),(26,false)]
theorem inputList1373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1373 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1373 (by decide) v hb
mask_input "1373|67108912|9671406556917033406171136"
def inputClause1374 : CNF.NClause := [(83,true),(4,true),(5,false),(11,true),(17,true),(23,true),(26,false)]
theorem inputList1374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1374 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1374 (by decide) v hb
mask_input "1374|67108896|9671406556917033406171152"
def inputClause1375 : CNF.NClause := [(83,true),(4,false),(5,true),(11,true),(17,true),(23,true),(26,false)]
theorem inputList1375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1375 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1375 (by decide) v hb
mask_input "1375|67108880|9671406556917033406171168"
def inputClause1377 : CNF.NClause := [(83,true),(4,false),(5,false),(11,false),(17,false),(23,false),(26,true)]
theorem inputList1377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1377 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1377 (by decide) v hb
mask_input "1377|8521776|9671406556917033464758272"
def inputClause1378 : CNF.NClause := [(83,true),(4,true),(5,false),(11,false),(17,false),(23,false),(26,true)]
theorem inputList1378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1378 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1378 (by decide) v hb
mask_input "1378|8521760|9671406556917033464758288"
def inputClause1379 : CNF.NClause := [(83,true),(4,false),(5,true),(11,false),(17,false),(23,false),(26,true)]
theorem inputList1379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1379 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1379 (by decide) v hb
mask_input "1379|8521744|9671406556917033464758304"
def inputClause1380 : CNF.NClause := [(83,true),(4,true),(5,true),(11,false),(17,false),(23,false),(26,true)]
theorem inputList1380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1380 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1380 (by decide) v hb
mask_input "1380|8521728|9671406556917033464758320"
def inputClause1381 : CNF.NClause := [(83,true),(4,false),(5,false),(11,true),(17,false),(23,false),(26,true)]
theorem inputList1381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1381 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1381 (by decide) v hb
mask_input "1381|8519728|9671406556917033464760320"
def inputClause1382 : CNF.NClause := [(83,true),(4,true),(5,false),(11,true),(17,false),(23,false),(26,true)]
theorem inputList1382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1382 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1382 (by decide) v hb
mask_input "1382|8519712|9671406556917033464760336"
def inputClause1383 : CNF.NClause := [(83,true),(4,false),(5,true),(11,true),(17,false),(23,false),(26,true)]
theorem inputList1383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1383 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1383 (by decide) v hb
mask_input "1383|8519696|9671406556917033464760352"
def inputClause1384 : CNF.NClause := [(83,true),(4,true),(5,true),(11,true),(17,false),(23,false),(26,true)]
theorem inputList1384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1384 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1384 (by decide) v hb
mask_input "1384|8519680|9671406556917033464760368"
def inputClause1385 : CNF.NClause := [(83,true),(4,false),(5,false),(11,false),(17,true),(23,false),(26,true)]
theorem inputList1385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1385 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1385 (by decide) v hb
mask_input "1385|8390704|9671406556917033464889344"
def inputClause1386 : CNF.NClause := [(83,true),(4,true),(5,false),(11,false),(17,true),(23,false),(26,true)]
theorem inputList1386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1386 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1386 (by decide) v hb
mask_input "1386|8390688|9671406556917033464889360"
def inputClause1387 : CNF.NClause := [(83,true),(4,false),(5,true),(11,false),(17,true),(23,false),(26,true)]
theorem inputList1387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1387 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1387 (by decide) v hb
mask_input "1387|8390672|9671406556917033464889376"
def inputClause1388 : CNF.NClause := [(83,true),(4,true),(5,true),(11,false),(17,true),(23,false),(26,true)]
theorem inputList1388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1388 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1388 (by decide) v hb
mask_input "1388|8390656|9671406556917033464889392"
def inputClause1389 : CNF.NClause := [(83,true),(4,false),(5,false),(11,true),(17,true),(23,false),(26,true)]
theorem inputList1389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1389 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1389 (by decide) v hb
mask_input "1389|8388656|9671406556917033464891392"
def inputClause1390 : CNF.NClause := [(83,true),(4,true),(5,false),(11,true),(17,true),(23,false),(26,true)]
theorem inputList1390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1390 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1390 (by decide) v hb
mask_input "1390|8388640|9671406556917033464891408"
def inputClause1391 : CNF.NClause := [(83,true),(4,false),(5,true),(11,true),(17,true),(23,false),(26,true)]
theorem inputList1391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1391 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1391 (by decide) v hb
mask_input "1391|8388624|9671406556917033464891424"
def inputClause1393 : CNF.NClause := [(83,true),(4,false),(5,false),(11,false),(17,false),(23,true),(26,true)]
theorem inputList1393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1393 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1393 (by decide) v hb
mask_input "1393|133168|9671406556917033473146880"
def inputClause1394 : CNF.NClause := [(83,true),(4,true),(5,false),(11,false),(17,false),(23,true),(26,true)]
theorem inputList1394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1394 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1394 (by decide) v hb
mask_input "1394|133152|9671406556917033473146896"
def inputClause1395 : CNF.NClause := [(83,true),(4,false),(5,true),(11,false),(17,false),(23,true),(26,true)]
theorem inputList1395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1395 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1395 (by decide) v hb
mask_input "1395|133136|9671406556917033473146912"
def inputClause1396 : CNF.NClause := [(83,true),(4,true),(5,true),(11,false),(17,false),(23,true),(26,true)]
theorem inputList1396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1396 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1396 (by decide) v hb
mask_input "1396|133120|9671406556917033473146928"
def inputClause1397 : CNF.NClause := [(83,true),(4,false),(5,false),(11,true),(17,false),(23,true),(26,true)]
theorem inputList1397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1397 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1397 (by decide) v hb
mask_input "1397|131120|9671406556917033473148928"
def inputClause1398 : CNF.NClause := [(83,true),(4,true),(5,false),(11,true),(17,false),(23,true),(26,true)]
theorem inputList1398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1398 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1398 (by decide) v hb
mask_input "1398|131104|9671406556917033473148944"
def inputClause1399 : CNF.NClause := [(83,true),(4,false),(5,true),(11,true),(17,false),(23,true),(26,true)]
theorem inputList1399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1399 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1399 (by decide) v hb
mask_input "1399|131088|9671406556917033473148960"
def inputClause1401 : CNF.NClause := [(83,true),(4,false),(5,false),(11,false),(17,true),(23,true),(26,true)]
theorem inputList1401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1401 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1401 (by decide) v hb
mask_input "1401|2096|9671406556917033473277952"
def inputClause1402 : CNF.NClause := [(83,true),(4,true),(5,false),(11,false),(17,true),(23,true),(26,true)]
theorem inputList1402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1402 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1402 (by decide) v hb
mask_input "1402|2080|9671406556917033473277968"
def inputClause1403 : CNF.NClause := [(83,true),(4,false),(5,true),(11,false),(17,true),(23,true),(26,true)]
theorem inputList1403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1403 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1403 (by decide) v hb
mask_input "1403|2064|9671406556917033473277984"
def inputClause1405 : CNF.NClause := [(83,true),(4,false),(5,false),(11,true),(17,true),(23,true),(26,true)]
theorem inputList1405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1405 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1405 (by decide) v hb
mask_input "1405|48|9671406556917033473280000"
def inputClause1406 : CNF.NClause := [(83,false),(4,true),(5,false),(11,true),(17,true),(23,true),(26,true)]
theorem inputList1406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1406 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1406 (by decide) v hb
mask_input "1406|9671406556917033397649440|75630608"
def inputClause1408 : CNF.NClause := [(83,false),(4,true),(5,true),(11,true),(17,true),(23,true),(26,true)]
theorem inputList1408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1408 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1408 (by decide) v hb
mask_input "1408|9671406556917033397649408|75630640"
def inputClause1409 : CNF.NClause := [(84,true),(2,false),(5,false),(13,false),(16,false),(24,false),(28,false)]
theorem inputList1409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1409 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1409 (by decide) v hb
mask_input "1409|285286436|19342813113834066795298816"
def inputClause1410 : CNF.NClause := [(84,true),(2,true),(5,false),(13,false),(16,false),(24,false),(28,false)]
theorem inputList1410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1410 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1410 (by decide) v hb
mask_input "1410|285286432|19342813113834066795298820"
def inputClause1411 : CNF.NClause := [(84,true),(2,false),(5,true),(13,false),(16,false),(24,false),(28,false)]
theorem inputList1411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1411 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1411 (by decide) v hb
mask_input "1411|285286404|19342813113834066795298848"
def inputClause1412 : CNF.NClause := [(84,true),(2,true),(5,true),(13,false),(16,false),(24,false),(28,false)]
theorem inputList1412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1412 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1412 (by decide) v hb
mask_input "1412|285286400|19342813113834066795298852"
def inputClause1413 : CNF.NClause := [(84,true),(2,false),(5,false),(13,true),(16,false),(24,false),(28,false)]
theorem inputList1413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1413 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1413 (by decide) v hb
mask_input "1413|285278244|19342813113834066795307008"
def inputClause1414 : CNF.NClause := [(84,true),(2,true),(5,false),(13,true),(16,false),(24,false),(28,false)]
theorem inputList1414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1414 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1414 (by decide) v hb
mask_input "1414|285278240|19342813113834066795307012"
def inputClause1415 : CNF.NClause := [(84,true),(2,false),(5,true),(13,true),(16,false),(24,false),(28,false)]
theorem inputList1415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1415 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1415 (by decide) v hb
mask_input "1415|285278212|19342813113834066795307040"
def inputClause1416 : CNF.NClause := [(84,true),(2,true),(5,true),(13,true),(16,false),(24,false),(28,false)]
theorem inputList1416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1416 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1416 (by decide) v hb
mask_input "1416|285278208|19342813113834066795307044"
end Percolation.MaskChain
