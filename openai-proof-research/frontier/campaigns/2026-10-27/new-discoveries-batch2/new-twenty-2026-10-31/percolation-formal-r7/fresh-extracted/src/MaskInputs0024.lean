import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause1331 : CNF.NClause := [(82,true),(5,false),(6,true),(7,false),(8,false),(9,true),(30,true)]
theorem inputList1331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1331 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) inputClause1331 (by decide) v hb
mask_input "1331|416|4835703278458517772567104"
def inputClause1332 : CNF.NClause := [(82,true),(5,true),(6,true),(7,false),(8,false),(9,true),(30,true)]
theorem inputList1332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1332 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) inputClause1332 (by decide) v hb
mask_input "1332|384|4835703278458517772567136"
def inputClause1333 : CNF.NClause := [(82,true),(5,false),(6,false),(7,true),(8,false),(9,true),(30,true)]
theorem inputList1333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1333 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) inputClause1333 (by decide) v hb
mask_input "1333|352|4835703278458517772567168"
def inputClause1334 : CNF.NClause := [(82,true),(5,true),(6,false),(7,true),(8,false),(9,true),(30,true)]
theorem inputList1334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1334 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) inputClause1334 (by decide) v hb
mask_input "1334|320|4835703278458517772567200"
def inputClause1335 : CNF.NClause := [(82,true),(5,false),(6,true),(7,true),(8,false),(9,true),(30,true)]
theorem inputList1335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1335 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) inputClause1335 (by decide) v hb
mask_input "1335|288|4835703278458517772567232"
def inputClause1336 : CNF.NClause := [(82,false),(5,true),(6,true),(7,true),(8,false),(9,true),(30,true)]
theorem inputList1336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1336 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) inputClause1336 (by decide) v hb
mask_input "1336|4835703278458516698824960|1073742560"
def inputClause1337 : CNF.NClause := [(82,true),(5,false),(6,false),(7,false),(8,true),(9,true),(30,true)]
theorem inputList1337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1337 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) inputClause1337 (by decide) v hb
mask_input "1337|224|4835703278458517772567296"
def inputClause1338 : CNF.NClause := [(82,true),(5,true),(6,false),(7,false),(8,true),(9,true),(30,true)]
theorem inputList1338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1338 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) inputClause1338 (by decide) v hb
mask_input "1338|192|4835703278458517772567328"
def inputClause1339 : CNF.NClause := [(82,true),(5,false),(6,true),(7,false),(8,true),(9,true),(30,true)]
theorem inputList1339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1339 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) inputClause1339 (by decide) v hb
mask_input "1339|160|4835703278458517772567360"
def inputClause1340 : CNF.NClause := [(82,false),(5,true),(6,true),(7,false),(8,true),(9,true),(30,true)]
theorem inputList1340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1340 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) inputClause1340 (by decide) v hb
mask_input "1340|4835703278458516698824832|1073742688"
def inputClause1341 : CNF.NClause := [(82,true),(5,false),(6,false),(7,true),(8,true),(9,true),(30,true)]
theorem inputList1341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1341 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) inputClause1341 (by decide) v hb
mask_input "1341|96|4835703278458517772567424"
def inputClause1342 : CNF.NClause := [(82,false),(5,true),(6,false),(7,true),(8,true),(9,true),(30,true)]
theorem inputList1342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1342 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) inputClause1342 (by decide) v hb
mask_input "1342|4835703278458516698824768|1073742752"
def inputClause1343 : CNF.NClause := [(82,false),(5,false),(6,true),(7,true),(8,true),(9,true),(30,true)]
theorem inputList1343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1343 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) inputClause1343 (by decide) v hb
mask_input "1343|4835703278458516698824736|1073742784"
def inputClause1345 : CNF.NClause := [(83,true),(4,false),(5,false),(11,false),(17,false),(23,false),(26,false)]
theorem inputList1345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1345 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1345 (by decide) v hb
mask_input "1345|75630640|9671406556917033397649408"
def inputClause1346 : CNF.NClause := [(83,true),(4,true),(5,false),(11,false),(17,false),(23,false),(26,false)]
theorem inputList1346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1346 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1346 (by decide) v hb
mask_input "1346|75630624|9671406556917033397649424"
def inputClause1347 : CNF.NClause := [(83,true),(4,false),(5,true),(11,false),(17,false),(23,false),(26,false)]
theorem inputList1347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1347 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1347 (by decide) v hb
mask_input "1347|75630608|9671406556917033397649440"
def inputClause1348 : CNF.NClause := [(83,true),(4,true),(5,true),(11,false),(17,false),(23,false),(26,false)]
theorem inputList1348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1348 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1348 (by decide) v hb
mask_input "1348|75630592|9671406556917033397649456"
def inputClause1349 : CNF.NClause := [(83,true),(4,false),(5,false),(11,true),(17,false),(23,false),(26,false)]
theorem inputList1349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1349 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1349 (by decide) v hb
mask_input "1349|75628592|9671406556917033397651456"
def inputClause1350 : CNF.NClause := [(83,true),(4,true),(5,false),(11,true),(17,false),(23,false),(26,false)]
theorem inputList1350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1350 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1350 (by decide) v hb
mask_input "1350|75628576|9671406556917033397651472"
def inputClause1351 : CNF.NClause := [(83,true),(4,false),(5,true),(11,true),(17,false),(23,false),(26,false)]
theorem inputList1351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1351 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1351 (by decide) v hb
mask_input "1351|75628560|9671406556917033397651488"
def inputClause1352 : CNF.NClause := [(83,true),(4,true),(5,true),(11,true),(17,false),(23,false),(26,false)]
theorem inputList1352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1352 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1352 (by decide) v hb
mask_input "1352|75628544|9671406556917033397651504"
def inputClause1353 : CNF.NClause := [(83,true),(4,false),(5,false),(11,false),(17,true),(23,false),(26,false)]
theorem inputList1353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1353 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1353 (by decide) v hb
mask_input "1353|75499568|9671406556917033397780480"
def inputClause1354 : CNF.NClause := [(83,true),(4,true),(5,false),(11,false),(17,true),(23,false),(26,false)]
theorem inputList1354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1354 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1354 (by decide) v hb
mask_input "1354|75499552|9671406556917033397780496"
def inputClause1355 : CNF.NClause := [(83,true),(4,false),(5,true),(11,false),(17,true),(23,false),(26,false)]
theorem inputList1355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1355 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1355 (by decide) v hb
mask_input "1355|75499536|9671406556917033397780512"
def inputClause1356 : CNF.NClause := [(83,true),(4,true),(5,true),(11,false),(17,true),(23,false),(26,false)]
theorem inputList1356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1356 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1356 (by decide) v hb
mask_input "1356|75499520|9671406556917033397780528"
def inputClause1357 : CNF.NClause := [(83,true),(4,false),(5,false),(11,true),(17,true),(23,false),(26,false)]
theorem inputList1357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1357 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1357 (by decide) v hb
mask_input "1357|75497520|9671406556917033397782528"
def inputClause1358 : CNF.NClause := [(83,true),(4,true),(5,false),(11,true),(17,true),(23,false),(26,false)]
theorem inputList1358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1358 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1358 (by decide) v hb
mask_input "1358|75497504|9671406556917033397782544"
def inputClause1359 : CNF.NClause := [(83,true),(4,false),(5,true),(11,true),(17,true),(23,false),(26,false)]
theorem inputList1359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1359 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1359 (by decide) v hb
mask_input "1359|75497488|9671406556917033397782560"
def inputClause1360 : CNF.NClause := [(83,true),(4,true),(5,true),(11,true),(17,true),(23,false),(26,false)]
theorem inputList1360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1360 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1360 (by decide) v hb
mask_input "1360|75497472|9671406556917033397782576"
def inputClause1361 : CNF.NClause := [(83,true),(4,false),(5,false),(11,false),(17,false),(23,true),(26,false)]
theorem inputList1361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1361 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1361 (by decide) v hb
mask_input "1361|67242032|9671406556917033406038016"
def inputClause1362 : CNF.NClause := [(83,true),(4,true),(5,false),(11,false),(17,false),(23,true),(26,false)]
theorem inputList1362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1362 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1362 (by decide) v hb
mask_input "1362|67242016|9671406556917033406038032"
def inputClause1363 : CNF.NClause := [(83,true),(4,false),(5,true),(11,false),(17,false),(23,true),(26,false)]
theorem inputList1363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1363 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1363 (by decide) v hb
mask_input "1363|67242000|9671406556917033406038048"
def inputClause1364 : CNF.NClause := [(83,true),(4,true),(5,true),(11,false),(17,false),(23,true),(26,false)]
theorem inputList1364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1364 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1364 (by decide) v hb
mask_input "1364|67241984|9671406556917033406038064"
def inputClause1365 : CNF.NClause := [(83,true),(4,false),(5,false),(11,true),(17,false),(23,true),(26,false)]
theorem inputList1365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1365 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1365 (by decide) v hb
mask_input "1365|67239984|9671406556917033406040064"
def inputClause1366 : CNF.NClause := [(83,true),(4,true),(5,false),(11,true),(17,false),(23,true),(26,false)]
theorem inputList1366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1366 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1366 (by decide) v hb
mask_input "1366|67239968|9671406556917033406040080"
def inputClause1367 : CNF.NClause := [(83,true),(4,false),(5,true),(11,true),(17,false),(23,true),(26,false)]
theorem inputList1367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1367 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1367 (by decide) v hb
mask_input "1367|67239952|9671406556917033406040096"
def inputClause1368 : CNF.NClause := [(83,true),(4,true),(5,true),(11,true),(17,false),(23,true),(26,false)]
theorem inputList1368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1368 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1368 (by decide) v hb
mask_input "1368|67239936|9671406556917033406040112"
def inputClause1369 : CNF.NClause := [(83,true),(4,false),(5,false),(11,false),(17,true),(23,true),(26,false)]
theorem inputList1369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1369 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1369 (by decide) v hb
mask_input "1369|67110960|9671406556917033406169088"
def inputClause1370 : CNF.NClause := [(83,true),(4,true),(5,false),(11,false),(17,true),(23,true),(26,false)]
theorem inputList1370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1370 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1370 (by decide) v hb
mask_input "1370|67110944|9671406556917033406169104"
def inputClause1371 : CNF.NClause := [(83,true),(4,false),(5,true),(11,false),(17,true),(23,true),(26,false)]
theorem inputList1371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1371 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1371 (by decide) v hb
mask_input "1371|67110928|9671406556917033406169120"
end Percolation.MaskChain
