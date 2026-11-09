import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause1080 : CNF.NClause := [(78,false),(4,true),(6,true),(13,true),(15,false),(22,true),(27,true)]
theorem inputList1080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1080 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1080 (by decide) v hb
mask_input "1080|302231454903657293709312|138420304"
def inputClause1084 : CNF.NClause := [(78,false),(4,true),(6,true),(13,false),(15,true),(22,true),(27,true)]
theorem inputList1084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1084 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1084 (by decide) v hb
mask_input "1084|302231454903657293684736|138444880"
def inputClause1086 : CNF.NClause := [(78,false),(4,true),(6,false),(13,true),(15,true),(22,true),(27,true)]
theorem inputList1086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1086 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1086 (by decide) v hb
mask_input "1086|302231454903657293676608|138453008"
def inputClause1087 : CNF.NClause := [(78,false),(4,false),(6,true),(13,true),(15,true),(22,true),(27,true)]
theorem inputList1087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1087 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1087 (by decide) v hb
mask_input "1087|302231454903657293676560|138453056"
def inputClause1200 : CNF.NClause := [(80,false),(3,true),(7,true),(11,true),(15,true),(24,false),(29,true)]
theorem inputList1200 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1200 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1200 (by decide) v hb
mask_input "1200|1208925819614629191483392|536905864"
def inputClause1208 : CNF.NClause := [(80,false),(3,true),(7,true),(11,true),(15,false),(24,true),(29,true)]
theorem inputList1208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1208 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1208 (by decide) v hb
mask_input "1208|1208925819614629174738944|553650312"
def inputClause1212 : CNF.NClause := [(80,false),(3,true),(7,true),(11,false),(15,true),(24,true),(29,true)]
theorem inputList1212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1212 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1212 (by decide) v hb
mask_input "1212|1208925819614629174708224|553681032"
def inputClause1214 : CNF.NClause := [(80,false),(3,true),(7,false),(11,true),(15,true),(24,true),(29,true)]
theorem inputList1214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1214 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1214 (by decide) v hb
mask_input "1214|1208925819614629174706304|553682952"
def inputClause1215 : CNF.NClause := [(80,false),(3,false),(7,true),(11,true),(15,true),(24,true),(29,true)]
theorem inputList1215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1215 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1215 (by decide) v hb
mask_input "1215|1208925819614629174706184|553683072"
def inputClause1264 : CNF.NClause := [(81,false),(1,true),(9,true),(12,true),(15,true),(23,false),(28,true)]
theorem inputList1264 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1264 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1264 (by decide) v hb
mask_input "1264|2417851639229258357800960|268472834"
def inputClause1272 : CNF.NClause := [(81,false),(1,true),(9,true),(12,true),(15,false),(23,true),(28,true)]
theorem inputList1272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1272 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1272 (by decide) v hb
mask_input "1272|2417851639229258349445120|276828674"
def inputClause1276 : CNF.NClause := [(81,false),(1,true),(9,true),(12,false),(15,true),(23,true),(28,true)]
theorem inputList1276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1276 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1276 (by decide) v hb
mask_input "1276|2417851639229258349416448|276857346"
def inputClause1278 : CNF.NClause := [(81,false),(1,true),(9,false),(12,true),(15,true),(23,true),(28,true)]
theorem inputList1278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1278 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1278 (by decide) v hb
mask_input "1278|2417851639229258349412864|276860930"
def inputClause1279 : CNF.NClause := [(81,false),(1,false),(9,true),(12,true),(15,true),(23,true),(28,true)]
theorem inputList1279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1279 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1279 (by decide) v hb
mask_input "1279|2417851639229258349412354|276861440"
def inputClause1376 : CNF.NClause := [(83,false),(4,true),(5,true),(11,true),(17,true),(23,true),(26,false)]
theorem inputList1376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1376 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1376 (by decide) v hb
mask_input "1376|9671406556917033464758272|8521776"
def inputClause1392 : CNF.NClause := [(83,false),(4,true),(5,true),(11,true),(17,true),(23,false),(26,true)]
theorem inputList1392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1392 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1392 (by decide) v hb
mask_input "1392|9671406556917033406038016|67242032"
def inputClause1400 : CNF.NClause := [(83,false),(4,true),(5,true),(11,true),(17,false),(23,true),(26,true)]
theorem inputList1400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1400 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1400 (by decide) v hb
mask_input "1400|9671406556917033397780480|75499568"
def inputClause1404 : CNF.NClause := [(83,false),(4,true),(5,true),(11,false),(17,true),(23,true),(26,true)]
theorem inputList1404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1404 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1404 (by decide) v hb
mask_input "1404|9671406556917033397651456|75628592"
def inputClause1407 : CNF.NClause := [(83,false),(4,false),(5,true),(11,true),(17,true),(23,true),(26,true)]
theorem inputList1407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1407 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) inputClause1407 (by decide) v hb
mask_input "1407|9671406556917033397649424|75630624"
def inputClause1456 : CNF.NClause := [(84,false),(2,true),(5,true),(13,true),(16,true),(24,false),(28,true)]
theorem inputList1456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1456 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1456 (by decide) v hb
mask_input "1456|19342813113834066812076032|268509220"
def inputClause1464 : CNF.NClause := [(84,false),(2,true),(5,true),(13,true),(16,false),(24,true),(28,true)]
theorem inputList1464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1464 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1464 (by decide) v hb
mask_input "1464|19342813113834066795364352|285220900"
def inputClause1468 : CNF.NClause := [(84,false),(2,true),(5,true),(13,false),(16,true),(24,true),(28,true)]
theorem inputList1468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1468 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1468 (by decide) v hb
mask_input "1468|19342813113834066795307008|285278244"
def inputClause1470 : CNF.NClause := [(84,false),(2,true),(5,false),(13,true),(16,true),(24,true),(28,true)]
theorem inputList1470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1470 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1470 (by decide) v hb
mask_input "1470|19342813113834066795298848|285286404"
def inputClause1471 : CNF.NClause := [(84,false),(2,false),(5,true),(13,true),(16,true),(24,true),(28,true)]
theorem inputList1471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1471 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) inputClause1471 (by decide) v hb
mask_input "1471|19342813113834066795298820|285286432"
def inputClause1504 : CNF.NClause := [(85,false),(3,true),(5,true),(12,true),(19,true),(21,true),(27,false)]
theorem inputList1504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1504 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) inputClause1504 (by decide) v hb
mask_input "1504|38685626227668133724815360|2625576"
def inputClause2032 : CNF.NClause := [(93,false),(56,true),(57,true),(58,true),(59,true),(60,false),(61,true)]
theorem inputList2032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2032 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2032 (by decide) v hb
mask_input "2032|9903520315435963703799840768|3386706919782612992"
def inputClause2040 : CNF.NClause := [(93,false),(56,true),(57,true),(58,true),(59,false),(60,true),(61,true)]
theorem inputList2040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2040 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2040 (by decide) v hb
mask_input "2040|9903520314859502951496417280|3963167672086036480"
def inputClause2044 : CNF.NClause := [(93,false),(56,true),(57,true),(58,false),(59,true),(60,true),(61,true)]
theorem inputList2044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2044 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2044 (by decide) v hb
mask_input "2044|9903520314571272575344705536|4251398048237748224"
def inputClause2046 : CNF.NClause := [(93,false),(56,true),(57,false),(58,true),(59,true),(60,true),(61,true)]
theorem inputList2046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2046 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2046 (by decide) v hb
mask_input "2046|9903520314427157387268849664|4395513236313604096"
def inputClause2081 : CNF.NClause := [(94,true),(35,false),(40,false),(45,false),(50,false),(55,false),(56,true)]
theorem inputList2081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2081 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2081 (by decide) v hb
mask_input "2081|37191015169261568|19807040628638141992423915520"
def inputClause2096 : CNF.NClause := [(94,false),(35,true),(40,true),(45,true),(50,true),(55,false),(56,true)]
theorem inputList2096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2096 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2096 (by decide) v hb
mask_input "2096|19807040628602113195404951552|73219812188225536"
def inputClause2104 : CNF.NClause := [(94,false),(35,true),(40,true),(45,true),(50,false),(55,true),(56,true)]
theorem inputList2104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2104 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2104 (by decide) v hb
mask_input "2104|19807040628567210298292830208|108122709300346880"
def inputClause2108 : CNF.NClause := [(94,false),(35,true),(40,true),(45,false),(50,true),(55,true),(56,true)]
theorem inputList2108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2108 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2108 (by decide) v hb
mask_input "2108|19807040628566119582758076416|109213424835100672"
def inputClause2110 : CNF.NClause := [(94,false),(35,true),(40,false),(45,true),(50,true),(55,true),(56,true)]
theorem inputList2110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2110 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) inputClause2110 (by decide) v hb
mask_input "2110|19807040628566085497897615360|109247509695561728"
def inputClause2160 : CNF.NClause := [(95,false),(33,true),(38,true),(43,true),(48,true),(53,false),(56,true)]
theorem inputList2160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2160 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2160 (by decide) v hb
mask_input "2160|39614081257141175996026716160|72348148575502336"
def inputClause2168 : CNF.NClause := [(95,false),(33,true),(38,true),(43,true),(48,false),(53,true),(56,true)]
theorem inputList2168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2168 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2168 (by decide) v hb
mask_input "2168|39614081257132450271748685824|81073872853532672"
def inputClause2172 : CNF.NClause := [(95,false),(33,true),(38,true),(43,false),(48,true),(53,true),(56,true)]
theorem inputList2172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2172 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2172 (by decide) v hb
mask_input "2172|39614081257132177592864997376|81346551737221120"
def inputClause2174 : CNF.NClause := [(95,false),(33,true),(38,false),(43,true),(48,true),(53,true),(56,true)]
theorem inputList2174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2174 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 2) 2) (activationX_mem 2) inputClause2174 (by decide) v hb
mask_input "2174|39614081257132169071649882112|81355072952336384"
def inputClause2224 : CNF.NClause := [(96,false),(34,true),(39,true),(44,true),(49,true),(54,false),(56,true)]
theorem inputList2224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2224 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2224 (by decide) v hb
mask_input "2224|79228162514282351992053432320|72638703113076736"
def inputClause2232 : CNF.NClause := [(96,false),(34,true),(39,true),(44,true),(49,false),(54,true),(56,true)]
theorem inputList2232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2232 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2232 (by decide) v hb
mask_input "2232|79228162514264900543497371648|90090151669137408"
end Percolation.MaskChain
