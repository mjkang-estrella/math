import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause1254 : CNF.NClause := [(81,true),(1,true),(9,false),(12,true),(15,false),(23,false),(28,true)]
theorem inputList1254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1254 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1254 (by decide) v hb
mask_input "1254|8421888|2417851639229258617851906"
def inputClause1255 : CNF.NClause := [(81,true),(1,false),(9,true),(12,true),(15,false),(23,false),(28,true)]
theorem inputList1255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1255 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1255 (by decide) v hb
mask_input "1255|8421378|2417851639229258617852416"
def inputClause1256 : CNF.NClause := [(81,true),(1,true),(9,true),(12,true),(15,false),(23,false),(28,true)]
theorem inputList1256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1256 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1256 (by decide) v hb
mask_input "1256|8421376|2417851639229258617852418"
def inputClause1257 : CNF.NClause := [(81,true),(1,false),(9,false),(12,false),(15,true),(23,false),(28,true)]
theorem inputList1257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1257 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1257 (by decide) v hb
mask_input "1257|8393218|2417851639229258617880576"
def inputClause1258 : CNF.NClause := [(81,true),(1,true),(9,false),(12,false),(15,true),(23,false),(28,true)]
theorem inputList1258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1258 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1258 (by decide) v hb
mask_input "1258|8393216|2417851639229258617880578"
def inputClause1259 : CNF.NClause := [(81,true),(1,false),(9,true),(12,false),(15,true),(23,false),(28,true)]
theorem inputList1259 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1259 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1259 (by decide) v hb
mask_input "1259|8392706|2417851639229258617881088"
def inputClause1260 : CNF.NClause := [(81,true),(1,true),(9,true),(12,false),(15,true),(23,false),(28,true)]
theorem inputList1260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1260 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1260 (by decide) v hb
mask_input "1260|8392704|2417851639229258617881090"
def inputClause1261 : CNF.NClause := [(81,true),(1,false),(9,false),(12,true),(15,true),(23,false),(28,true)]
theorem inputList1261 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1261 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1261 (by decide) v hb
mask_input "1261|8389122|2417851639229258617884672"
def inputClause1262 : CNF.NClause := [(81,true),(1,true),(9,false),(12,true),(15,true),(23,false),(28,true)]
theorem inputList1262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1262 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1262 (by decide) v hb
mask_input "1262|8389120|2417851639229258617884674"
def inputClause1263 : CNF.NClause := [(81,true),(1,false),(9,true),(12,true),(15,true),(23,false),(28,true)]
theorem inputList1263 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1263 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1263 (by decide) v hb
mask_input "1263|8388610|2417851639229258617885184"
def inputClause1265 : CNF.NClause := [(81,true),(1,false),(9,false),(12,false),(15,false),(23,true),(28,true)]
theorem inputList1265 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1265 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1265 (by decide) v hb
mask_input "1265|37378|2417851639229258626236416"
def inputClause1266 : CNF.NClause := [(81,true),(1,true),(9,false),(12,false),(15,false),(23,true),(28,true)]
theorem inputList1266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1266 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1266 (by decide) v hb
mask_input "1266|37376|2417851639229258626236418"
def inputClause1267 : CNF.NClause := [(81,true),(1,false),(9,true),(12,false),(15,false),(23,true),(28,true)]
theorem inputList1267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1267 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1267 (by decide) v hb
mask_input "1267|36866|2417851639229258626236928"
def inputClause1268 : CNF.NClause := [(81,true),(1,true),(9,true),(12,false),(15,false),(23,true),(28,true)]
theorem inputList1268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1268 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1268 (by decide) v hb
mask_input "1268|36864|2417851639229258626236930"
def inputClause1269 : CNF.NClause := [(81,true),(1,false),(9,false),(12,true),(15,false),(23,true),(28,true)]
theorem inputList1269 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1269 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1269 (by decide) v hb
mask_input "1269|33282|2417851639229258626240512"
def inputClause1270 : CNF.NClause := [(81,true),(1,true),(9,false),(12,true),(15,false),(23,true),(28,true)]
theorem inputList1270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1270 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1270 (by decide) v hb
mask_input "1270|33280|2417851639229258626240514"
def inputClause1271 : CNF.NClause := [(81,true),(1,false),(9,true),(12,true),(15,false),(23,true),(28,true)]
theorem inputList1271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1271 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1271 (by decide) v hb
mask_input "1271|32770|2417851639229258626241024"
def inputClause1273 : CNF.NClause := [(81,true),(1,false),(9,false),(12,false),(15,true),(23,true),(28,true)]
theorem inputList1273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1273 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1273 (by decide) v hb
mask_input "1273|4610|2417851639229258626269184"
def inputClause1274 : CNF.NClause := [(81,true),(1,true),(9,false),(12,false),(15,true),(23,true),(28,true)]
theorem inputList1274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1274 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1274 (by decide) v hb
mask_input "1274|4608|2417851639229258626269186"
def inputClause1275 : CNF.NClause := [(81,true),(1,false),(9,true),(12,false),(15,true),(23,true),(28,true)]
theorem inputList1275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1275 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1275 (by decide) v hb
mask_input "1275|4098|2417851639229258626269696"
def inputClause1277 : CNF.NClause := [(81,true),(1,false),(9,false),(12,true),(15,true),(23,true),(28,true)]
theorem inputList1277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1277 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1277 (by decide) v hb
mask_input "1277|514|2417851639229258626273280"
def inputClause1280 : CNF.NClause := [(81,false),(1,true),(9,true),(12,true),(15,true),(23,true),(28,true)]
theorem inputList1280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1280 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1280 (by decide) v hb
mask_input "1280|2417851639229258349412352|276861442"
def inputClause1313 : CNF.NClause := [(82,true),(5,false),(6,false),(7,false),(8,false),(9,false),(30,true)]
theorem inputList1313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1313 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) inputClause1313 (by decide) v hb
mask_input "1313|992|4835703278458517772566528"
def inputClause1314 : CNF.NClause := [(82,true),(5,true),(6,false),(7,false),(8,false),(9,false),(30,true)]
theorem inputList1314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1314 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) inputClause1314 (by decide) v hb
mask_input "1314|960|4835703278458517772566560"
def inputClause1315 : CNF.NClause := [(82,true),(5,false),(6,true),(7,false),(8,false),(9,false),(30,true)]
theorem inputList1315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1315 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) inputClause1315 (by decide) v hb
mask_input "1315|928|4835703278458517772566592"
def inputClause1316 : CNF.NClause := [(82,true),(5,true),(6,true),(7,false),(8,false),(9,false),(30,true)]
theorem inputList1316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1316 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) inputClause1316 (by decide) v hb
mask_input "1316|896|4835703278458517772566624"
def inputClause1317 : CNF.NClause := [(82,true),(5,false),(6,false),(7,true),(8,false),(9,false),(30,true)]
theorem inputList1317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1317 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) inputClause1317 (by decide) v hb
mask_input "1317|864|4835703278458517772566656"
def inputClause1318 : CNF.NClause := [(82,true),(5,true),(6,false),(7,true),(8,false),(9,false),(30,true)]
theorem inputList1318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1318 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) inputClause1318 (by decide) v hb
mask_input "1318|832|4835703278458517772566688"
def inputClause1319 : CNF.NClause := [(82,true),(5,false),(6,true),(7,true),(8,false),(9,false),(30,true)]
theorem inputList1319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1319 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) inputClause1319 (by decide) v hb
mask_input "1319|800|4835703278458517772566720"
def inputClause1320 : CNF.NClause := [(82,true),(5,true),(6,true),(7,true),(8,false),(9,false),(30,true)]
theorem inputList1320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1320 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) inputClause1320 (by decide) v hb
mask_input "1320|768|4835703278458517772566752"
def inputClause1321 : CNF.NClause := [(82,true),(5,false),(6,false),(7,false),(8,true),(9,false),(30,true)]
theorem inputList1321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1321 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) inputClause1321 (by decide) v hb
mask_input "1321|736|4835703278458517772566784"
def inputClause1322 : CNF.NClause := [(82,true),(5,true),(6,false),(7,false),(8,true),(9,false),(30,true)]
theorem inputList1322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1322 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) inputClause1322 (by decide) v hb
mask_input "1322|704|4835703278458517772566816"
def inputClause1323 : CNF.NClause := [(82,true),(5,false),(6,true),(7,false),(8,true),(9,false),(30,true)]
theorem inputList1323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1323 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) inputClause1323 (by decide) v hb
mask_input "1323|672|4835703278458517772566848"
def inputClause1324 : CNF.NClause := [(82,true),(5,true),(6,true),(7,false),(8,true),(9,false),(30,true)]
theorem inputList1324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1324 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) inputClause1324 (by decide) v hb
mask_input "1324|640|4835703278458517772566880"
def inputClause1325 : CNF.NClause := [(82,true),(5,false),(6,false),(7,true),(8,true),(9,false),(30,true)]
theorem inputList1325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1325 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) inputClause1325 (by decide) v hb
mask_input "1325|608|4835703278458517772566912"
def inputClause1326 : CNF.NClause := [(82,true),(5,true),(6,false),(7,true),(8,true),(9,false),(30,true)]
theorem inputList1326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1326 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) inputClause1326 (by decide) v hb
mask_input "1326|576|4835703278458517772566944"
def inputClause1327 : CNF.NClause := [(82,true),(5,false),(6,true),(7,true),(8,true),(9,false),(30,true)]
theorem inputList1327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1327 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) inputClause1327 (by decide) v hb
mask_input "1327|544|4835703278458517772566976"
def inputClause1328 : CNF.NClause := [(82,false),(5,true),(6,true),(7,true),(8,true),(9,false),(30,true)]
theorem inputList1328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1328 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) inputClause1328 (by decide) v hb
mask_input "1328|4835703278458516698825216|1073742304"
def inputClause1329 : CNF.NClause := [(82,true),(5,false),(6,false),(7,false),(8,false),(9,true),(30,true)]
theorem inputList1329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1329 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) inputClause1329 (by decide) v hb
mask_input "1329|480|4835703278458517772567040"
def inputClause1330 : CNF.NClause := [(82,true),(5,true),(6,false),(7,false),(8,false),(9,true),(30,true)]
theorem inputList1330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1330 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 20) 20) (activationA_mem 20) inputClause1330 (by decide) v hb
mask_input "1330|448|4835703278458517772567072"
end Percolation.MaskChain
