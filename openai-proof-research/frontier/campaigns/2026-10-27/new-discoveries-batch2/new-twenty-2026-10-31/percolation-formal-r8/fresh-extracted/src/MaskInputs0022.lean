import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause1211 : CNF.NClause := [(80,true),(3,false),(7,true),(11,false),(15,true),(24,true),(29,true)]
theorem inputList1211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1211 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1211 (by decide) v hb
mask_input "1211|2056|1208925819614629728387200"
def inputClause1213 : CNF.NClause := [(80,true),(3,false),(7,false),(11,true),(15,true),(24,true),(29,true)]
theorem inputList1213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1213 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1213 (by decide) v hb
mask_input "1213|136|1208925819614629728389120"
def inputClause1216 : CNF.NClause := [(80,false),(3,true),(7,true),(11,true),(15,true),(24,true),(29,true)]
theorem inputList1216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1216 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1216 (by decide) v hb
mask_input "1216|1208925819614629174706176|553683080"
def inputClause1217 : CNF.NClause := [(81,true),(1,false),(9,false),(12,false),(15,false),(23,false),(28,false)]
theorem inputList1217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1217 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1217 (by decide) v hb
mask_input "1217|276861442|2417851639229258349412352"
def inputClause1218 : CNF.NClause := [(81,true),(1,true),(9,false),(12,false),(15,false),(23,false),(28,false)]
theorem inputList1218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1218 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1218 (by decide) v hb
mask_input "1218|276861440|2417851639229258349412354"
def inputClause1219 : CNF.NClause := [(81,true),(1,false),(9,true),(12,false),(15,false),(23,false),(28,false)]
theorem inputList1219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1219 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1219 (by decide) v hb
mask_input "1219|276860930|2417851639229258349412864"
def inputClause1220 : CNF.NClause := [(81,true),(1,true),(9,true),(12,false),(15,false),(23,false),(28,false)]
theorem inputList1220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1220 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1220 (by decide) v hb
mask_input "1220|276860928|2417851639229258349412866"
def inputClause1221 : CNF.NClause := [(81,true),(1,false),(9,false),(12,true),(15,false),(23,false),(28,false)]
theorem inputList1221 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1221 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1221 (by decide) v hb
mask_input "1221|276857346|2417851639229258349416448"
def inputClause1222 : CNF.NClause := [(81,true),(1,true),(9,false),(12,true),(15,false),(23,false),(28,false)]
theorem inputList1222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1222 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1222 (by decide) v hb
mask_input "1222|276857344|2417851639229258349416450"
def inputClause1223 : CNF.NClause := [(81,true),(1,false),(9,true),(12,true),(15,false),(23,false),(28,false)]
theorem inputList1223 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1223 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1223 (by decide) v hb
mask_input "1223|276856834|2417851639229258349416960"
def inputClause1224 : CNF.NClause := [(81,true),(1,true),(9,true),(12,true),(15,false),(23,false),(28,false)]
theorem inputList1224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1224 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1224 (by decide) v hb
mask_input "1224|276856832|2417851639229258349416962"
def inputClause1225 : CNF.NClause := [(81,true),(1,false),(9,false),(12,false),(15,true),(23,false),(28,false)]
theorem inputList1225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1225 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1225 (by decide) v hb
mask_input "1225|276828674|2417851639229258349445120"
def inputClause1226 : CNF.NClause := [(81,true),(1,true),(9,false),(12,false),(15,true),(23,false),(28,false)]
theorem inputList1226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1226 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1226 (by decide) v hb
mask_input "1226|276828672|2417851639229258349445122"
def inputClause1227 : CNF.NClause := [(81,true),(1,false),(9,true),(12,false),(15,true),(23,false),(28,false)]
theorem inputList1227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1227 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1227 (by decide) v hb
mask_input "1227|276828162|2417851639229258349445632"
def inputClause1228 : CNF.NClause := [(81,true),(1,true),(9,true),(12,false),(15,true),(23,false),(28,false)]
theorem inputList1228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1228 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1228 (by decide) v hb
mask_input "1228|276828160|2417851639229258349445634"
def inputClause1229 : CNF.NClause := [(81,true),(1,false),(9,false),(12,true),(15,true),(23,false),(28,false)]
theorem inputList1229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1229 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1229 (by decide) v hb
mask_input "1229|276824578|2417851639229258349449216"
def inputClause1230 : CNF.NClause := [(81,true),(1,true),(9,false),(12,true),(15,true),(23,false),(28,false)]
theorem inputList1230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1230 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1230 (by decide) v hb
mask_input "1230|276824576|2417851639229258349449218"
def inputClause1231 : CNF.NClause := [(81,true),(1,false),(9,true),(12,true),(15,true),(23,false),(28,false)]
theorem inputList1231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1231 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1231 (by decide) v hb
mask_input "1231|276824066|2417851639229258349449728"
def inputClause1232 : CNF.NClause := [(81,true),(1,true),(9,true),(12,true),(15,true),(23,false),(28,false)]
theorem inputList1232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1232 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1232 (by decide) v hb
mask_input "1232|276824064|2417851639229258349449730"
def inputClause1233 : CNF.NClause := [(81,true),(1,false),(9,false),(12,false),(15,false),(23,true),(28,false)]
theorem inputList1233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1233 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1233 (by decide) v hb
mask_input "1233|268472834|2417851639229258357800960"
def inputClause1234 : CNF.NClause := [(81,true),(1,true),(9,false),(12,false),(15,false),(23,true),(28,false)]
theorem inputList1234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1234 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1234 (by decide) v hb
mask_input "1234|268472832|2417851639229258357800962"
def inputClause1235 : CNF.NClause := [(81,true),(1,false),(9,true),(12,false),(15,false),(23,true),(28,false)]
theorem inputList1235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1235 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1235 (by decide) v hb
mask_input "1235|268472322|2417851639229258357801472"
def inputClause1236 : CNF.NClause := [(81,true),(1,true),(9,true),(12,false),(15,false),(23,true),(28,false)]
theorem inputList1236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1236 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1236 (by decide) v hb
mask_input "1236|268472320|2417851639229258357801474"
def inputClause1237 : CNF.NClause := [(81,true),(1,false),(9,false),(12,true),(15,false),(23,true),(28,false)]
theorem inputList1237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1237 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1237 (by decide) v hb
mask_input "1237|268468738|2417851639229258357805056"
def inputClause1238 : CNF.NClause := [(81,true),(1,true),(9,false),(12,true),(15,false),(23,true),(28,false)]
theorem inputList1238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1238 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1238 (by decide) v hb
mask_input "1238|268468736|2417851639229258357805058"
def inputClause1239 : CNF.NClause := [(81,true),(1,false),(9,true),(12,true),(15,false),(23,true),(28,false)]
theorem inputList1239 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1239 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1239 (by decide) v hb
mask_input "1239|268468226|2417851639229258357805568"
def inputClause1240 : CNF.NClause := [(81,true),(1,true),(9,true),(12,true),(15,false),(23,true),(28,false)]
theorem inputList1240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1240 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1240 (by decide) v hb
mask_input "1240|268468224|2417851639229258357805570"
def inputClause1241 : CNF.NClause := [(81,true),(1,false),(9,false),(12,false),(15,true),(23,true),(28,false)]
theorem inputList1241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1241 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1241 (by decide) v hb
mask_input "1241|268440066|2417851639229258357833728"
def inputClause1242 : CNF.NClause := [(81,true),(1,true),(9,false),(12,false),(15,true),(23,true),(28,false)]
theorem inputList1242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1242 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1242 (by decide) v hb
mask_input "1242|268440064|2417851639229258357833730"
def inputClause1243 : CNF.NClause := [(81,true),(1,false),(9,true),(12,false),(15,true),(23,true),(28,false)]
theorem inputList1243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1243 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1243 (by decide) v hb
mask_input "1243|268439554|2417851639229258357834240"
def inputClause1244 : CNF.NClause := [(81,true),(1,true),(9,true),(12,false),(15,true),(23,true),(28,false)]
theorem inputList1244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1244 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1244 (by decide) v hb
mask_input "1244|268439552|2417851639229258357834242"
def inputClause1245 : CNF.NClause := [(81,true),(1,false),(9,false),(12,true),(15,true),(23,true),(28,false)]
theorem inputList1245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1245 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1245 (by decide) v hb
mask_input "1245|268435970|2417851639229258357837824"
def inputClause1246 : CNF.NClause := [(81,true),(1,true),(9,false),(12,true),(15,true),(23,true),(28,false)]
theorem inputList1246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1246 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1246 (by decide) v hb
mask_input "1246|268435968|2417851639229258357837826"
def inputClause1247 : CNF.NClause := [(81,true),(1,false),(9,true),(12,true),(15,true),(23,true),(28,false)]
theorem inputList1247 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1247 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1247 (by decide) v hb
mask_input "1247|268435458|2417851639229258357838336"
def inputClause1248 : CNF.NClause := [(81,false),(1,true),(9,true),(12,true),(15,true),(23,true),(28,false)]
theorem inputList1248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1248 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1248 (by decide) v hb
mask_input "1248|2417851639229258617847808|8425986"
def inputClause1249 : CNF.NClause := [(81,true),(1,false),(9,false),(12,false),(15,false),(23,false),(28,true)]
theorem inputList1249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1249 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1249 (by decide) v hb
mask_input "1249|8425986|2417851639229258617847808"
def inputClause1250 : CNF.NClause := [(81,true),(1,true),(9,false),(12,false),(15,false),(23,false),(28,true)]
theorem inputList1250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1250 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1250 (by decide) v hb
mask_input "1250|8425984|2417851639229258617847810"
def inputClause1251 : CNF.NClause := [(81,true),(1,false),(9,true),(12,false),(15,false),(23,false),(28,true)]
theorem inputList1251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1251 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1251 (by decide) v hb
mask_input "1251|8425474|2417851639229258617848320"
def inputClause1252 : CNF.NClause := [(81,true),(1,true),(9,true),(12,false),(15,false),(23,false),(28,true)]
theorem inputList1252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1252 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1252 (by decide) v hb
mask_input "1252|8425472|2417851639229258617848322"
def inputClause1253 : CNF.NClause := [(81,true),(1,false),(9,false),(12,true),(15,false),(23,false),(28,true)]
theorem inputList1253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1253 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 19) 19) (activationA_mem 19) inputClause1253 (by decide) v hb
mask_input "1253|8421890|2417851639229258617851904"
end Percolation.MaskChain
