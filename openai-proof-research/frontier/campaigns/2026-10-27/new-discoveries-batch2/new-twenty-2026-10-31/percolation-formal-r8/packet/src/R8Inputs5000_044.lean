import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause6293 : CNF.NClause := [(49,false),(18,false),(65,false),(69,true),(73,false),(77,true),(86,false),(91,false)]
theorem inputList6293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6293 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6293 (by decide) v hb
mask_input "6293|2553260812653113653642657792|151706023262187352489984"
def inputClause6294 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,false),(77,true),(86,false),(91,false)]
theorem inputList6294 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6294 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6294 (by decide) v hb
mask_input "6294|2553260812653113653642395648|151706023262187352752128"
def inputClause6295 : CNF.NClause := [(49,false),(18,false),(65,true),(69,true),(73,false),(77,true),(86,false),(91,false)]
theorem inputList6295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6295 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6295 (by decide) v hb
mask_input "6295|2553260775759625506223554560|151742916750334771593216"
def inputClause6296 : CNF.NClause := [(49,false),(18,true),(65,true),(69,true),(73,false),(77,true),(86,false),(91,false)]
theorem inputList6296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6296 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6296 (by decide) v hb
mask_input "6296|2553260775759625506223292416|151742916750334771855360"
def inputClause6297 : CNF.NClause := [(49,false),(18,false),(65,false),(69,false),(73,true),(77,true),(86,false),(91,false)]
theorem inputList6297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6297 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6297 (by decide) v hb
mask_input "6297|2553251958215958273057882112|160560460417567937265664"
def inputClause6298 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,true),(77,true),(86,false),(91,false)]
theorem inputList6298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6298 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6298 (by decide) v hb
mask_input "6298|2553251958215958273057619968|160560460417567937527808"
def inputClause6299 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(73,true),(77,true),(86,false),(91,false)]
theorem inputList6299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6299 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6299 (by decide) v hb
mask_input "6299|2553251921322470125638778880|160597353905715356368896"
def inputClause6300 : CNF.NClause := [(49,false),(18,true),(65,true),(69,false),(73,true),(77,true),(86,false),(91,false)]
theorem inputList6300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6300 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6300 (by decide) v hb
mask_input "6300|2553251921322470125638516736|160597353905715356631040"
def inputClause6301 : CNF.NClause := [(49,false),(18,false),(65,false),(69,true),(73,true),(77,true),(86,false),(91,false)]
theorem inputList6301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6301 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6301 (by decide) v hb
mask_input "6301|2553251367920147914352230400|161150756227926642917376"
def inputClause6302 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,true),(77,true),(86,false),(91,false)]
theorem inputList6302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6302 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6302 (by decide) v hb
mask_input "6302|2553251367920147914351968256|161150756227926643179520"
def inputClause6303 : CNF.NClause := [(49,false),(18,false),(65,true),(69,true),(73,true),(77,true),(86,false),(91,false)]
theorem inputList6303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6303 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6303 (by decide) v hb
mask_input "6303|2553251331026659766933127168|161187649716074062020608"
def inputClause6304 : CNF.NClause := [(49,false),(18,true),(65,true),(69,true),(73,true),(77,true),(86,false),(91,false)]
theorem inputList6304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6304 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6304 (by decide) v hb
mask_input "6304|2553251331026659766932865024|161187649716074062282752"
def inputClause6305 : CNF.NClause := [(49,false),(18,false),(65,false),(69,false),(73,false),(77,false),(86,true),(91,false)]
theorem inputList6305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6305 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6305 (by decide) v hb
mask_input "6305|2476041266221039573813952512|77371252455336267181195264"
def inputClause6306 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,false),(77,false),(86,true),(91,false)]
theorem inputList6306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6306 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6306 (by decide) v hb
mask_input "6306|2476041266221039573813690368|77371252455336267181457408"
def inputClause6307 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(73,false),(77,false),(86,true),(91,false)]
theorem inputList6307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6307 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6307 (by decide) v hb
mask_input "6307|2476041229327551426394849280|77371289348824414600298496"
def inputClause6308 : CNF.NClause := [(49,false),(18,true),(65,true),(69,false),(73,false),(77,false),(86,true),(91,false)]
theorem inputList6308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6308 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6308 (by decide) v hb
mask_input "6308|2476041229327551426394587136|77371289348824414600560640"
def inputClause6309 : CNF.NClause := [(49,false),(18,false),(65,false),(69,true),(73,false),(77,false),(86,true),(91,false)]
theorem inputList6309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6309 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6309 (by decide) v hb
mask_input "6309|2476040675925229215108300800|77371842751146625886846976"
def inputClause6310 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,false),(77,false),(86,true),(91,false)]
theorem inputList6310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6310 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6310 (by decide) v hb
mask_input "6310|2476040675925229215108038656|77371842751146625887109120"
def inputClause6311 : CNF.NClause := [(49,false),(18,false),(65,true),(69,true),(73,false),(77,false),(86,true),(91,false)]
theorem inputList6311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6311 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6311 (by decide) v hb
mask_input "6311|2476040639031741067689197568|77371879644634773305950208"
def inputClause6312 : CNF.NClause := [(49,false),(18,true),(65,true),(69,true),(73,false),(77,false),(86,true),(91,false)]
theorem inputList6312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6312 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6312 (by decide) v hb
mask_input "6312|2476040639031741067688935424|77371879644634773306212352"
def inputClause6313 : CNF.NClause := [(49,false),(18,false),(65,false),(69,false),(73,true),(77,false),(86,true),(91,false)]
theorem inputList6313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6313 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6313 (by decide) v hb
mask_input "6313|2476031821488073834523525120|77380697188302006471622656"
def inputClause6314 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,true),(77,false),(86,true),(91,false)]
theorem inputList6314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6314 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6314 (by decide) v hb
mask_input "6314|2476031821488073834523262976|77380697188302006471884800"
def inputClause6315 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(73,true),(77,false),(86,true),(91,false)]
theorem inputList6315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6315 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6315 (by decide) v hb
mask_input "6315|2476031784594585687104421888|77380734081790153890725888"
def inputClause6316 : CNF.NClause := [(49,false),(18,true),(65,true),(69,false),(73,true),(77,false),(86,true),(91,false)]
theorem inputList6316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6316 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6316 (by decide) v hb
mask_input "6316|2476031784594585687104159744|77380734081790153890988032"
def inputClause6317 : CNF.NClause := [(49,false),(18,false),(65,false),(69,true),(73,true),(77,false),(86,true),(91,false)]
theorem inputList6317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6317 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6317 (by decide) v hb
mask_input "6317|2476031231192263475817873408|77381287484112365177274368"
def inputClause6318 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,true),(77,false),(86,true),(91,false)]
theorem inputList6318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6318 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6318 (by decide) v hb
mask_input "6318|2476031231192263475817611264|77381287484112365177536512"
def inputClause6319 : CNF.NClause := [(49,false),(18,false),(65,true),(69,true),(73,true),(77,false),(86,true),(91,false)]
theorem inputList6319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6319 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6319 (by decide) v hb
mask_input "6319|2476031194298775328398770176|77381324377600512596377600"
def inputClause6320 : CNF.NClause := [(49,false),(18,true),(65,true),(69,true),(73,true),(77,false),(86,true),(91,false)]
theorem inputList6320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6320 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6320 (by decide) v hb
mask_input "6320|2476031194298775328398508032|77381324377600512596639744"
def inputClause6321 : CNF.NClause := [(49,false),(18,false),(65,false),(69,false),(73,false),(77,true),(86,true),(91,false)]
theorem inputList6321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6321 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6321 (by decide) v hb
mask_input "6321|2475890150493587745167114240|77522368182788095828033536"
def inputClause6322 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,false),(77,true),(86,true),(91,false)]
theorem inputList6322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6322 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6322 (by decide) v hb
mask_input "6322|2475890150493587745166852096|77522368182788095828295680"
def inputClause6323 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(73,false),(77,true),(86,true),(91,false)]
theorem inputList6323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6323 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6323 (by decide) v hb
mask_input "6323|2475890113600099597748011008|77522405076276243247136768"
def inputClause6324 : CNF.NClause := [(49,false),(18,true),(65,true),(69,false),(73,false),(77,true),(86,true),(91,false)]
theorem inputList6324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6324 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6324 (by decide) v hb
mask_input "6324|2475890113600099597747748864|77522405076276243247398912"
def inputClause6326 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,false),(77,true),(86,true),(91,false)]
theorem inputList6326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6326 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6326 (by decide) v hb
mask_input "6326|2475889560197777386461200384|77522958478598454533947392"
def inputClause6327 : CNF.NClause := [(49,false),(18,false),(65,true),(69,true),(73,false),(77,true),(86,true),(91,false)]
theorem inputList6327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6327 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6327 (by decide) v hb
mask_input "6327|2475889523304289239042359296|77522995372086601952788480"
def inputClause6328 : CNF.NClause := [(49,false),(18,true),(65,true),(69,true),(73,false),(77,true),(86,true),(91,false)]
theorem inputList6328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6328 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6328 (by decide) v hb
mask_input "6328|2475889523304289239042097152|77522995372086601953050624"
def inputClause6329 : CNF.NClause := [(49,false),(18,false),(65,false),(69,false),(73,true),(77,true),(86,true),(91,false)]
theorem inputList6329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6329 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6329 (by decide) v hb
mask_input "6329|2475880705760622005876686848|77531812915753835118460928"
def inputClause6330 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,true),(77,true),(86,true),(91,false)]
theorem inputList6330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6330 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6330 (by decide) v hb
mask_input "6330|2475880705760622005876424704|77531812915753835118723072"
def inputClause6331 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(73,true),(77,true),(86,true),(91,false)]
theorem inputList6331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6331 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6331 (by decide) v hb
mask_input "6331|2475880668867133858457583616|77531849809241982537564160"
def inputClause6332 : CNF.NClause := [(49,false),(18,true),(65,true),(69,false),(73,true),(77,true),(86,true),(91,false)]
theorem inputList6332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6332 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6332 (by decide) v hb
mask_input "6332|2475880668867133858457321472|77531849809241982537826304"
def inputClause6333 : CNF.NClause := [(49,false),(18,false),(65,false),(69,true),(73,true),(77,true),(86,true),(91,false)]
theorem inputList6333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6333 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6333 (by decide) v hb
mask_input "6333|2475880115464811647171035136|77532403211564193824112640"
end Percolation.MaskChain
