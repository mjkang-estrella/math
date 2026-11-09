import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause2377 : CNF.NClause := [(99,true),(35,false),(39,false),(43,false),(47,true),(51,false),(60,false)]
theorem inputList2377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2377 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2377 (by decide) v hb
mask_input "2377|1155182684629106688|633825300114114841485839958016"
def inputClause2378 : CNF.NClause := [(99,true),(35,true),(39,false),(43,false),(47,true),(51,false),(60,false)]
theorem inputList2378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2378 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2378 (by decide) v hb
mask_input "2378|1155182650269368320|633825300114114841520199696384"
def inputClause2379 : CNF.NClause := [(99,true),(35,false),(39,true),(43,false),(47,true),(51,false),(60,false)]
theorem inputList2379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2379 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2379 (by decide) v hb
mask_input "2379|1155182134873292800|633825300114114842035595771904"
def inputClause2380 : CNF.NClause := [(99,true),(35,true),(39,true),(43,false),(47,true),(51,false),(60,false)]
theorem inputList2380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2380 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2380 (by decide) v hb
mask_input "2380|1155182100513554432|633825300114114842069955510272"
def inputClause2381 : CNF.NClause := [(99,true),(35,false),(39,false),(43,true),(47,true),(51,false),(60,false)]
theorem inputList2381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2381 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2381 (by decide) v hb
mask_input "2381|1155173888536084480|633825300114114850281932980224"
def inputClause2382 : CNF.NClause := [(99,true),(35,true),(39,false),(43,true),(47,true),(51,false),(60,false)]
theorem inputList2382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2382 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2382 (by decide) v hb
mask_input "2382|1155173854176346112|633825300114114850316292718592"
def inputClause2383 : CNF.NClause := [(99,true),(35,false),(39,true),(43,true),(47,true),(51,false),(60,false)]
theorem inputList2383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2383 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2383 (by decide) v hb
mask_input "2383|1155173338780270592|633825300114114850831688794112"
def inputClause2384 : CNF.NClause := [(99,true),(35,true),(39,true),(43,true),(47,true),(51,false),(60,false)]
theorem inputList2384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2384 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2384 (by decide) v hb
mask_input "2384|1155173304420532224|633825300114114850866048532480"
def inputClause2385 : CNF.NClause := [(99,true),(35,false),(39,false),(43,false),(47,false),(51,true),(60,false)]
theorem inputList2385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2385 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2385 (by decide) v hb
mask_input "2385|1153071622303776768|633825300114116952548165287936"
def inputClause2386 : CNF.NClause := [(99,true),(35,true),(39,false),(43,false),(47,false),(51,true),(60,false)]
theorem inputList2386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2386 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2386 (by decide) v hb
mask_input "2386|1153071587944038400|633825300114116952582525026304"
def inputClause2387 : CNF.NClause := [(99,true),(35,false),(39,true),(43,false),(47,false),(51,true),(60,false)]
theorem inputList2387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2387 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2387 (by decide) v hb
mask_input "2387|1153071072547962880|633825300114116953097921101824"
def inputClause2388 : CNF.NClause := [(99,true),(35,true),(39,true),(43,false),(47,false),(51,true),(60,false)]
theorem inputList2388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2388 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2388 (by decide) v hb
mask_input "2388|1153071038188224512|633825300114116953132280840192"
def inputClause2389 : CNF.NClause := [(99,true),(35,false),(39,false),(43,true),(47,false),(51,true),(60,false)]
theorem inputList2389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2389 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2389 (by decide) v hb
mask_input "2389|1153062826210754560|633825300114116961344258310144"
def inputClause2390 : CNF.NClause := [(99,true),(35,true),(39,false),(43,true),(47,false),(51,true),(60,false)]
theorem inputList2390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2390 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2390 (by decide) v hb
mask_input "2390|1153062791851016192|633825300114116961378618048512"
def inputClause2391 : CNF.NClause := [(99,true),(35,false),(39,true),(43,true),(47,false),(51,true),(60,false)]
theorem inputList2391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2391 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2391 (by decide) v hb
mask_input "2391|1153062276454940672|633825300114116961894014124032"
def inputClause2392 : CNF.NClause := [(99,true),(35,true),(39,true),(43,true),(47,false),(51,true),(60,false)]
theorem inputList2392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2392 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2392 (by decide) v hb
mask_input "2392|1153062242095202304|633825300114116961928373862400"
def inputClause2393 : CNF.NClause := [(99,true),(35,false),(39,false),(43,false),(47,true),(51,true),(60,false)]
theorem inputList2393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2393 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2393 (by decide) v hb
mask_input "2393|1152930884815421440|633825300114117093285653643264"
def inputClause2394 : CNF.NClause := [(99,true),(35,true),(39,false),(43,false),(47,true),(51,true),(60,false)]
theorem inputList2394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2394 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2394 (by decide) v hb
mask_input "2394|1152930850455683072|633825300114117093320013381632"
def inputClause2395 : CNF.NClause := [(99,true),(35,false),(39,true),(43,false),(47,true),(51,true),(60,false)]
theorem inputList2395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2395 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2395 (by decide) v hb
mask_input "2395|1152930335059607552|633825300114117093835409457152"
def inputClause2396 : CNF.NClause := [(99,true),(35,true),(39,true),(43,false),(47,true),(51,true),(60,false)]
theorem inputList2396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2396 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2396 (by decide) v hb
mask_input "2396|1152930300699869184|633825300114117093869769195520"
def inputClause2397 : CNF.NClause := [(99,true),(35,false),(39,false),(43,true),(47,true),(51,true),(60,false)]
theorem inputList2397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2397 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2397 (by decide) v hb
mask_input "2397|1152922088722399232|633825300114117102081746665472"
def inputClause2398 : CNF.NClause := [(99,true),(35,true),(39,false),(43,true),(47,true),(51,true),(60,false)]
theorem inputList2398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2398 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2398 (by decide) v hb
mask_input "2398|1152922054362660864|633825300114117102116106403840"
def inputClause2399 : CNF.NClause := [(99,true),(35,false),(39,true),(43,true),(47,true),(51,true),(60,false)]
theorem inputList2399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2399 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2399 (by decide) v hb
mask_input "2399|1152921538966585344|633825300114117102631502479360"
def inputClause2400 : CNF.NClause := [(99,false),(35,true),(39,true),(43,true),(47,true),(51,true),(60,false)]
theorem inputList2400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2400 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2400 (by decide) v hb
mask_input "2400|633825300115267622252958449664|2401917510615040"
def inputClause2401 : CNF.NClause := [(99,true),(35,false),(39,false),(43,false),(47,false),(51,false),(60,true)]
theorem inputList2401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2401 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2401 (by decide) v hb
mask_input "2401|2401917510615040|633825300115267622252958449664"
def inputClause2402 : CNF.NClause := [(99,true),(35,true),(39,false),(43,false),(47,false),(51,false),(60,true)]
theorem inputList2402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2402 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2402 (by decide) v hb
mask_input "2402|2401883150876672|633825300115267622287318188032"
def inputClause2403 : CNF.NClause := [(99,true),(35,false),(39,true),(43,false),(47,false),(51,false),(60,true)]
theorem inputList2403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2403 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2403 (by decide) v hb
mask_input "2403|2401367754801152|633825300115267622802714263552"
def inputClause2404 : CNF.NClause := [(99,true),(35,true),(39,true),(43,false),(47,false),(51,false),(60,true)]
theorem inputList2404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2404 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2404 (by decide) v hb
mask_input "2404|2401333395062784|633825300115267622837074001920"
def inputClause2405 : CNF.NClause := [(99,true),(35,false),(39,false),(43,true),(47,false),(51,false),(60,true)]
theorem inputList2405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2405 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2405 (by decide) v hb
mask_input "2405|2393121417592832|633825300115267631049051471872"
def inputClause2406 : CNF.NClause := [(99,true),(35,true),(39,false),(43,true),(47,false),(51,false),(60,true)]
theorem inputList2406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2406 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2406 (by decide) v hb
mask_input "2406|2393087057854464|633825300115267631083411210240"
def inputClause2407 : CNF.NClause := [(99,true),(35,false),(39,true),(43,true),(47,false),(51,false),(60,true)]
theorem inputList2407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2407 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2407 (by decide) v hb
mask_input "2407|2392571661778944|633825300115267631598807285760"
def inputClause2408 : CNF.NClause := [(99,true),(35,true),(39,true),(43,true),(47,false),(51,false),(60,true)]
theorem inputList2408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2408 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2408 (by decide) v hb
mask_input "2408|2392537302040576|633825300115267631633167024128"
def inputClause2409 : CNF.NClause := [(99,true),(35,false),(39,false),(43,false),(47,true),(51,false),(60,true)]
theorem inputList2409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2409 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2409 (by decide) v hb
mask_input "2409|2261180022259712|633825300115267762990446804992"
def inputClause2410 : CNF.NClause := [(99,true),(35,true),(39,false),(43,false),(47,true),(51,false),(60,true)]
theorem inputList2410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2410 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2410 (by decide) v hb
mask_input "2410|2261145662521344|633825300115267763024806543360"
def inputClause2411 : CNF.NClause := [(99,true),(35,false),(39,true),(43,false),(47,true),(51,false),(60,true)]
theorem inputList2411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2411 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2411 (by decide) v hb
mask_input "2411|2260630266445824|633825300115267763540202618880"
def inputClause2412 : CNF.NClause := [(99,true),(35,true),(39,true),(43,false),(47,true),(51,false),(60,true)]
theorem inputList2412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2412 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2412 (by decide) v hb
mask_input "2412|2260595906707456|633825300115267763574562357248"
def inputClause2413 : CNF.NClause := [(99,true),(35,false),(39,false),(43,true),(47,true),(51,false),(60,true)]
theorem inputList2413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2413 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2413 (by decide) v hb
mask_input "2413|2252383929237504|633825300115267771786539827200"
def inputClause2414 : CNF.NClause := [(99,true),(35,true),(39,false),(43,true),(47,true),(51,false),(60,true)]
theorem inputList2414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2414 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2414 (by decide) v hb
mask_input "2414|2252349569499136|633825300115267771820899565568"
def inputClause2415 : CNF.NClause := [(99,true),(35,false),(39,true),(43,true),(47,true),(51,false),(60,true)]
theorem inputList2415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2415 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2415 (by decide) v hb
mask_input "2415|2251834173423616|633825300115267772336295641088"
def inputClause2417 : CNF.NClause := [(99,true),(35,false),(39,false),(43,false),(47,false),(51,true),(60,true)]
theorem inputList2417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2417 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2417 (by decide) v hb
mask_input "2417|150117696929792|633825300115269874052772134912"
end Percolation.MaskChain
