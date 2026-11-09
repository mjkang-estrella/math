import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause2462 : CNF.NClause := [(100,true),(33,true),(40,false),(42,true),(49,true),(51,true),(58,false)]
theorem inputList2462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2462 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2462 (by decide) v hb
mask_input "2462|288231475663339520|1267650600228232220653106757632"
def inputClause2463 : CNF.NClause := [(100,true),(33,false),(40,true),(42,true),(49,true),(51,true),(58,false)]
theorem inputList2463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2463 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2463 (by decide) v hb
mask_input "2463|288230384741646336|1267650600228232221744028450816"
def inputClause2464 : CNF.NClause := [(100,false),(33,true),(40,true),(42,true),(49,true),(51,true),(58,false)]
theorem inputList2464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2464 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2464 (by decide) v hb
mask_input "2464|1267650600228517631872854917120|2820255915180032"
def inputClause2465 : CNF.NClause := [(100,true),(33,false),(40,false),(42,false),(49,false),(51,false),(58,true)]
theorem inputList2465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2465 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2465 (by decide) v hb
mask_input "2465|2820255915180032|1267650600228517631872854917120"
def inputClause2466 : CNF.NClause := [(100,true),(33,true),(40,false),(42,false),(49,false),(51,false),(58,true)]
theorem inputList2466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2466 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2466 (by decide) v hb
mask_input "2466|2820247325245440|1267650600228517631881444851712"
def inputClause2467 : CNF.NClause := [(100,true),(33,false),(40,true),(42,false),(49,false),(51,false),(58,true)]
theorem inputList2467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2467 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2467 (by decide) v hb
mask_input "2467|2819156403552256|1267650600228517632972366544896"
def inputClause2468 : CNF.NClause := [(100,true),(33,true),(40,true),(42,false),(49,false),(51,false),(58,true)]
theorem inputList2468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2468 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2468 (by decide) v hb
mask_input "2468|2819147813617664|1267650600228517632980956479488"
def inputClause2469 : CNF.NClause := [(100,true),(33,false),(40,false),(42,true),(49,false),(51,false),(58,true)]
theorem inputList2469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2469 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2469 (by decide) v hb
mask_input "2469|2815857868668928|1267650600228517636270901428224"
def inputClause2470 : CNF.NClause := [(100,true),(33,true),(40,false),(42,true),(49,false),(51,false),(58,true)]
theorem inputList2470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2470 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2470 (by decide) v hb
mask_input "2470|2815849278734336|1267650600228517636279491362816"
def inputClause2471 : CNF.NClause := [(100,true),(33,false),(40,true),(42,true),(49,false),(51,false),(58,true)]
theorem inputList2471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2471 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2471 (by decide) v hb
mask_input "2471|2814758357041152|1267650600228517637370413056000"
def inputClause2472 : CNF.NClause := [(100,true),(33,true),(40,true),(42,true),(49,false),(51,false),(58,true)]
theorem inputList2472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2472 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2472 (by decide) v hb
mask_input "2472|2814749767106560|1267650600228517637379002990592"
def inputClause2473 : CNF.NClause := [(100,true),(33,false),(40,false),(42,false),(49,true),(51,false),(58,true)]
theorem inputList2473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2473 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2473 (by decide) v hb
mask_input "2473|2257305961758720|1267650600228518194822808338432"
def inputClause2474 : CNF.NClause := [(100,true),(33,true),(40,false),(42,false),(49,true),(51,false),(58,true)]
theorem inputList2474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2474 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2474 (by decide) v hb
mask_input "2474|2257297371824128|1267650600228518194831398273024"
def inputClause2475 : CNF.NClause := [(100,true),(33,false),(40,true),(42,false),(49,true),(51,false),(58,true)]
theorem inputList2475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2475 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2475 (by decide) v hb
mask_input "2475|2256206450130944|1267650600228518195922319966208"
def inputClause2476 : CNF.NClause := [(100,true),(33,true),(40,true),(42,false),(49,true),(51,false),(58,true)]
theorem inputList2476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2476 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2476 (by decide) v hb
mask_input "2476|2256197860196352|1267650600228518195930909900800"
def inputClause2477 : CNF.NClause := [(100,true),(33,false),(40,false),(42,true),(49,true),(51,false),(58,true)]
theorem inputList2477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2477 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2477 (by decide) v hb
mask_input "2477|2252907915247616|1267650600228518199220854849536"
def inputClause2478 : CNF.NClause := [(100,true),(33,true),(40,false),(42,true),(49,true),(51,false),(58,true)]
theorem inputList2478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2478 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2478 (by decide) v hb
mask_input "2478|2252899325313024|1267650600228518199229444784128"
def inputClause2479 : CNF.NClause := [(100,true),(33,false),(40,true),(42,true),(49,true),(51,false),(58,true)]
theorem inputList2479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2479 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2479 (by decide) v hb
mask_input "2479|2251808403619840|1267650600228518200320366477312"
def inputClause2481 : CNF.NClause := [(100,true),(33,false),(40,false),(42,false),(49,false),(51,true),(58,true)]
theorem inputList2481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2481 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2481 (by decide) v hb
mask_input "2481|568456101494784|1267650600228519883672668602368"
def inputClause2482 : CNF.NClause := [(100,true),(33,true),(40,false),(42,false),(49,false),(51,true),(58,true)]
theorem inputList2482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2482 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2482 (by decide) v hb
mask_input "2482|568447511560192|1267650600228519883681258536960"
def inputClause2483 : CNF.NClause := [(100,true),(33,false),(40,true),(42,false),(49,false),(51,true),(58,true)]
theorem inputList2483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2483 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2483 (by decide) v hb
mask_input "2483|567356589867008|1267650600228519884772180230144"
def inputClause2484 : CNF.NClause := [(100,true),(33,true),(40,true),(42,false),(49,false),(51,true),(58,true)]
theorem inputList2484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2484 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2484 (by decide) v hb
mask_input "2484|567347999932416|1267650600228519884780770164736"
def inputClause2485 : CNF.NClause := [(100,true),(33,false),(40,false),(42,true),(49,false),(51,true),(58,true)]
theorem inputList2485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2485 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2485 (by decide) v hb
mask_input "2485|564058054983680|1267650600228519888070715113472"
def inputClause2486 : CNF.NClause := [(100,true),(33,true),(40,false),(42,true),(49,false),(51,true),(58,true)]
theorem inputList2486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2486 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2486 (by decide) v hb
mask_input "2486|564049465049088|1267650600228519888079305048064"
def inputClause2487 : CNF.NClause := [(100,true),(33,false),(40,true),(42,true),(49,false),(51,true),(58,true)]
theorem inputList2487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2487 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2487 (by decide) v hb
mask_input "2487|562958543355904|1267650600228519889170226741248"
def inputClause2489 : CNF.NClause := [(100,true),(33,false),(40,false),(42,false),(49,true),(51,true),(58,true)]
theorem inputList2489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2489 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2489 (by decide) v hb
mask_input "2489|5506148073472|1267650600228520446622622023680"
def inputClause2490 : CNF.NClause := [(100,true),(33,true),(40,false),(42,false),(49,true),(51,true),(58,true)]
theorem inputList2490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2490 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2490 (by decide) v hb
mask_input "2490|5497558138880|1267650600228520446631211958272"
def inputClause2491 : CNF.NClause := [(100,true),(33,false),(40,true),(42,false),(49,true),(51,true),(58,true)]
theorem inputList2491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2491 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2491 (by decide) v hb
mask_input "2491|4406636445696|1267650600228520447722133651456"
def inputClause2493 : CNF.NClause := [(100,true),(33,false),(40,false),(42,true),(49,true),(51,true),(58,true)]
theorem inputList2493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2493 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2493 (by decide) v hb
mask_input "2493|1108101562368|1267650600228520451020668534784"
def inputClause2496 : CNF.NClause := [(100,false),(33,true),(40,true),(42,true),(49,true),(51,true),(58,true)]
theorem inputList2496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2496 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2496 (by decide) v hb
mask_input "2496|1267650600228229401496703205376|291050632066891776"
def inputClause2497 : CNF.NClause := [(101,true),(34,false),(37,false),(45,false),(48,false),(51,false),(59,false)]
theorem inputList2497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2497 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2497 (by decide) v hb
mask_input "2497|579029366084730880|2535301200456458802993406410752"
def inputClause2498 : CNF.NClause := [(101,true),(34,true),(37,false),(45,false),(48,false),(51,false),(59,false)]
theorem inputList2498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2498 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2498 (by decide) v hb
mask_input "2498|579029348904861696|2535301200456458803010586279936"
def inputClause2499 : CNF.NClause := [(101,true),(34,false),(37,true),(45,false),(48,false),(51,false),(59,false)]
theorem inputList2499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2499 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2499 (by decide) v hb
mask_input "2499|579029228645777408|2535301200456458803130845364224"
def inputClause2500 : CNF.NClause := [(101,true),(34,true),(37,true),(45,false),(48,false),(51,false),(59,false)]
theorem inputList2500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2500 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2500 (by decide) v hb
mask_input "2500|579029211465908224|2535301200456458803148025233408"
def inputClause2501 : CNF.NClause := [(101,true),(34,false),(37,false),(45,true),(48,false),(51,false),(59,false)]
theorem inputList2501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2501 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2501 (by decide) v hb
mask_input "2501|578994181712642048|2535301200456458838177778499584"
def inputClause2502 : CNF.NClause := [(101,true),(34,true),(37,false),(45,true),(48,false),(51,false),(59,false)]
theorem inputList2502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2502 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2502 (by decide) v hb
mask_input "2502|578994164532772864|2535301200456458838194958368768"
def inputClause2503 : CNF.NClause := [(101,true),(34,false),(37,true),(45,true),(48,false),(51,false),(59,false)]
theorem inputList2503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2503 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2503 (by decide) v hb
mask_input "2503|578994044273688576|2535301200456458838315217453056"
def inputClause2504 : CNF.NClause := [(101,true),(34,true),(37,true),(45,true),(48,false),(51,false),(59,false)]
theorem inputList2504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2504 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2504 (by decide) v hb
mask_input "2504|578994027093819392|2535301200456458838332397322240"
def inputClause2505 : CNF.NClause := [(101,true),(34,false),(37,false),(45,false),(48,true),(51,false),(59,false)]
theorem inputList2505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2505 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2505 (by decide) v hb
mask_input "2505|578747891108020224|2535301200456459084468383121408"
def inputClause2506 : CNF.NClause := [(101,true),(34,true),(37,false),(45,false),(48,true),(51,false),(59,false)]
theorem inputList2506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2506 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2506 (by decide) v hb
mask_input "2506|578747873928151040|2535301200456459084485562990592"
end Percolation.MaskChain
