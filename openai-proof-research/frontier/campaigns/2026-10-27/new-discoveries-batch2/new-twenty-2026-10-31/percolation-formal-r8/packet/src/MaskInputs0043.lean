import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause2418 : CNF.NClause := [(99,true),(35,true),(39,false),(43,false),(47,false),(51,true),(60,true)]
theorem inputList2418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2418 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2418 (by decide) v hb
mask_input "2418|150083337191424|633825300115269874087131873280"
def inputClause2419 : CNF.NClause := [(99,true),(35,false),(39,true),(43,false),(47,false),(51,true),(60,true)]
theorem inputList2419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2419 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2419 (by decide) v hb
mask_input "2419|149567941115904|633825300115269874602527948800"
def inputClause2420 : CNF.NClause := [(99,true),(35,true),(39,true),(43,false),(47,false),(51,true),(60,true)]
theorem inputList2420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2420 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2420 (by decide) v hb
mask_input "2420|149533581377536|633825300115269874636887687168"
def inputClause2421 : CNF.NClause := [(99,true),(35,false),(39,false),(43,true),(47,false),(51,true),(60,true)]
theorem inputList2421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2421 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2421 (by decide) v hb
mask_input "2421|141321603907584|633825300115269882848865157120"
def inputClause2422 : CNF.NClause := [(99,true),(35,true),(39,false),(43,true),(47,false),(51,true),(60,true)]
theorem inputList2422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2422 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2422 (by decide) v hb
mask_input "2422|141287244169216|633825300115269882883224895488"
def inputClause2423 : CNF.NClause := [(99,true),(35,false),(39,true),(43,true),(47,false),(51,true),(60,true)]
theorem inputList2423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2423 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2423 (by decide) v hb
mask_input "2423|140771848093696|633825300115269883398620971008"
def inputClause2425 : CNF.NClause := [(99,true),(35,false),(39,false),(43,false),(47,true),(51,true),(60,true)]
theorem inputList2425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2425 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2425 (by decide) v hb
mask_input "2425|9380208574464|633825300115270014790260490240"
def inputClause2426 : CNF.NClause := [(99,true),(35,true),(39,false),(43,false),(47,true),(51,true),(60,true)]
theorem inputList2426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2426 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2426 (by decide) v hb
mask_input "2426|9345848836096|633825300115270014824620228608"
def inputClause2427 : CNF.NClause := [(99,true),(35,false),(39,true),(43,false),(47,true),(51,true),(60,true)]
theorem inputList2427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2427 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2427 (by decide) v hb
mask_input "2427|8830452760576|633825300115270015340016304128"
def inputClause2429 : CNF.NClause := [(99,true),(35,false),(39,false),(43,true),(47,true),(51,true),(60,true)]
theorem inputList2429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2429 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2429 (by decide) v hb
mask_input "2429|584115552256|633825300115270023586353512448"
def inputClause2432 : CNF.NClause := [(99,false),(35,true),(39,true),(43,true),(47,true),(51,true),(60,true)]
theorem inputList2432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2432 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2432 (by decide) v hb
mask_input "2432|633825300114114700748351602688|1155323422117462016"
def inputClause2433 : CNF.NClause := [(100,true),(33,false),(40,false),(42,false),(49,false),(51,false),(58,false)]
theorem inputList2433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2433 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2433 (by decide) v hb
mask_input "2433|291050632066891776|1267650600228229401496703205376"
def inputClause2434 : CNF.NClause := [(100,true),(33,true),(40,false),(42,false),(49,false),(51,false),(58,false)]
theorem inputList2434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2434 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2434 (by decide) v hb
mask_input "2434|291050623476957184|1267650600228229401505293139968"
def inputClause2435 : CNF.NClause := [(100,true),(33,false),(40,true),(42,false),(49,false),(51,false),(58,false)]
theorem inputList2435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2435 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2435 (by decide) v hb
mask_input "2435|291049532555264000|1267650600228229402596214833152"
def inputClause2436 : CNF.NClause := [(100,true),(33,true),(40,true),(42,false),(49,false),(51,false),(58,false)]
theorem inputList2436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2436 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2436 (by decide) v hb
mask_input "2436|291049523965329408|1267650600228229402604804767744"
def inputClause2437 : CNF.NClause := [(100,true),(33,false),(40,false),(42,true),(49,false),(51,false),(58,false)]
theorem inputList2437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2437 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2437 (by decide) v hb
mask_input "2437|291046234020380672|1267650600228229405894749716480"
def inputClause2438 : CNF.NClause := [(100,true),(33,true),(40,false),(42,true),(49,false),(51,false),(58,false)]
theorem inputList2438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2438 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2438 (by decide) v hb
mask_input "2438|291046225430446080|1267650600228229405903339651072"
def inputClause2439 : CNF.NClause := [(100,true),(33,false),(40,true),(42,true),(49,false),(51,false),(58,false)]
theorem inputList2439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2439 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2439 (by decide) v hb
mask_input "2439|291045134508752896|1267650600228229406994261344256"
def inputClause2440 : CNF.NClause := [(100,true),(33,true),(40,true),(42,true),(49,false),(51,false),(58,false)]
theorem inputList2440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2440 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2440 (by decide) v hb
mask_input "2440|291045125918818304|1267650600228229407002851278848"
def inputClause2441 : CNF.NClause := [(100,true),(33,false),(40,false),(42,false),(49,true),(51,false),(58,false)]
theorem inputList2441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2441 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2441 (by decide) v hb
mask_input "2441|290487682113470464|1267650600228229964446656626688"
def inputClause2442 : CNF.NClause := [(100,true),(33,true),(40,false),(42,false),(49,true),(51,false),(58,false)]
theorem inputList2442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2442 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2442 (by decide) v hb
mask_input "2442|290487673523535872|1267650600228229964455246561280"
def inputClause2443 : CNF.NClause := [(100,true),(33,false),(40,true),(42,false),(49,true),(51,false),(58,false)]
theorem inputList2443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2443 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2443 (by decide) v hb
mask_input "2443|290486582601842688|1267650600228229965546168254464"
def inputClause2444 : CNF.NClause := [(100,true),(33,true),(40,true),(42,false),(49,true),(51,false),(58,false)]
theorem inputList2444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2444 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2444 (by decide) v hb
mask_input "2444|290486574011908096|1267650600228229965554758189056"
def inputClause2445 : CNF.NClause := [(100,true),(33,false),(40,false),(42,true),(49,true),(51,false),(58,false)]
theorem inputList2445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2445 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2445 (by decide) v hb
mask_input "2445|290483284066959360|1267650600228229968844703137792"
def inputClause2446 : CNF.NClause := [(100,true),(33,true),(40,false),(42,true),(49,true),(51,false),(58,false)]
theorem inputList2446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2446 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2446 (by decide) v hb
mask_input "2446|290483275477024768|1267650600228229968853293072384"
def inputClause2447 : CNF.NClause := [(100,true),(33,false),(40,true),(42,true),(49,true),(51,false),(58,false)]
theorem inputList2447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2447 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2447 (by decide) v hb
mask_input "2447|290482184555331584|1267650600228229969944214765568"
def inputClause2448 : CNF.NClause := [(100,true),(33,true),(40,true),(42,true),(49,true),(51,false),(58,false)]
theorem inputList2448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2448 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2448 (by decide) v hb
mask_input "2448|290482175965396992|1267650600228229969952804700160"
def inputClause2449 : CNF.NClause := [(100,true),(33,false),(40,false),(42,false),(49,false),(51,true),(58,false)]
theorem inputList2449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2449 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2449 (by decide) v hb
mask_input "2449|288798832253206528|1267650600228231653296516890624"
def inputClause2450 : CNF.NClause := [(100,true),(33,true),(40,false),(42,false),(49,false),(51,true),(58,false)]
theorem inputList2450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2450 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2450 (by decide) v hb
mask_input "2450|288798823663271936|1267650600228231653305106825216"
def inputClause2451 : CNF.NClause := [(100,true),(33,false),(40,true),(42,false),(49,false),(51,true),(58,false)]
theorem inputList2451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2451 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2451 (by decide) v hb
mask_input "2451|288797732741578752|1267650600228231654396028518400"
def inputClause2452 : CNF.NClause := [(100,true),(33,true),(40,true),(42,false),(49,false),(51,true),(58,false)]
theorem inputList2452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2452 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2452 (by decide) v hb
mask_input "2452|288797724151644160|1267650600228231654404618452992"
def inputClause2453 : CNF.NClause := [(100,true),(33,false),(40,false),(42,true),(49,false),(51,true),(58,false)]
theorem inputList2453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2453 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2453 (by decide) v hb
mask_input "2453|288794434206695424|1267650600228231657694563401728"
def inputClause2454 : CNF.NClause := [(100,true),(33,true),(40,false),(42,true),(49,false),(51,true),(58,false)]
theorem inputList2454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2454 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2454 (by decide) v hb
mask_input "2454|288794425616760832|1267650600228231657703153336320"
def inputClause2455 : CNF.NClause := [(100,true),(33,false),(40,true),(42,true),(49,false),(51,true),(58,false)]
theorem inputList2455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2455 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2455 (by decide) v hb
mask_input "2455|288793334695067648|1267650600228231658794075029504"
def inputClause2456 : CNF.NClause := [(100,true),(33,true),(40,true),(42,true),(49,false),(51,true),(58,false)]
theorem inputList2456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2456 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2456 (by decide) v hb
mask_input "2456|288793326105133056|1267650600228231658802664964096"
def inputClause2457 : CNF.NClause := [(100,true),(33,false),(40,false),(42,false),(49,true),(51,true),(58,false)]
theorem inputList2457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2457 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2457 (by decide) v hb
mask_input "2457|288235882299785216|1267650600228232216246470311936"
def inputClause2458 : CNF.NClause := [(100,true),(33,true),(40,false),(42,false),(49,true),(51,true),(58,false)]
theorem inputList2458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2458 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2458 (by decide) v hb
mask_input "2458|288235873709850624|1267650600228232216255060246528"
def inputClause2459 : CNF.NClause := [(100,true),(33,false),(40,true),(42,false),(49,true),(51,true),(58,false)]
theorem inputList2459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2459 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2459 (by decide) v hb
mask_input "2459|288234782788157440|1267650600228232217345981939712"
def inputClause2460 : CNF.NClause := [(100,true),(33,true),(40,true),(42,false),(49,true),(51,true),(58,false)]
theorem inputList2460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2460 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2460 (by decide) v hb
mask_input "2460|288234774198222848|1267650600228232217354571874304"
def inputClause2461 : CNF.NClause := [(100,true),(33,false),(40,false),(42,true),(49,true),(51,true),(58,false)]
theorem inputList2461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2461 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2461 (by decide) v hb
mask_input "2461|288231484253274112|1267650600228232220644516823040"
end Percolation.MaskChain
