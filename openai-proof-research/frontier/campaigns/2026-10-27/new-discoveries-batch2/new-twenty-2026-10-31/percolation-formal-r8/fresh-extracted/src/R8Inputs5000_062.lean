import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause7387 : CNF.NClause := [(57,false),(26,false),(62,true),(71,false),(75,true),(79,true),(83,false),(91,true)]
theorem inputList7387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7387 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7387 (by decide) v hb
mask_input "7387|9673767884273656363220992|2476522325024116839974699008"
def inputClause7389 : CNF.NClause := [(57,false),(26,false),(62,false),(71,true),(75,true),(79,true),(83,false),(91,true)]
theorem inputList7389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7389 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7389 (by decide) v hb
mask_input "7389|9671411312718239968002048|2476524681595672256369917952"
def inputClause7390 : CNF.NClause := [(57,false),(26,true),(62,false),(71,true),(75,true),(79,true),(83,false),(91,true)]
theorem inputList7390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7390 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7390 (by decide) v hb
mask_input "7390|9671411312718239900893184|2476524681595672256437026816"
def inputClause7392 : CNF.NClause := [(57,false),(26,true),(62,true),(71,true),(75,true),(79,true),(83,false),(91,true)]
theorem inputList7392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7392 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7392 (by decide) v hb
mask_input "7392|9671406701032221473505280|2476524686207358274864414720"
def inputClause7393 : CNF.NClause := [(57,false),(26,false),(62,false),(71,false),(75,false),(79,false),(83,true),(91,true)]
theorem inputList7393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7393 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7393 (by decide) v hb
mask_input "7393|644607780712913142022144|2485551485127677583195897856"
def inputClause7394 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,false),(79,false),(83,true),(91,true)]
theorem inputList7394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7394 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7394 (by decide) v hb
mask_input "7394|644607780712913074913280|2485551485127677583263006720"
def inputClause7395 : CNF.NClause := [(57,false),(26,false),(62,true),(71,false),(75,false),(79,false),(83,true),(91,true)]
theorem inputList7395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7395 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7395 (by decide) v hb
mask_input "7395|644603169026894714634240|2485551489739363601623285760"
def inputClause7397 : CNF.NClause := [(57,false),(26,false),(62,false),(71,true),(75,false),(79,false),(83,true),(91,true)]
theorem inputList7397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7397 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7397 (by decide) v hb
mask_input "7397|642246597471478319415296|2485553846310919018018504704"
def inputClause7398 : CNF.NClause := [(57,false),(26,true),(62,false),(71,true),(75,false),(79,false),(83,true),(91,true)]
theorem inputList7398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7398 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7398 (by decide) v hb
mask_input "7398|642246597471478252306432|2485553846310919018085613568"
def inputClause7399 : CNF.NClause := [(57,false),(26,false),(62,true),(71,true),(75,false),(79,false),(83,true),(91,true)]
theorem inputList7399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7399 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7399 (by decide) v hb
mask_input "7399|642241985785459892027392|2485553850922605036445892608"
def inputClause7400 : CNF.NClause := [(57,false),(26,true),(62,true),(71,true),(75,false),(79,false),(83,true),(91,true)]
theorem inputList7400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7400 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7400 (by decide) v hb
mask_input "7400|642241985785459824918528|2485553850922605036513001472"
def inputClause7402 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,true),(79,false),(83,true),(91,true)]
theorem inputList7402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7402 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7402 (by decide) v hb
mask_input "7402|606828848849955913203712|2485589264059540540424716288"
def inputClause7403 : CNF.NClause := [(57,false),(26,false),(62,true),(71,false),(75,true),(79,false),(83,true),(91,true)]
theorem inputList7403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7403 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7403 (by decide) v hb
mask_input "7403|606824237163937552924672|2485589268671226558784995328"
def inputClause7406 : CNF.NClause := [(57,false),(26,true),(62,false),(71,true),(75,true),(79,false),(83,true),(91,true)]
theorem inputList7406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7406 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7406 (by decide) v hb
mask_input "7406|604467665608521090596864|2485591625242781975247323136"
def inputClause7408 : CNF.NClause := [(57,false),(26,true),(62,true),(71,true),(75,true),(79,false),(83,true),(91,true)]
theorem inputList7408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7408 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7408 (by decide) v hb
mask_input "7408|604463053922502663208960|2485591629854467993674711040"
def inputClause7409 : CNF.NClause := [(57,false),(26,false),(62,false),(71,false),(75,false),(79,true),(83,true),(91,true)]
theorem inputList7409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7409 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7409 (by decide) v hb
mask_input "7409|40144870905598554669056|2486155948037484897783250944"
def inputClause7410 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,false),(79,true),(83,true),(91,true)]
theorem inputList7410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7410 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7410 (by decide) v hb
mask_input "7410|40144870905598487560192|2486155948037484897850359808"
def inputClause7411 : CNF.NClause := [(57,false),(26,false),(62,true),(71,false),(75,false),(79,true),(83,true),(91,true)]
theorem inputList7411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7411 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7411 (by decide) v hb
mask_input "7411|40140259219580127281152|2486155952649170916210638848"
def inputClause7413 : CNF.NClause := [(57,false),(26,false),(62,false),(71,true),(75,false),(79,true),(83,true),(91,true)]
theorem inputList7413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7413 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7413 (by decide) v hb
mask_input "7413|37783687664163732062208|2486158309220726332605857792"
def inputClause7414 : CNF.NClause := [(57,false),(26,true),(62,false),(71,true),(75,false),(79,true),(83,true),(91,true)]
theorem inputList7414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7414 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7414 (by decide) v hb
mask_input "7414|37783687664163664953344|2486158309220726332672966656"
def inputClause7417 : CNF.NClause := [(57,false),(26,false),(62,false),(71,false),(75,true),(79,true),(83,true),(91,true)]
theorem inputList7417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7417 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7417 (by decide) v hb
mask_input "7417|2365939042641392959488|2486193726969347854944960512"
def inputClause7418 : CNF.NClause := [(57,false),(26,true),(62,false),(71,false),(75,true),(79,true),(83,true),(91,true)]
theorem inputList7418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7418 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7418 (by decide) v hb
mask_input "7418|2365939042641325850624|2486193726969347855012069376"
def inputClause7419 : CNF.NClause := [(57,false),(26,false),(62,true),(71,false),(75,true),(79,true),(83,true),(91,true)]
theorem inputList7419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7419 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7419 (by decide) v hb
mask_input "7419|2361327356622965571584|2486193731581033873372348416"
def inputClause7422 : CNF.NClause := [(57,false),(26,true),(62,false),(71,true),(75,true),(79,true),(83,true),(91,true)]
theorem inputList7422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7422 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7422 (by decide) v hb
mask_input "7422|4755801206503243776|2486196088152589289834676224"
def inputClause7424 : CNF.NClause := [(57,false),(26,true),(62,true),(71,true),(75,true),(79,true),(83,true),(91,true)]
theorem inputList7424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7424 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 26) (spread_mem 26) inputClause7424 (by decide) v hb
mask_input "7424|144115188075855872|2486196092764275308262064128"
def inputClause7425 : CNF.NClause := [(58,true),(27,false),(62,false),(69,false),(76,false),(78,false),(85,false),(89,false)]
theorem inputList7425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7425 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7425 (by decide) v hb
mask_input "7425|658034030096484219924512768|288230376151711744"
def inputClause7553 : CNF.NClause := [(59,true),(28,false),(62,false),(70,false),(73,false),(81,false),(84,false),(90,false)]
theorem inputList7553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7553 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7553 (by decide) v hb
mask_input "7553|1259711333974716075441389568|576460752303423488"
def inputClause7554 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,false),(81,false),(84,false),(90,false)]
theorem inputList7554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7554 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7554 (by decide) v hb
mask_input "7554|1259711334551176827476377600|268435456"
def inputClause7555 : CNF.NClause := [(59,false),(28,false),(62,true),(70,false),(73,false),(81,false),(84,false),(90,false)]
theorem inputList7555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7555 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7555 (by decide) v hb
mask_input "7555|1259711329939490809317425152|4611686018427387904"
def inputClause7557 : CNF.NClause := [(59,false),(28,false),(62,false),(70,true),(73,false),(81,false),(84,false),(90,false)]
theorem inputList7557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7557 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7557 (by decide) v hb
mask_input "7557|1259710153959556110333509632|1180591620717411303424"
def inputClause7558 : CNF.NClause := [(59,false),(28,true),(62,false),(70,true),(73,false),(81,false),(84,false),(90,false)]
theorem inputList7558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7558 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7558 (by decide) v hb
mask_input "7558|1259710153959556110065074176|1180591620717679738880"
def inputClause7559 : CNF.NClause := [(59,false),(28,false),(62,true),(70,true),(73,false),(81,false),(84,false),(90,false)]
theorem inputList7559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7559 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7559 (by decide) v hb
mask_input "7559|1259710149347870091906121728|1185203306735838691328"
def inputClause7560 : CNF.NClause := [(59,false),(28,true),(62,true),(70,true),(73,false),(81,false),(84,false),(90,false)]
theorem inputList7560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7560 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7560 (by decide) v hb
mask_input "7560|1259710149347870091637686272|1185203306736107126784"
def inputClause7561 : CNF.NClause := [(59,false),(28,false),(62,false),(70,false),(73,true),(81,false),(84,false),(90,false)]
theorem inputList7561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7561 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7561 (by decide) v hb
mask_input "7561|1259701889818211088454385664|9444732965739290427392"
def inputClause7562 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,true),(81,false),(84,false),(90,false)]
theorem inputList7562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7562 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7562 (by decide) v hb
mask_input "7562|1259701889818211088185950208|9444732965739558862848"
def inputClause7563 : CNF.NClause := [(59,false),(28,false),(62,true),(70,false),(73,true),(81,false),(84,false),(90,false)]
theorem inputList7563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7563 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7563 (by decide) v hb
mask_input "7563|1259701885206525070026997760|9449344651757717815296"
def inputClause7564 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,true),(81,false),(84,false),(90,false)]
theorem inputList7564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7564 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7564 (by decide) v hb
mask_input "7564|1259701885206525069758562304|9449344651757986250752"
def inputClause7565 : CNF.NClause := [(59,false),(28,false),(62,false),(70,true),(73,true),(81,false),(84,false),(90,false)]
theorem inputList7565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7565 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7565 (by decide) v hb
mask_input "7565|1259700709226590371043082240|10625324586456701730816"
def inputClause7566 : CNF.NClause := [(59,false),(28,true),(62,false),(70,true),(73,true),(81,false),(84,false),(90,false)]
theorem inputList7566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7566 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7566 (by decide) v hb
mask_input "7566|1259700709226590370774646784|10625324586456970166272"
def inputClause7567 : CNF.NClause := [(59,false),(28,false),(62,true),(70,true),(73,true),(81,false),(84,false),(90,false)]
theorem inputList7567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7567 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7567 (by decide) v hb
mask_input "7567|1259700704614904352615694336|10629936272475129118720"
end Percolation.MaskChain
