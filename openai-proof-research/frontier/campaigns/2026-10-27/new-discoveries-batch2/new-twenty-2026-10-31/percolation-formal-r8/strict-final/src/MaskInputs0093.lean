import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause6154 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,true),(77,false),(83,false),(88,false)]
theorem inputList6154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6154 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6154 (by decide) v hb
mask_input "6154|319308731144360196866834432|75557863725914323550208"
def inputClause6162 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,false),(77,true),(83,false),(88,false)]
theorem inputList6162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6162 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6162 (by decide) v hb
mask_input "6162|319233173280634282543415296|151115727451828646969344"
def inputClause6170 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,true),(77,true),(83,false),(88,false)]
theorem inputList6170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6170 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6170 (by decide) v hb
mask_input "6170|319157615416908368219996160|226673591177742970388480"
def inputClause6178 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,false),(77,false),(83,true),(88,false)]
theorem inputList6178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6178 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6178 (by decide) v hb
mask_input "6178|309712882451169077792604160|9671406556917033397780480"
def inputClause6186 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,true),(77,false),(83,true),(88,false)]
theorem inputList6186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6186 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6186 (by decide) v hb
mask_input "6186|309637324587443163469185024|9746964420642947721199616"
def inputClause6194 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,false),(77,true),(83,true),(88,false)]
theorem inputList6194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6194 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6194 (by decide) v hb
mask_input "6194|309561766723717249145765888|9822522284368862044618752"
def inputClause6202 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,true),(77,true),(83,true),(88,false)]
theorem inputList6202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6202 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6202 (by decide) v hb
mask_input "6202|309486208859991334822346752|9898080148094776368037888"
def inputClause6218 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,true),(77,false),(83,false),(88,true)]
theorem inputList6218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6218 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6218 (by decide) v hb
mask_input "6218|9823721323015128142053376|309560567685070983048331264"
def inputClause6234 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,true),(77,true),(83,false),(88,true)]
theorem inputList6234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6234 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6234 (by decide) v hb
mask_input "6234|9672605595563299495215104|309711683412522811695169536"
def inputClause6242 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,false),(77,false),(83,true),(88,true)]
theorem inputList6242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6242 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6242 (by decide) v hb
mask_input "6242|227872629824009067823104|319156416378262102122561536"
def inputClause6250 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,true),(77,false),(83,true),(88,true)]
theorem inputList6250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6250 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6250 (by decide) v hb
mask_input "6250|152314766098094744403968|319231974241988016445980672"
def inputClause6258 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,false),(77,true),(83,true),(88,true)]
theorem inputList6258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6258 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6258 (by decide) v hb
mask_input "6258|76756902372180420984832|319307532105713930769399808"
def inputClause6266 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,true),(77,true),(83,true),(88,true)]
theorem inputList6266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6266 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6266 (by decide) v hb
mask_input "6266|1199038646266097565696|319383089969439845092818944"
def inputClause6274 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,false),(77,false),(86,false),(91,false)]
theorem inputList6274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6274 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6274 (by decide) v hb
mask_input "6274|2553412518676375840994885632|262144"
def inputClause6289 : CNF.NClause := [(49,false),(18,false),(65,false),(69,false),(73,false),(77,true),(86,false),(91,false)]
theorem inputList6289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6289 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6289 (by decide) v hb
mask_input "6289|2553261402948924012348309504|151115727451828646838272"
def inputClause6290 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,false),(77,true),(86,false),(91,false)]
theorem inputList6290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6290 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6290 (by decide) v hb
mask_input "6290|2553261402948924012348047360|151115727451828647100416"
def inputClause6338 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,false),(77,false),(86,false),(91,true)]
theorem inputList6338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6338 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6338 (by decide) v hb
mask_input "6338|77532440105615291196637184|2475880078570760549798510592"
def inputClause6353 : CNF.NClause := [(49,false),(18,false),(65,false),(69,false),(73,false),(77,true),(86,false),(91,true)]
theorem inputList6353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6353 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6353 (by decide) v hb
mask_input "6353|77381324378163462550061056|2476031194298212378445086720"
def inputClause6354 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,false),(77,true),(86,false),(91,true)]
theorem inputList6354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6354 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6354 (by decide) v hb
mask_input "6354|77381324378163462549798912|2476031194298212378445348864"
def inputClause6402 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,false),(77,false),(85,false),(90,false)]
theorem inputList6402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6402 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6402 (by decide) v hb
mask_input "6402|1276798041114171087301640192|524288"
def inputClause6410 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,true),(77,false),(85,false),(90,false)]
theorem inputList6410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6410 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6410 (by decide) v hb
mask_input "6410|1276779151648239608720785408|18889465931478581379072"
def inputClause6417 : CNF.NClause := [(50,false),(19,false),(63,false),(71,false),(74,false),(77,true),(85,false),(90,false)]
theorem inputList6417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6417 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6417 (by decide) v hb
mask_input "6417|1276646925386719258655326208|151115727451828646838272"
def inputClause6418 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,false),(77,true),(85,false),(90,false)]
theorem inputList6418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6418 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6418 (by decide) v hb
mask_input "6418|1276646925386719258654801920|151115727451828647362560"
def inputClause6426 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,true),(77,true),(85,false),(90,false)]
theorem inputList6426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6426 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6426 (by decide) v hb
mask_input "6426|1276628035920787780073947136|170005193383307228217344"
def inputClause6442 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,true),(77,false),(85,true),(90,false)]
theorem inputList6442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6442 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6442 (by decide) v hb
mask_input "6442|1238093525420571475130187776|38704515693599612171976704"
def inputClause6458 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,true),(77,true),(85,true),(90,false)]
theorem inputList6458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6458 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6458 (by decide) v hb
mask_input "6458|1237942409693119646483349504|38855631421051440818814976"
def inputClause6466 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,false),(77,false),(85,false),(90,true)]
theorem inputList6466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6466 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6466 (by decide) v hb
mask_input "6466|38858001828790812402515968|1237940039285380274899648512"
def inputClause6474 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,true),(77,false),(85,false),(90,true)]
theorem inputList6474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6474 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6474 (by decide) v hb
mask_input "6474|38839112362859333821661184|1237958928751311753480503296"
def inputClause6481 : CNF.NClause := [(50,false),(19,false),(63,false),(71,false),(74,false),(77,true),(85,false),(90,true)]
theorem inputList6481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6481 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6481 (by decide) v hb
mask_input "6481|38706886101338983756201984|1238091155012832103545962496"
def inputClause6482 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,false),(77,true),(85,false),(90,true)]
theorem inputList6482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6482 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6482 (by decide) v hb
mask_input "6482|38706886101338983755677696|1238091155012832103546486784"
def inputClause6490 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,true),(77,true),(85,false),(90,true)]
theorem inputList6490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6490 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6490 (by decide) v hb
mask_input "6490|38687996635407505174822912|1238110044478763582127341568"
def inputClause6506 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,true),(77,false),(85,true),(90,true)]
theorem inputList6506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6506 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6506 (by decide) v hb
mask_input "6506|153486135191200231063552|1276644554978979887071100928"
def inputClause6522 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,true),(77,true),(85,true),(90,true)]
theorem inputList6522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6522 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6522 (by decide) v hb
mask_input "6522|2370407739371584225280|1276795670706431715717939200"
def inputClause6658 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,false),(79,false),(85,false),(88,false)]
theorem inputList6658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6658 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6658 (by decide) v hb
mask_input "6658|348784765057218740335149056|2097152"
def inputClause6662 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,false),(79,false),(85,false),(88,false)]
theorem inputList6662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6662 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6662 (by decide) v hb
mask_input "6662|348784617483266150658736128|147573952589678510080"
def inputClause6670 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,true),(79,false),(85,false),(88,false)]
theorem inputList6670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6670 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6670 (by decide) v hb
mask_input "6670|348775172750300411368308736|9592306918328968937472"
def inputClause6678 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,false),(79,true),(85,false),(88,false)]
theorem inputList6678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6678 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6678 (by decide) v hb
mask_input "6678|348180154573458836071383040|604610483759904265863168"
def inputClause6686 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,true),(79,true),(85,false),(88,false)]
theorem inputList6686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6686 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6686 (by decide) v hb
mask_input "6686|348170709840493096780955648|614055216725643556290560"
def inputClause6694 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,false),(79,false),(85,true),(88,false)]
theorem inputList6694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6694 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6694 (by decide) v hb
mask_input "6694|310098991255598017068138496|38685773801620723269107712"
def inputClause6702 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,true),(79,false),(85,true),(88,false)]
theorem inputList6702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6702 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6702 (by decide) v hb
mask_input "6702|310089546522632277777711104|38695218534586462559535104"
end Percolation.MaskChain
