import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause2236 : CNF.NClause := [(96,false),(34,true),(39,true),(44,false),(49,true),(54,true),(56,true)]
theorem inputList2236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2236 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2236 (by decide) v hb
mask_input "2236|79228162514264355185729994752|90635509436514304"
def inputClause2238 : CNF.NClause := [(96,false),(34,true),(39,false),(44,true),(49,true),(54,true),(56,true)]
theorem inputList2238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2238 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 3) 3) (activationX_mem 3) inputClause2238 (by decide) v hb
mask_input "2238|79228162514264338143299764224|90652551866744832"
def inputClause2288 : CNF.NClause := [(97,false),(32,true),(37,true),(42,true),(47,true),(52,false),(56,true)]
theorem inputList2288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2288 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2288 (by decide) v hb
mask_input "2288|158456325028533178786715271168|72202871306715136"
def inputClause2296 : CNF.NClause := [(97,false),(32,true),(37,true),(42,true),(47,false),(52,true),(56,true)]
theorem inputList2296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2296 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2296 (by decide) v hb
mask_input "2296|158456325028528815924576256000|76565733445730304"
def inputClause2300 : CNF.NClause := [(97,false),(32,true),(37,true),(42,false),(47,true),(52,true),(56,true)]
theorem inputList2300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2300 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2300 (by decide) v hb
mask_input "2300|158456325028528679585134411776|76702072887574528"
def inputClause2302 : CNF.NClause := [(97,false),(32,true),(37,false),(42,true),(47,true),(52,true),(56,true)]
theorem inputList2302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2302 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2302 (by decide) v hb
mask_input "2302|158456325028528675324526854144|76706333495132160"
def inputClause2303 : CNF.NClause := [(97,false),(32,false),(37,true),(42,true),(47,true),(52,true),(56,true)]
theorem inputList2303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2303 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 4) 4) (activationX_mem 4) inputClause2303 (by decide) v hb
mask_input "2303|158456325028528675191382867968|76706466639118336"
def inputClause2352 : CNF.NClause := [(98,false),(51,true),(52,true),(53,true),(54,true),(55,false),(61,true)]
theorem inputList2352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2352 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2352 (by decide) v hb
mask_input "2352|316912650057093379171194765312|2339620006418972672"
def inputClause2360 : CNF.NClause := [(98,false),(51,true),(52,true),(53,true),(54,false),(55,true),(61,true)]
theorem inputList2360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2360 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2360 (by decide) v hb
mask_input "2360|316912650057075364772685283328|2357634404928454656"
def inputClause2364 : CNF.NClause := [(98,false),(51,true),(52,true),(53,false),(54,true),(55,true),(61,true)]
theorem inputList2364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2364 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2364 (by decide) v hb
mask_input "2364|316912650057066357573430542336|2366641604183195648"
def inputClause2366 : CNF.NClause := [(98,false),(51,true),(52,false),(53,true),(54,true),(55,true),(61,true)]
theorem inputList2366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2366 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 5) 5) (activationX_mem 5) inputClause2366 (by decide) v hb
mask_input "2366|316912650057061853973803171840|2371145203810566144"
def inputClause2416 : CNF.NClause := [(99,false),(35,true),(39,true),(43,true),(47,true),(51,false),(60,true)]
theorem inputList2416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2416 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2416 (by decide) v hb
mask_input "2416|633825300114116952548165287936|1153071622303776768"
def inputClause2424 : CNF.NClause := [(99,false),(35,true),(39,true),(43,true),(47,false),(51,true),(60,true)]
theorem inputList2424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2424 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2424 (by decide) v hb
mask_input "2424|633825300114114841485839958016|1155182684629106688"
def inputClause2428 : CNF.NClause := [(99,false),(35,true),(39,true),(43,false),(47,true),(51,true),(60,true)]
theorem inputList2428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2428 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2428 (by decide) v hb
mask_input "2428|633825300114114709544444624896|1155314626024439808"
def inputClause2430 : CNF.NClause := [(99,false),(35,true),(39,false),(43,true),(47,true),(51,true),(60,true)]
theorem inputList2430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2430 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2430 (by decide) v hb
mask_input "2430|633825300114114701298107416576|1155322872361648128"
def inputClause2431 : CNF.NClause := [(99,false),(35,false),(39,true),(43,true),(47,true),(51,true),(60,true)]
theorem inputList2431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2431 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 6) 6) (activationX_mem 6) inputClause2431 (by decide) v hb
mask_input "2431|633825300114114700782711341056|1155323387757723648"
def inputClause2480 : CNF.NClause := [(100,false),(33,true),(40,true),(42,true),(49,true),(51,false),(58,true)]
theorem inputList2480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2480 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2480 (by decide) v hb
mask_input "2480|1267650600228231653296516890624|288798832253206528"
def inputClause2488 : CNF.NClause := [(100,false),(33,true),(40,true),(42,true),(49,false),(51,true),(58,true)]
theorem inputList2488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2488 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2488 (by decide) v hb
mask_input "2488|1267650600228229964446656626688|290487682113470464"
def inputClause2492 : CNF.NClause := [(100,false),(33,true),(40,true),(42,false),(49,true),(51,true),(58,true)]
theorem inputList2492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2492 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2492 (by decide) v hb
mask_input "2492|1267650600228229405894749716480|291046234020380672"
def inputClause2494 : CNF.NClause := [(100,false),(33,true),(40,false),(42,true),(49,true),(51,true),(58,true)]
theorem inputList2494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2494 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2494 (by decide) v hb
mask_input "2494|1267650600228229402596214833152|291049532555264000"
def inputClause2495 : CNF.NClause := [(100,false),(33,false),(40,true),(42,true),(49,true),(51,true),(58,true)]
theorem inputList2495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2495 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 7) 7) (activationX_mem 7) inputClause2495 (by decide) v hb
mask_input "2495|1267650600228229401505293139968|291050623476957184"
def inputClause2544 : CNF.NClause := [(101,false),(34,true),(37,true),(45,true),(48,true),(51,false),(59,true)]
theorem inputList2544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2544 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2544 (by decide) v hb
mask_input "2544|2535301200456461054793220096000|576777566271045632"
def inputClause2552 : CNF.NClause := [(101,false),(34,true),(37,true),(45,true),(48,false),(51,true),(59,true)]
theorem inputList2552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2552 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2552 (by decide) v hb
mask_input "2552|2535301200456459084468383121408|578747891108020224"
def inputClause2556 : CNF.NClause := [(101,false),(34,true),(37,true),(45,false),(48,true),(51,true),(59,true)]
theorem inputList2556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2556 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2556 (by decide) v hb
mask_input "2556|2535301200456458838177778499584|578994181712642048"
def inputClause2558 : CNF.NClause := [(101,false),(34,true),(37,false),(45,true),(48,true),(51,true),(59,true)]
theorem inputList2558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2558 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2558 (by decide) v hb
mask_input "2558|2535301200456458803130845364224|579029228645777408"
def inputClause2559 : CNF.NClause := [(101,false),(34,false),(37,true),(45,true),(48,true),(51,true),(59,true)]
theorem inputList2559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2559 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2559 (by decide) v hb
mask_input "2559|2535301200456458803010586279936|579029348904861696"
def inputClause2592 : CNF.NClause := [(102,false),(32,true),(38,true),(44,true),(50,true),(51,true),(57,false)]
theorem inputList2592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2592 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2592 (by decide) v hb
mask_input "2592|5070602400913061721174888677376|3395571079446528"
def inputClause2608 : CNF.NClause := [(102,false),(32,true),(38,true),(44,true),(50,true),(51,false),(57,true)]
theorem inputList2608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2608 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2608 (by decide) v hb
mask_input "2608|5070602400912919857786626506752|145258959341617152"
def inputClause2616 : CNF.NClause := [(102,false),(32,true),(38,true),(44,true),(50,false),(51,true),(57,true)]
theorem inputList2616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2616 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2616 (by decide) v hb
mask_input "2616|5070602400912918731886719664128|146384859248459776"
def inputClause2620 : CNF.NClause := [(102,false),(32,true),(38,true),(44,false),(50,true),(51,true),(57,true)]
theorem inputList2620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2620 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2620 (by decide) v hb
mask_input "2620|5070602400912917623578998865920|147493166969257984"
def inputClause2622 : CNF.NClause := [(102,false),(32,true),(38,false),(44,true),(50,true),(51,true),(57,true)]
theorem inputList2622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2622 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2622 (by decide) v hb
mask_input "2622|5070602400912917606261690728448|147510484277395456"
def inputClause2672 : CNF.NClause := [(103,false),(41,true),(42,true),(43,true),(44,true),(45,false),(61,true)]
theorem inputList2672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2672 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2672 (by decide) v hb
mask_input "2672|10141204801825835247157997731840|2305875994562527232"
def inputClause2680 : CNF.NClause := [(103,false),(41,true),(42,true),(43,true),(44,false),(45,true),(61,true)]
theorem inputList2680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2680 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2680 (by decide) v hb
mask_input "2680|10141204801825835229565811687424|2305893586748571648"
def inputClause2684 : CNF.NClause := [(103,false),(41,true),(42,true),(43,false),(44,true),(45,true),(61,true)]
theorem inputList2684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2684 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2684 (by decide) v hb
mask_input "2684|10141204801825835220769718665216|2305902382841593856"
def inputClause2686 : CNF.NClause := [(103,false),(41,true),(42,false),(43,true),(44,true),(45,true),(61,true)]
theorem inputList2686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2686 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2686 (by decide) v hb
mask_input "2686|10141204801825835216371672154112|2305906780888104960"
def inputClause2720 : CNF.NClause := [(104,false),(35,true),(38,true),(41,true),(49,true),(52,true),(59,false)]
theorem inputList2720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2720 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2720 (by decide) v hb
mask_input "2720|20282409603652246884699554709504|5069057841692672"
def inputClause2736 : CNF.NClause := [(104,false),(35,true),(38,true),(41,true),(49,true),(52,false),(59,true)]
theorem inputList2736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2736 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2736 (by decide) v hb
mask_input "2736|20282409603651674927546878656512|577026210517745664"
def inputClause2744 : CNF.NClause := [(104,false),(35,true),(38,true),(41,true),(49,false),(52,true),(59,true)]
theorem inputList2744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2744 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2744 (by decide) v hb
mask_input "2744|20282409603651670986897204707328|580966860191694848"
def inputClause2748 : CNF.NClause := [(104,false),(35,true),(38,true),(41,false),(49,true),(52,true),(59,true)]
theorem inputList2748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2748 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2748 (by decide) v hb
mask_input "2748|20282409603651670426146274541568|581527611121860608"
def inputClause2750 : CNF.NClause := [(104,false),(35,true),(38,false),(41,true),(49,true),(52,true),(59,true)]
theorem inputList2750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2750 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) inputClause2750 (by decide) v hb
mask_input "2750|20282409603651670424222129192960|581529535267209216"
end Percolation.MaskChain
