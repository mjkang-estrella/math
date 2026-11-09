import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause5397 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(72,false),(80,true),(83,false),(90,false)]
theorem inputList5397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5397 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5397 (by decide) v hb
mask_input "5397|1247616241995760870826706944|1209516115424987880357888"
def inputClause5398 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,false),(80,true),(83,false),(90,false)]
theorem inputList5398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5398 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5398 (by decide) v hb
mask_input "5398|1247616241995760870826704896|1209516115424987880359936"
def inputClause5399 : CNF.NClause := [(42,false),(11,false),(66,true),(69,true),(72,false),(80,true),(83,false),(90,false)]
theorem inputList5399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5399 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5399 (by decide) v hb
mask_input "5399|1247616168208784575988500480|1209589902401282718564352"
def inputClause5400 : CNF.NClause := [(42,false),(11,true),(66,true),(69,true),(72,false),(80,true),(83,false),(90,false)]
theorem inputList5400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5400 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5400 (by decide) v hb
mask_input "5400|1247616168208784575988498432|1209589902401282718566400"
def inputClause5401 : CNF.NClause := [(42,false),(11,false),(66,false),(69,false),(72,true),(80,true),(83,false),(90,false)]
theorem inputList5401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5401 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5401 (by decide) v hb
mask_input "5401|1247612109925088359887144960|1213648186097498819919872"
def inputClause5402 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,true),(80,true),(83,false),(90,false)]
theorem inputList5402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5402 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5402 (by decide) v hb
mask_input "5402|1247612109925088359887142912|1213648186097498819921920"
def inputClause5403 : CNF.NClause := [(42,false),(11,false),(66,true),(69,false),(72,true),(80,true),(83,false),(90,false)]
theorem inputList5403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5403 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5403 (by decide) v hb
mask_input "5403|1247612036138112065048938496|1213721973073793658126336"
def inputClause5404 : CNF.NClause := [(42,false),(11,true),(66,true),(69,false),(72,true),(80,true),(83,false),(90,false)]
theorem inputList5404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5404 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5404 (by decide) v hb
mask_input "5404|1247612036138112065048936448|1213721973073793658128384"
def inputClause5405 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(72,true),(80,true),(83,false),(90,false)]
theorem inputList5405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5405 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5405 (by decide) v hb
mask_input "5405|1247611519629278001181493248|1214238481907857525571584"
def inputClause5406 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,true),(80,true),(83,false),(90,false)]
theorem inputList5406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5406 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5406 (by decide) v hb
mask_input "5406|1247611519629278001181491200|1214238481907857525573632"
def inputClause5407 : CNF.NClause := [(42,false),(11,false),(66,true),(69,true),(72,true),(80,true),(83,false),(90,false)]
theorem inputList5407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5407 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5407 (by decide) v hb
mask_input "5407|1247611445842301706343286784|1214312268884152363778048"
def inputClause5408 : CNF.NClause := [(42,false),(11,true),(66,true),(69,true),(72,true),(80,true),(83,false),(90,false)]
theorem inputList5408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5408 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5408 (by decide) v hb
mask_input "5408|1247611445842301706343284736|1214312268884152363780096"
def inputClause5409 : CNF.NClause := [(42,false),(11,false),(66,false),(69,false),(72,false),(80,false),(83,true),(90,false)]
theorem inputList5409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5409 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5409 (by decide) v hb
mask_input "5409|1239154351554268825309415424|9671406556917033397649408"
def inputClause5410 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,false),(80,false),(83,true),(90,false)]
theorem inputList5410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5410 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5410 (by decide) v hb
mask_input "5410|1239154351554268825309413376|9671406556917033397651456"
def inputClause5411 : CNF.NClause := [(42,false),(11,false),(66,true),(69,false),(72,false),(80,false),(83,true),(90,false)]
theorem inputList5411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5411 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5411 (by decide) v hb
mask_input "5411|1239154277767292530471208960|9671480343893328235855872"
def inputClause5412 : CNF.NClause := [(42,false),(11,true),(66,true),(69,false),(72,false),(80,false),(83,true),(90,false)]
theorem inputList5412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5412 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5412 (by decide) v hb
mask_input "5412|1239154277767292530471206912|9671480343893328235857920"
def inputClause5413 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(72,false),(80,false),(83,true),(90,false)]
theorem inputList5413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5413 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5413 (by decide) v hb
mask_input "5413|1239153761258458466603763712|9671996852727392103301120"
def inputClause5414 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,false),(80,false),(83,true),(90,false)]
theorem inputList5414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5414 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5414 (by decide) v hb
mask_input "5414|1239153761258458466603761664|9671996852727392103303168"
def inputClause5415 : CNF.NClause := [(42,false),(11,false),(66,true),(69,true),(72,false),(80,false),(83,true),(90,false)]
theorem inputList5415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5415 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5415 (by decide) v hb
mask_input "5415|1239153687471482171765557248|9672070639703686941507584"
def inputClause5416 : CNF.NClause := [(42,false),(11,true),(66,true),(69,true),(72,false),(80,false),(83,true),(90,false)]
theorem inputList5416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5416 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5416 (by decide) v hb
mask_input "5416|1239153687471482171765555200|9672070639703686941509632"
def inputClause5417 : CNF.NClause := [(42,false),(11,false),(66,false),(69,false),(72,true),(80,false),(83,true),(90,false)]
theorem inputList5417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5417 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5417 (by decide) v hb
mask_input "5417|1239149629187785955664201728|9676128923399903042863104"
def inputClause5418 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,true),(80,false),(83,true),(90,false)]
theorem inputList5418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5418 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5418 (by decide) v hb
mask_input "5418|1239149629187785955664199680|9676128923399903042865152"
def inputClause5419 : CNF.NClause := [(42,false),(11,false),(66,true),(69,false),(72,true),(80,false),(83,true),(90,false)]
theorem inputList5419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5419 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5419 (by decide) v hb
mask_input "5419|1239149555400809660825995264|9676202710376197881069568"
def inputClause5420 : CNF.NClause := [(42,false),(11,true),(66,true),(69,false),(72,true),(80,false),(83,true),(90,false)]
theorem inputList5420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5420 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5420 (by decide) v hb
mask_input "5420|1239149555400809660825993216|9676202710376197881071616"
def inputClause5421 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(72,true),(80,false),(83,true),(90,false)]
theorem inputList5421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5421 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5421 (by decide) v hb
mask_input "5421|1239149038891975596958550016|9676719219210261748514816"
def inputClause5422 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,true),(80,false),(83,true),(90,false)]
theorem inputList5422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5422 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5422 (by decide) v hb
mask_input "5422|1239149038891975596958547968|9676719219210261748516864"
def inputClause5423 : CNF.NClause := [(42,false),(11,false),(66,true),(69,true),(72,true),(80,false),(83,true),(90,false)]
theorem inputList5423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5423 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5423 (by decide) v hb
mask_input "5423|1239148965104999302120343552|9676793006186556586721280"
def inputClause5424 : CNF.NClause := [(42,false),(11,true),(66,true),(69,true),(72,true),(80,false),(83,true),(90,false)]
theorem inputList5424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5424 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5424 (by decide) v hb
mask_input "5424|1239148965104999302120341504|9676793006186556586723328"
def inputClause5425 : CNF.NClause := [(42,false),(11,false),(66,false),(69,false),(72,false),(80,true),(83,true),(90,false)]
theorem inputList5425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5425 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5425 (by decide) v hb
mask_input "5425|1237945425734654196134709248|10880332376531662572355584"
def inputClause5426 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,false),(80,true),(83,true),(90,false)]
theorem inputList5426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5426 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5426 (by decide) v hb
mask_input "5426|1237945425734654196134707200|10880332376531662572357632"
def inputClause5427 : CNF.NClause := [(42,false),(11,false),(66,true),(69,false),(72,false),(80,true),(83,true),(90,false)]
theorem inputList5427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5427 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5427 (by decide) v hb
mask_input "5427|1237945351947677901296502784|10880406163507957410562048"
def inputClause5428 : CNF.NClause := [(42,false),(11,true),(66,true),(69,false),(72,false),(80,true),(83,true),(90,false)]
theorem inputList5428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5428 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5428 (by decide) v hb
mask_input "5428|1237945351947677901296500736|10880406163507957410564096"
def inputClause5429 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(72,false),(80,true),(83,true),(90,false)]
theorem inputList5429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5429 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5429 (by decide) v hb
mask_input "5429|1237944835438843837429057536|10880922672342021278007296"
def inputClause5430 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,false),(80,true),(83,true),(90,false)]
theorem inputList5430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5430 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5430 (by decide) v hb
mask_input "5430|1237944835438843837429055488|10880922672342021278009344"
def inputClause5431 : CNF.NClause := [(42,false),(11,false),(66,true),(69,true),(72,false),(80,true),(83,true),(90,false)]
theorem inputList5431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5431 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5431 (by decide) v hb
mask_input "5431|1237944761651867542590851072|10880996459318316116213760"
def inputClause5432 : CNF.NClause := [(42,false),(11,true),(66,true),(69,true),(72,false),(80,true),(83,true),(90,false)]
theorem inputList5432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5432 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5432 (by decide) v hb
mask_input "5432|1237944761651867542590849024|10880996459318316116215808"
def inputClause5433 : CNF.NClause := [(42,false),(11,false),(66,false),(69,false),(72,true),(80,true),(83,true),(90,false)]
theorem inputList5433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5433 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5433 (by decide) v hb
mask_input "5433|1237940703368171326489495552|10885054743014532217569280"
def inputClause5434 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,true),(80,true),(83,true),(90,false)]
theorem inputList5434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5434 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5434 (by decide) v hb
mask_input "5434|1237940703368171326489493504|10885054743014532217571328"
def inputClause5435 : CNF.NClause := [(42,false),(11,false),(66,true),(69,false),(72,true),(80,true),(83,true),(90,false)]
theorem inputList5435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5435 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5435 (by decide) v hb
mask_input "5435|1237940629581195031651289088|10885128529990827055775744"
def inputClause5436 : CNF.NClause := [(42,false),(11,true),(66,true),(69,false),(72,true),(80,true),(83,true),(90,false)]
theorem inputList5436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5436 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5436 (by decide) v hb
mask_input "5436|1237940629581195031651287040|10885128529990827055777792"
end Percolation.MaskChain
