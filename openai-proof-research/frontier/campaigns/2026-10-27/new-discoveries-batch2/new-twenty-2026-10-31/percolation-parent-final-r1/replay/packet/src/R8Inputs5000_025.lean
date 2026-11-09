import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause5437 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(72,true),(80,true),(83,true),(90,false)]
theorem inputList5437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5437 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5437 (by decide) v hb
mask_input "5437|1237940113072360967783843840|10885645038824890923220992"
def inputClause5438 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,true),(80,true),(83,true),(90,false)]
theorem inputList5438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5438 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5438 (by decide) v hb
mask_input "5438|1237940113072360967783841792|10885645038824890923223040"
def inputClause5439 : CNF.NClause := [(42,false),(11,false),(66,true),(69,true),(72,true),(80,true),(83,true),(90,false)]
theorem inputList5439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5439 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5439 (by decide) v hb
mask_input "5439|1237940039285384672945637376|10885718825801185761427456"
def inputClause5440 : CNF.NClause := [(42,false),(11,true),(66,true),(69,true),(72,true),(80,true),(83,true),(90,false)]
theorem inputList5440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5440 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5440 (by decide) v hb
mask_input "5440|1237940039285384672945635328|10885718825801185761429504"
def inputClause5441 : CNF.NClause := [(42,false),(11,false),(66,false),(69,false),(72,false),(80,false),(83,false),(90,true)]
theorem inputList5441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5441 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5441 (by decide) v hb
mask_input "5441|10885718825805583807940608|1237940039285380274899124224"
def inputClause5442 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,false),(80,false),(83,false),(90,true)]
theorem inputList5442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5442 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5442 (by decide) v hb
mask_input "5442|10885718825805583807938560|1237940039285380274899126272"
def inputClause5443 : CNF.NClause := [(42,false),(11,false),(66,true),(69,false),(72,false),(80,false),(83,false),(90,true)]
theorem inputList5443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5443 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5443 (by decide) v hb
mask_input "5443|10885645038829288969734144|1237940113072356569737330688"
def inputClause5444 : CNF.NClause := [(42,false),(11,true),(66,true),(69,false),(72,false),(80,false),(83,false),(90,true)]
theorem inputList5444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5444 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5444 (by decide) v hb
mask_input "5444|10885645038829288969732096|1237940113072356569737332736"
def inputClause5445 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(72,false),(80,false),(83,false),(90,true)]
theorem inputList5445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5445 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5445 (by decide) v hb
mask_input "5445|10885128529995225102288896|1237940629581190633604775936"
def inputClause5446 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,false),(80,false),(83,false),(90,true)]
theorem inputList5446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5446 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5446 (by decide) v hb
mask_input "5446|10885128529995225102286848|1237940629581190633604777984"
def inputClause5447 : CNF.NClause := [(42,false),(11,false),(66,true),(69,true),(72,false),(80,false),(83,false),(90,true)]
theorem inputList5447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5447 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5447 (by decide) v hb
mask_input "5447|10885054743018930264082432|1237940703368166928442982400"
def inputClause5448 : CNF.NClause := [(42,false),(11,true),(66,true),(69,true),(72,false),(80,false),(83,false),(90,true)]
theorem inputList5448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5448 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5448 (by decide) v hb
mask_input "5448|10885054743018930264080384|1237940703368166928442984448"
def inputClause5449 : CNF.NClause := [(42,false),(11,false),(66,false),(69,false),(72,true),(80,false),(83,false),(90,true)]
theorem inputList5449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5449 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5449 (by decide) v hb
mask_input "5449|10880996459322714162726912|1237944761651863144544337920"
def inputClause5450 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,true),(80,false),(83,false),(90,true)]
theorem inputList5450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5450 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5450 (by decide) v hb
mask_input "5450|10880996459322714162724864|1237944761651863144544339968"
def inputClause5451 : CNF.NClause := [(42,false),(11,false),(66,true),(69,false),(72,true),(80,false),(83,false),(90,true)]
theorem inputList5451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5451 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5451 (by decide) v hb
mask_input "5451|10880922672346419324520448|1237944835438839439382544384"
def inputClause5452 : CNF.NClause := [(42,false),(11,true),(66,true),(69,false),(72,true),(80,false),(83,false),(90,true)]
theorem inputList5452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5452 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5452 (by decide) v hb
mask_input "5452|10880922672346419324518400|1237944835438839439382546432"
def inputClause5453 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(72,true),(80,false),(83,false),(90,true)]
theorem inputList5453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5453 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5453 (by decide) v hb
mask_input "5453|10880406163512355457075200|1237945351947673503249989632"
def inputClause5454 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,true),(80,false),(83,false),(90,true)]
theorem inputList5454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5454 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5454 (by decide) v hb
mask_input "5454|10880406163512355457073152|1237945351947673503249991680"
def inputClause5455 : CNF.NClause := [(42,false),(11,false),(66,true),(69,true),(72,true),(80,false),(83,false),(90,true)]
theorem inputList5455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5455 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5455 (by decide) v hb
mask_input "5455|10880332376536060618868736|1237945425734649798088196096"
def inputClause5456 : CNF.NClause := [(42,false),(11,true),(66,true),(69,true),(72,true),(80,false),(83,false),(90,true)]
theorem inputList5456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5456 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5456 (by decide) v hb
mask_input "5456|10880332376536060618866688|1237945425734649798088198144"
def inputClause5457 : CNF.NClause := [(42,false),(11,false),(66,false),(69,false),(72,false),(80,true),(83,false),(90,true)]
theorem inputList5457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5457 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5457 (by decide) v hb
mask_input "5457|9676793006190954633234432|1239148965104994904073830400"
def inputClause5458 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,false),(80,true),(83,false),(90,true)]
theorem inputList5458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5458 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5458 (by decide) v hb
mask_input "5458|9676793006190954633232384|1239148965104994904073832448"
def inputClause5459 : CNF.NClause := [(42,false),(11,false),(66,true),(69,false),(72,false),(80,true),(83,false),(90,true)]
theorem inputList5459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5459 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5459 (by decide) v hb
mask_input "5459|9676719219214659795027968|1239149038891971198912036864"
def inputClause5460 : CNF.NClause := [(42,false),(11,true),(66,true),(69,false),(72,false),(80,true),(83,false),(90,true)]
theorem inputList5460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5460 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5460 (by decide) v hb
mask_input "5460|9676719219214659795025920|1239149038891971198912038912"
def inputClause5461 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(72,false),(80,true),(83,false),(90,true)]
theorem inputList5461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5461 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5461 (by decide) v hb
mask_input "5461|9676202710380595927582720|1239149555400805262779482112"
def inputClause5462 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,false),(80,true),(83,false),(90,true)]
theorem inputList5462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5462 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5462 (by decide) v hb
mask_input "5462|9676202710380595927580672|1239149555400805262779484160"
def inputClause5464 : CNF.NClause := [(42,false),(11,true),(66,true),(69,true),(72,false),(80,true),(83,false),(90,true)]
theorem inputList5464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5464 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5464 (by decide) v hb
mask_input "5464|9676128923404301089374208|1239149629187781557617690624"
def inputClause5465 : CNF.NClause := [(42,false),(11,false),(66,false),(69,false),(72,true),(80,true),(83,false),(90,true)]
theorem inputList5465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5465 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5465 (by decide) v hb
mask_input "5465|9672070639708084988020736|1239153687471477773719044096"
def inputClause5466 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,true),(80,true),(83,false),(90,true)]
theorem inputList5466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5466 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5466 (by decide) v hb
mask_input "5466|9672070639708084988018688|1239153687471477773719046144"
def inputClause5467 : CNF.NClause := [(42,false),(11,false),(66,true),(69,false),(72,true),(80,true),(83,false),(90,true)]
theorem inputList5467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5467 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5467 (by decide) v hb
mask_input "5467|9671996852731790149814272|1239153761258454068557250560"
def inputClause5468 : CNF.NClause := [(42,false),(11,true),(66,true),(69,false),(72,true),(80,true),(83,false),(90,true)]
theorem inputList5468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5468 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5468 (by decide) v hb
mask_input "5468|9671996852731790149812224|1239153761258454068557252608"
def inputClause5469 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(72,true),(80,true),(83,false),(90,true)]
theorem inputList5469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5469 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5469 (by decide) v hb
mask_input "5469|9671480343897726282369024|1239154277767288132424695808"
def inputClause5470 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,true),(80,true),(83,false),(90,true)]
theorem inputList5470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5470 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5470 (by decide) v hb
mask_input "5470|9671480343897726282366976|1239154277767288132424697856"
def inputClause5472 : CNF.NClause := [(42,false),(11,true),(66,true),(69,true),(72,true),(80,true),(83,false),(90,true)]
theorem inputList5472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5472 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5472 (by decide) v hb
mask_input "5472|9671406556921431444160512|1239154351554264427262904320"
def inputClause5473 : CNF.NClause := [(42,false),(11,false),(66,false),(69,false),(72,false),(80,false),(83,true),(90,true)]
theorem inputList5473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5473 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5473 (by decide) v hb
mask_input "5473|1214312268888550410291200|1247611445842297308296773632"
def inputClause5474 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,false),(80,false),(83,true),(90,true)]
theorem inputList5474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5474 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5474 (by decide) v hb
mask_input "5474|1214312268888550410289152|1247611445842297308296775680"
def inputClause5475 : CNF.NClause := [(42,false),(11,false),(66,true),(69,false),(72,false),(80,false),(83,true),(90,true)]
theorem inputList5475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5475 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5475 (by decide) v hb
mask_input "5475|1214238481912255572084736|1247611519629273603134980096"
def inputClause5476 : CNF.NClause := [(42,false),(11,true),(66,true),(69,false),(72,false),(80,false),(83,true),(90,true)]
theorem inputList5476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5476 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5476 (by decide) v hb
mask_input "5476|1214238481912255572082688|1247611519629273603134982144"
def inputClause5477 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(72,false),(80,false),(83,true),(90,true)]
theorem inputList5477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5477 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5477 (by decide) v hb
mask_input "5477|1213721973078191704639488|1247612036138107667002425344"
def inputClause5478 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(72,false),(80,false),(83,true),(90,true)]
theorem inputList5478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5478 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 11) (spread_mem 11) inputClause5478 (by decide) v hb
mask_input "5478|1213721973078191704637440|1247612036138107667002427392"
end Percolation.MaskChain
