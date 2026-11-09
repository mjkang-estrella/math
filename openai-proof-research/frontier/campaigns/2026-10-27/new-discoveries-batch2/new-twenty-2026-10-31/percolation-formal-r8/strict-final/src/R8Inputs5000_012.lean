import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause4403 : CNF.NClause := [(34,false),(3,false),(65,true),(70,false),(75,false),(80,true),(85,true),(87,false)]
theorem inputList4403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4403 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4403 (by decide) v hb
mask_input "4403|154781464434156226115272712|39894588940770910184407040"
def inputClause4404 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,false),(80,true),(85,true),(87,false)]
theorem inputList4404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4404 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4404 (by decide) v hb
mask_input "4404|154781464434156226115272704|39894588940770910184407048"
def inputClause4405 : CNF.NClause := [(34,false),(3,false),(65,false),(70,true),(75,false),(80,true),(85,true),(87,false)]
theorem inputList4405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4405 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4405 (by decide) v hb
mask_input "4405|154780320736023656123072520|39895732638903480176607232"
def inputClause4406 : CNF.NClause := [(34,false),(3,true),(65,false),(70,true),(75,false),(80,true),(85,true),(87,false)]
theorem inputList4406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4406 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4406 (by decide) v hb
mask_input "4406|154780320736023656123072512|39895732638903480176607240"
def inputClause4407 : CNF.NClause := [(34,false),(3,false),(65,true),(70,true),(75,false),(80,true),(85,true),(87,false)]
theorem inputList4407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4407 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4407 (by decide) v hb
mask_input "4407|154780283842535508703969288|39895769532391627595710464"
def inputClause4408 : CNF.NClause := [(34,false),(3,true),(65,true),(70,true),(75,false),(80,true),(85,true),(87,false)]
theorem inputList4408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4408 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4408 (by decide) v hb
mask_input "4408|154780283842535508703969280|39895769532391627595710472"
def inputClause4409 : CNF.NClause := [(34,false),(3,false),(65,false),(70,false),(75,true),(80,true),(85,true),(87,false)]
theorem inputList4409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4409 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4409 (by decide) v hb
mask_input "4409|154743722395781416372666376|39932330979145719927013376"
def inputClause4410 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,true),(80,true),(85,true),(87,false)]
theorem inputList4410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4410 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4410 (by decide) v hb
mask_input "4410|154743722395781416372666368|39932330979145719927013384"
def inputClause4411 : CNF.NClause := [(34,false),(3,false),(65,true),(70,false),(75,true),(80,true),(85,true),(87,false)]
theorem inputList4411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4411 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4411 (by decide) v hb
mask_input "4411|154743685502293268953563144|39932367872633867346116608"
def inputClause4412 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,true),(80,true),(85,true),(87,false)]
theorem inputList4412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4412 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4412 (by decide) v hb
mask_input "4412|154743685502293268953563136|39932367872633867346116616"
def inputClause4413 : CNF.NClause := [(34,false),(3,false),(65,false),(70,true),(75,true),(80,true),(85,true),(87,false)]
theorem inputList4413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4413 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4413 (by decide) v hb
mask_input "4413|154742541804160698961362952|39933511570766437338316800"
def inputClause4414 : CNF.NClause := [(34,false),(3,true),(65,false),(70,true),(75,true),(80,true),(85,true),(87,false)]
theorem inputList4414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4414 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4414 (by decide) v hb
mask_input "4414|154742541804160698961362944|39933511570766437338316808"
def inputClause4415 : CNF.NClause := [(34,false),(3,false),(65,true),(70,true),(75,true),(80,true),(85,true),(87,false)]
theorem inputList4415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4415 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4415 (by decide) v hb
mask_input "4415|154742504910672551542259720|39933548464254584757420032"
def inputClause4416 : CNF.NClause := [(34,false),(3,true),(65,true),(70,true),(75,true),(80,true),(85,true),(87,false)]
theorem inputList4416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4416 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4416 (by decide) v hb
mask_input "4416|154742504910672551542259712|39933548464254584757420040"
def inputClause4417 : CNF.NClause := [(34,false),(3,false),(65,false),(70,false),(75,false),(80,false),(85,false),(87,true)]
theorem inputList4417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4417 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4417 (by decide) v hb
mask_input "4417|39933548464254601937289224|154742504910672534362390528"
def inputClause4418 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,false),(80,false),(85,false),(87,true)]
theorem inputList4418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4418 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4418 (by decide) v hb
mask_input "4418|39933548464254601937289216|154742504910672534362390536"
def inputClause4419 : CNF.NClause := [(34,false),(3,false),(65,true),(70,false),(75,false),(80,false),(85,false),(87,true)]
theorem inputList4419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4419 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4419 (by decide) v hb
mask_input "4419|39933511570766454518185992|154742541804160681781493760"
def inputClause4420 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,false),(80,false),(85,false),(87,true)]
theorem inputList4420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4420 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4420 (by decide) v hb
mask_input "4420|39933511570766454518185984|154742541804160681781493768"
def inputClause4421 : CNF.NClause := [(34,false),(3,false),(65,false),(70,true),(75,false),(80,false),(85,false),(87,true)]
theorem inputList4421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4421 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4421 (by decide) v hb
mask_input "4421|39932367872633884525985800|154743685502293251773693952"
def inputClause4422 : CNF.NClause := [(34,false),(3,true),(65,false),(70,true),(75,false),(80,false),(85,false),(87,true)]
theorem inputList4422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4422 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4422 (by decide) v hb
mask_input "4422|39932367872633884525985792|154743685502293251773693960"
def inputClause4424 : CNF.NClause := [(34,false),(3,true),(65,true),(70,true),(75,false),(80,false),(85,false),(87,true)]
theorem inputList4424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4424 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4424 (by decide) v hb
mask_input "4424|39932330979145737106882560|154743722395781399192797192"
def inputClause4425 : CNF.NClause := [(34,false),(3,false),(65,false),(70,false),(75,true),(80,false),(85,false),(87,true)]
theorem inputList4425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4425 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4425 (by decide) v hb
mask_input "4425|39895769532391644775579656|154780283842535491524100096"
def inputClause4426 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,true),(80,false),(85,false),(87,true)]
theorem inputList4426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4426 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4426 (by decide) v hb
mask_input "4426|39895769532391644775579648|154780283842535491524100104"
def inputClause4427 : CNF.NClause := [(34,false),(3,false),(65,true),(70,false),(75,true),(80,false),(85,false),(87,true)]
theorem inputList4427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4427 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4427 (by decide) v hb
mask_input "4427|39895732638903497356476424|154780320736023638943203328"
def inputClause4428 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,true),(80,false),(85,false),(87,true)]
theorem inputList4428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4428 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4428 (by decide) v hb
mask_input "4428|39895732638903497356476416|154780320736023638943203336"
def inputClause4429 : CNF.NClause := [(34,false),(3,false),(65,false),(70,true),(75,true),(80,false),(85,false),(87,true)]
theorem inputList4429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4429 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4429 (by decide) v hb
mask_input "4429|39894588940770927364276232|154781464434156208935403520"
def inputClause4430 : CNF.NClause := [(34,false),(3,true),(65,false),(70,true),(75,true),(80,false),(85,false),(87,true)]
theorem inputList4430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4430 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4430 (by decide) v hb
mask_input "4430|39894588940770927364276224|154781464434156208935403528"
def inputClause4431 : CNF.NClause := [(34,false),(3,false),(65,true),(70,true),(75,true),(80,false),(85,false),(87,true)]
theorem inputList4431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4431 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4431 (by decide) v hb
mask_input "4431|39894552047282779945173000|154781501327644356354506752"
def inputClause4432 : CNF.NClause := [(34,false),(3,true),(65,true),(70,true),(75,true),(80,false),(85,false),(87,true)]
theorem inputList4432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4432 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4432 (by decide) v hb
mask_input "4432|39894552047282779945172992|154781501327644356354506760"
def inputClause4433 : CNF.NClause := [(34,false),(3,false),(65,false),(70,false),(75,false),(80,true),(85,false),(87,true)]
theorem inputList4433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4433 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4433 (by decide) v hb
mask_input "4433|38724622644639972762583048|155951430730287163537096704"
def inputClause4434 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,false),(80,true),(85,false),(87,true)]
theorem inputList4434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4434 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4434 (by decide) v hb
mask_input "4434|38724622644639972762583040|155951430730287163537096712"
def inputClause4435 : CNF.NClause := [(34,false),(3,false),(65,true),(70,false),(75,false),(80,true),(85,false),(87,true)]
theorem inputList4435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4435 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4435 (by decide) v hb
mask_input "4435|38724585751151825343479816|155951467623775310956199936"
def inputClause4436 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,false),(80,true),(85,false),(87,true)]
theorem inputList4436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4436 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4436 (by decide) v hb
mask_input "4436|38724585751151825343479808|155951467623775310956199944"
def inputClause4437 : CNF.NClause := [(34,false),(3,false),(65,false),(70,true),(75,false),(80,true),(85,false),(87,true)]
theorem inputList4437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4437 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4437 (by decide) v hb
mask_input "4437|38723442053019255351279624|155952611321907880948400128"
def inputClause4438 : CNF.NClause := [(34,false),(3,true),(65,false),(70,true),(75,false),(80,true),(85,false),(87,true)]
theorem inputList4438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4438 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4438 (by decide) v hb
mask_input "4438|38723442053019255351279616|155952611321907880948400136"
def inputClause4439 : CNF.NClause := [(34,false),(3,false),(65,true),(70,true),(75,false),(80,true),(85,false),(87,true)]
theorem inputList4439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4439 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4439 (by decide) v hb
mask_input "4439|38723405159531107932176392|155952648215396028367503360"
def inputClause4440 : CNF.NClause := [(34,false),(3,true),(65,true),(70,true),(75,false),(80,true),(85,false),(87,true)]
theorem inputList4440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4440 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4440 (by decide) v hb
mask_input "4440|38723405159531107932176384|155952648215396028367503368"
def inputClause4441 : CNF.NClause := [(34,false),(3,false),(65,false),(70,false),(75,true),(80,true),(85,false),(87,true)]
theorem inputList4441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4441 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4441 (by decide) v hb
mask_input "4441|38686843712777015600873480|155989209662150120698806272"
def inputClause4442 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,true),(80,true),(85,false),(87,true)]
theorem inputList4442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4442 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4442 (by decide) v hb
mask_input "4442|38686843712777015600873472|155989209662150120698806280"
def inputClause4443 : CNF.NClause := [(34,false),(3,false),(65,true),(70,false),(75,true),(80,true),(85,false),(87,true)]
theorem inputList4443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4443 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 3) (spread_mem 3) inputClause4443 (by decide) v hb
mask_input "4443|38686806819288868181770248|155989246555638268117909504"
end Percolation.MaskChain
