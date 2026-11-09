import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause4525 : CNF.NClause := [(35,false),(4,false),(63,false),(68,true),(73,true),(78,false),(83,true),(87,false)]
theorem inputList4525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4525 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4525 (by decide) v hb
mask_input "4525|155044745588948262870581264|9681146437787952040902656"
def inputClause4526 : CNF.NClause := [(35,false),(4,true),(63,false),(68,true),(73,true),(78,false),(83,true),(87,false)]
theorem inputList4526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4526 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4526 (by decide) v hb
mask_input "4526|155044745588948262870581248|9681146437787952040902672"
def inputClause4527 : CNF.NClause := [(35,false),(4,false),(63,true),(68,true),(73,true),(78,false),(83,true),(87,false)]
theorem inputList4527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4527 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4527 (by decide) v hb
mask_input "4527|155044736365576226015805456|9681155661159988895678464"
def inputClause4528 : CNF.NClause := [(35,false),(4,true),(63,true),(68,true),(73,true),(78,false),(83,true),(87,false)]
theorem inputList4528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4528 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4528 (by decide) v hb
mask_input "4528|155044736365576226015805440|9681155661159988895678480"
def inputClause4529 : CNF.NClause := [(35,false),(4,false),(63,false),(68,false),(73,false),(78,true),(83,true),(87,false)]
theorem inputList4529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4529 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4529 (by decide) v hb
mask_input "4529|154752254014915524220157968|9973638011820690691325952"
def inputClause4530 : CNF.NClause := [(35,false),(4,true),(63,false),(68,false),(73,false),(78,true),(83,true),(87,false)]
theorem inputList4530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4530 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4530 (by decide) v hb
mask_input "4530|154752254014915524220157952|9973638011820690691325968"
def inputClause4531 : CNF.NClause := [(35,false),(4,false),(63,true),(68,false),(73,false),(78,true),(83,true),(87,false)]
theorem inputList4531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4531 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4531 (by decide) v hb
mask_input "4531|154752244791543487365382160|9973647235192727546101760"
def inputClause4532 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,false),(78,true),(83,true),(87,false)]
theorem inputList4532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4532 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4532 (by decide) v hb
mask_input "4532|154752244791543487365382144|9973647235192727546101776"
def inputClause4533 : CNF.NClause := [(35,false),(4,false),(63,false),(68,true),(73,false),(78,true),(83,true),(87,false)]
theorem inputList4533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4533 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4533 (by decide) v hb
mask_input "4533|154751958867010344867332112|9973933159725870044151808"
def inputClause4534 : CNF.NClause := [(35,false),(4,true),(63,false),(68,true),(73,false),(78,true),(83,true),(87,false)]
theorem inputList4534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4534 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4534 (by decide) v hb
mask_input "4534|154751958867010344867332096|9973933159725870044151824"
def inputClause4535 : CNF.NClause := [(35,false),(4,false),(63,true),(68,true),(73,false),(78,true),(83,true),(87,false)]
theorem inputList4535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4535 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4535 (by decide) v hb
mask_input "4535|154751949643638308012556304|9973942383097906898927616"
def inputClause4536 : CNF.NClause := [(35,false),(4,true),(63,true),(68,true),(73,false),(78,true),(83,true),(87,false)]
theorem inputList4536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4536 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4536 (by decide) v hb
mask_input "4536|154751949643638308012556288|9973942383097906898927632"
def inputClause4537 : CNF.NClause := [(35,false),(4,false),(63,false),(68,false),(73,true),(78,true),(83,true),(87,false)]
theorem inputList4537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4537 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4537 (by decide) v hb
mask_input "4537|154742809281949784929730576|9983082744786429981753344"
def inputClause4538 : CNF.NClause := [(35,false),(4,true),(63,false),(68,false),(73,true),(78,true),(83,true),(87,false)]
theorem inputList4538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4538 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4538 (by decide) v hb
mask_input "4538|154742809281949784929730560|9983082744786429981753360"
def inputClause4539 : CNF.NClause := [(35,false),(4,false),(63,true),(68,false),(73,true),(78,true),(83,true),(87,false)]
theorem inputList4539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4539 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4539 (by decide) v hb
mask_input "4539|154742800058577748074954768|9983091968158466836529152"
def inputClause4540 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,true),(78,true),(83,true),(87,false)]
theorem inputList4540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4540 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4540 (by decide) v hb
mask_input "4540|154742800058577748074954752|9983091968158466836529168"
def inputClause4541 : CNF.NClause := [(35,false),(4,false),(63,false),(68,true),(73,true),(78,true),(83,true),(87,false)]
theorem inputList4541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4541 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4541 (by decide) v hb
mask_input "4541|154742514134044605576904720|9983377892691609334579200"
def inputClause4542 : CNF.NClause := [(35,false),(4,true),(63,false),(68,true),(73,true),(78,true),(83,true),(87,false)]
theorem inputList4542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4542 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4542 (by decide) v hb
mask_input "4542|154742514134044605576904704|9983377892691609334579216"
def inputClause4543 : CNF.NClause := [(35,false),(4,false),(63,true),(68,true),(73,true),(78,true),(83,true),(87,false)]
theorem inputList4543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4543 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4543 (by decide) v hb
mask_input "4543|154742504910672568722128912|9983387116063646189355008"
def inputClause4544 : CNF.NClause := [(35,false),(4,true),(63,true),(68,true),(73,true),(78,true),(83,true),(87,false)]
theorem inputList4544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4544 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4544 (by decide) v hb
mask_input "4544|154742504910672568722128896|9983387116063646189355024"
def inputClause4545 : CNF.NClause := [(35,false),(4,false),(63,false),(68,false),(73,false),(78,false),(83,false),(87,true)]
theorem inputList4545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4545 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4545 (by decide) v hb
mask_input "4545|9983387116063680549093392|154742504910672534362390528"
def inputClause4546 : CNF.NClause := [(35,false),(4,true),(63,false),(68,false),(73,false),(78,false),(83,false),(87,true)]
theorem inputList4546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4546 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4546 (by decide) v hb
mask_input "4546|9983387116063680549093376|154742504910672534362390544"
def inputClause4547 : CNF.NClause := [(35,false),(4,false),(63,true),(68,false),(73,false),(78,false),(83,false),(87,true)]
theorem inputList4547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4547 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4547 (by decide) v hb
mask_input "4547|9983377892691643694317584|154742514134044571217166336"
def inputClause4549 : CNF.NClause := [(35,false),(4,false),(63,false),(68,true),(73,false),(78,false),(83,false),(87,true)]
theorem inputList4549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4549 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4549 (by decide) v hb
mask_input "4549|9983091968158501196267536|154742800058577713715216384"
def inputClause4550 : CNF.NClause := [(35,false),(4,true),(63,false),(68,true),(73,false),(78,false),(83,false),(87,true)]
theorem inputList4550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4550 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4550 (by decide) v hb
mask_input "4550|9983091968158501196267520|154742800058577713715216400"
def inputClause4551 : CNF.NClause := [(35,false),(4,false),(63,true),(68,true),(73,false),(78,false),(83,false),(87,true)]
theorem inputList4551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4551 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4551 (by decide) v hb
mask_input "4551|9983082744786464341491728|154742809281949750569992192"
def inputClause4552 : CNF.NClause := [(35,false),(4,true),(63,true),(68,true),(73,false),(78,false),(83,false),(87,true)]
theorem inputList4552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4552 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4552 (by decide) v hb
mask_input "4552|9983082744786464341491712|154742809281949750569992208"
def inputClause4553 : CNF.NClause := [(35,false),(4,false),(63,false),(68,false),(73,true),(78,false),(83,false),(87,true)]
theorem inputList4553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4553 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4553 (by decide) v hb
mask_input "4553|9973942383097941258666000|154751949643638273652817920"
def inputClause4554 : CNF.NClause := [(35,false),(4,true),(63,false),(68,false),(73,true),(78,false),(83,false),(87,true)]
theorem inputList4554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4554 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4554 (by decide) v hb
mask_input "4554|9973942383097941258665984|154751949643638273652817936"
def inputClause4555 : CNF.NClause := [(35,false),(4,false),(63,true),(68,false),(73,true),(78,false),(83,false),(87,true)]
theorem inputList4555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4555 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4555 (by decide) v hb
mask_input "4555|9973933159725904403890192|154751958867010310507593728"
def inputClause4556 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,true),(78,false),(83,false),(87,true)]
theorem inputList4556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4556 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4556 (by decide) v hb
mask_input "4556|9973933159725904403890176|154751958867010310507593744"
def inputClause4557 : CNF.NClause := [(35,false),(4,false),(63,false),(68,true),(73,true),(78,false),(83,false),(87,true)]
theorem inputList4557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4557 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4557 (by decide) v hb
mask_input "4557|9973647235192761905840144|154752244791543453005643776"
def inputClause4558 : CNF.NClause := [(35,false),(4,true),(63,false),(68,true),(73,true),(78,false),(83,false),(87,true)]
theorem inputList4558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4558 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4558 (by decide) v hb
mask_input "4558|9973647235192761905840128|154752244791543453005643792"
def inputClause4559 : CNF.NClause := [(35,false),(4,false),(63,true),(68,true),(73,true),(78,false),(83,false),(87,true)]
theorem inputList4559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4559 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4559 (by decide) v hb
mask_input "4559|9973638011820725051064336|154752254014915489860419584"
def inputClause4560 : CNF.NClause := [(35,false),(4,true),(63,true),(68,true),(73,true),(78,false),(83,false),(87,true)]
theorem inputList4560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4560 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4560 (by decide) v hb
mask_input "4560|9973638011820725051064320|154752254014915489860419600"
def inputClause4561 : CNF.NClause := [(35,false),(4,false),(63,false),(68,false),(73,false),(78,true),(83,false),(87,true)]
theorem inputList4561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4561 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4561 (by decide) v hb
mask_input "4561|9681155661160023255416848|155044736365576191656067072"
def inputClause4562 : CNF.NClause := [(35,false),(4,true),(63,false),(68,false),(73,false),(78,true),(83,false),(87,true)]
theorem inputList4562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4562 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4562 (by decide) v hb
mask_input "4562|9681155661160023255416832|155044736365576191656067088"
def inputClause4563 : CNF.NClause := [(35,false),(4,false),(63,true),(68,false),(73,false),(78,true),(83,false),(87,true)]
theorem inputList4563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4563 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4563 (by decide) v hb
mask_input "4563|9681146437787986400641040|155044745588948228510842880"
def inputClause4564 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,false),(78,true),(83,false),(87,true)]
theorem inputList4564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4564 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4564 (by decide) v hb
mask_input "4564|9681146437787986400641024|155044745588948228510842896"
def inputClause4565 : CNF.NClause := [(35,false),(4,false),(63,false),(68,true),(73,false),(78,true),(83,false),(87,true)]
theorem inputList4565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4565 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4565 (by decide) v hb
mask_input "4565|9680860513254843902590992|155045031513481371008892928"
end Percolation.MaskChain
