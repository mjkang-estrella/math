import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause6557 : CNF.NClause := [(51,false),(20,false),(67,false),(68,true),(69,true),(70,true),(71,false),(92,false)]
theorem inputList6557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6557 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6557 (by decide) v hb
mask_input "6557|4951762665900966923910250496|2066035336255469780992"
def inputClause6558 : CNF.NClause := [(51,false),(20,true),(67,false),(68,true),(69,true),(70,true),(71,false),(92,false)]
theorem inputList6558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6558 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6558 (by decide) v hb
mask_input "6558|4951762665900966923909201920|2066035336255470829568"
def inputClause6559 : CNF.NClause := [(51,false),(20,false),(67,true),(68,true),(69,true),(70,true),(71,false),(92,false)]
theorem inputList6559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6559 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6559 (by decide) v hb
mask_input "6559|4951762518327014334233837568|2213609288845146193920"
def inputClause6560 : CNF.NClause := [(51,false),(20,true),(67,true),(68,true),(69,true),(70,true),(71,false),(92,false)]
theorem inputList6560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6560 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6560 (by decide) v hb
mask_input "6560|4951762518327014334232788992|2213609288845147242496"
def inputClause6561 : CNF.NClause := [(51,false),(20,false),(67,false),(68,false),(69,false),(70,false),(71,true),(92,false)]
theorem inputList6561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6561 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6561 (by decide) v hb
mask_input "6561|4951762370753061744557424640|2361183241434822606848"
def inputClause6562 : CNF.NClause := [(51,false),(20,true),(67,false),(68,false),(69,false),(70,false),(71,true),(92,false)]
theorem inputList6562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6562 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6562 (by decide) v hb
mask_input "6562|4951762370753061744556376064|2361183241434823655424"
def inputClause6563 : CNF.NClause := [(51,false),(20,false),(67,true),(68,false),(69,false),(70,false),(71,true),(92,false)]
theorem inputList6563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6563 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6563 (by decide) v hb
mask_input "6563|4951762223179109154881011712|2508757194024499019776"
def inputClause6564 : CNF.NClause := [(51,false),(20,true),(67,true),(68,false),(69,false),(70,false),(71,true),(92,false)]
theorem inputList6564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6564 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6564 (by decide) v hb
mask_input "6564|4951762223179109154879963136|2508757194024500068352"
def inputClause6565 : CNF.NClause := [(51,false),(20,false),(67,false),(68,true),(69,false),(70,false),(71,true),(92,false)]
theorem inputList6565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6565 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6565 (by decide) v hb
mask_input "6565|4951762075605156565204598784|2656331146614175432704"
def inputClause6566 : CNF.NClause := [(51,false),(20,true),(67,false),(68,true),(69,false),(70,false),(71,true),(92,false)]
theorem inputList6566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6566 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6566 (by decide) v hb
mask_input "6566|4951762075605156565203550208|2656331146614176481280"
def inputClause6567 : CNF.NClause := [(51,false),(20,false),(67,true),(68,true),(69,false),(70,false),(71,true),(92,false)]
theorem inputList6567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6567 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6567 (by decide) v hb
mask_input "6567|4951761928031203975528185856|2803905099203851845632"
def inputClause6568 : CNF.NClause := [(51,false),(20,true),(67,true),(68,true),(69,false),(70,false),(71,true),(92,false)]
theorem inputList6568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6568 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6568 (by decide) v hb
mask_input "6568|4951761928031203975527137280|2803905099203852894208"
def inputClause6569 : CNF.NClause := [(51,false),(20,false),(67,false),(68,false),(69,true),(70,false),(71,true),(92,false)]
theorem inputList6569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6569 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6569 (by decide) v hb
mask_input "6569|4951761780457251385851772928|2951479051793528258560"
def inputClause6570 : CNF.NClause := [(51,false),(20,true),(67,false),(68,false),(69,true),(70,false),(71,true),(92,false)]
theorem inputList6570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6570 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6570 (by decide) v hb
mask_input "6570|4951761780457251385850724352|2951479051793529307136"
def inputClause6571 : CNF.NClause := [(51,false),(20,false),(67,true),(68,false),(69,true),(70,false),(71,true),(92,false)]
theorem inputList6571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6571 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6571 (by decide) v hb
mask_input "6571|4951761632883298796175360000|3099053004383204671488"
def inputClause6572 : CNF.NClause := [(51,false),(20,true),(67,true),(68,false),(69,true),(70,false),(71,true),(92,false)]
theorem inputList6572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6572 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6572 (by decide) v hb
mask_input "6572|4951761632883298796174311424|3099053004383205720064"
def inputClause6573 : CNF.NClause := [(51,false),(20,false),(67,false),(68,true),(69,true),(70,false),(71,true),(92,false)]
theorem inputList6573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6573 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6573 (by decide) v hb
mask_input "6573|4951761485309346206498947072|3246626956972881084416"
def inputClause6574 : CNF.NClause := [(51,false),(20,true),(67,false),(68,true),(69,true),(70,false),(71,true),(92,false)]
theorem inputList6574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6574 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6574 (by decide) v hb
mask_input "6574|4951761485309346206497898496|3246626956972882132992"
def inputClause6575 : CNF.NClause := [(51,false),(20,false),(67,true),(68,true),(69,true),(70,false),(71,true),(92,false)]
theorem inputList6575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6575 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6575 (by decide) v hb
mask_input "6575|4951761337735393616822534144|3394200909562557497344"
def inputClause6576 : CNF.NClause := [(51,false),(20,true),(67,true),(68,true),(69,true),(70,false),(71,true),(92,false)]
theorem inputList6576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6576 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6576 (by decide) v hb
mask_input "6576|4951761337735393616821485568|3394200909562558545920"
def inputClause6577 : CNF.NClause := [(51,false),(20,false),(67,false),(68,false),(69,false),(70,true),(71,true),(92,false)]
theorem inputList6577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6577 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6577 (by decide) v hb
mask_input "6577|4951761190161441027146121216|3541774862152233910272"
def inputClause6578 : CNF.NClause := [(51,false),(20,true),(67,false),(68,false),(69,false),(70,true),(71,true),(92,false)]
theorem inputList6578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6578 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6578 (by decide) v hb
mask_input "6578|4951761190161441027145072640|3541774862152234958848"
def inputClause6579 : CNF.NClause := [(51,false),(20,false),(67,true),(68,false),(69,false),(70,true),(71,true),(92,false)]
theorem inputList6579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6579 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6579 (by decide) v hb
mask_input "6579|4951761042587488437469708288|3689348814741910323200"
def inputClause6580 : CNF.NClause := [(51,false),(20,true),(67,true),(68,false),(69,false),(70,true),(71,true),(92,false)]
theorem inputList6580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6580 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6580 (by decide) v hb
mask_input "6580|4951761042587488437468659712|3689348814741911371776"
def inputClause6581 : CNF.NClause := [(51,false),(20,false),(67,false),(68,true),(69,false),(70,true),(71,true),(92,false)]
theorem inputList6581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6581 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6581 (by decide) v hb
mask_input "6581|4951760895013535847793295360|3836922767331586736128"
def inputClause6582 : CNF.NClause := [(51,false),(20,true),(67,false),(68,true),(69,false),(70,true),(71,true),(92,false)]
theorem inputList6582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6582 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6582 (by decide) v hb
mask_input "6582|4951760895013535847792246784|3836922767331587784704"
def inputClause6583 : CNF.NClause := [(51,false),(20,false),(67,true),(68,true),(69,false),(70,true),(71,true),(92,false)]
theorem inputList6583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6583 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6583 (by decide) v hb
mask_input "6583|4951760747439583258116882432|3984496719921263149056"
def inputClause6584 : CNF.NClause := [(51,false),(20,true),(67,true),(68,true),(69,false),(70,true),(71,true),(92,false)]
theorem inputList6584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6584 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6584 (by decide) v hb
mask_input "6584|4951760747439583258115833856|3984496719921264197632"
def inputClause6585 : CNF.NClause := [(51,false),(20,false),(67,false),(68,false),(69,true),(70,true),(71,true),(92,false)]
theorem inputList6585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6585 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6585 (by decide) v hb
mask_input "6585|4951760599865630668440469504|4132070672510939561984"
def inputClause6586 : CNF.NClause := [(51,false),(20,true),(67,false),(68,false),(69,true),(70,true),(71,true),(92,false)]
theorem inputList6586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6586 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6586 (by decide) v hb
mask_input "6586|4951760599865630668439420928|4132070672510940610560"
def inputClause6587 : CNF.NClause := [(51,false),(20,false),(67,true),(68,false),(69,true),(70,true),(71,true),(92,false)]
theorem inputList6587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6587 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6587 (by decide) v hb
mask_input "6587|4951760452291678078764056576|4279644625100615974912"
def inputClause6588 : CNF.NClause := [(51,false),(20,true),(67,true),(68,false),(69,true),(70,true),(71,true),(92,false)]
theorem inputList6588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6588 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6588 (by decide) v hb
mask_input "6588|4951760452291678078763008000|4279644625100617023488"
def inputClause6589 : CNF.NClause := [(51,false),(20,false),(67,false),(68,true),(69,true),(70,true),(71,true),(92,false)]
theorem inputList6589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6589 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6589 (by decide) v hb
mask_input "6589|4951760304717725489087643648|4427218577690292387840"
def inputClause6590 : CNF.NClause := [(51,false),(20,true),(67,false),(68,true),(69,true),(70,true),(71,true),(92,false)]
theorem inputList6590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6590 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6590 (by decide) v hb
mask_input "6590|4951760304717725489086595072|4427218577690293436416"
def inputClause6591 : CNF.NClause := [(51,false),(20,false),(67,true),(68,true),(69,true),(70,true),(71,true),(92,false)]
theorem inputList6591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6591 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6591 (by decide) v hb
mask_input "6591|4951760157143772899411230720|4574792530279968800768"
def inputClause6592 : CNF.NClause := [(51,false),(20,true),(67,true),(68,true),(69,true),(70,true),(71,true),(92,false)]
theorem inputList6592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6592 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6592 (by decide) v hb
mask_input "6592|4951760157143772899410182144|4574792530279969849344"
def inputClause6593 : CNF.NClause := [(51,false),(20,false),(67,false),(68,false),(69,false),(70,false),(71,false),(92,true)]
theorem inputList6593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6593 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6593 (by decide) v hb
mask_input "6593|4574794782079783534592|4951760157141521099596496896"
def inputClause6594 : CNF.NClause := [(51,false),(20,true),(67,false),(68,false),(69,false),(70,false),(71,false),(92,true)]
theorem inputList6594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6594 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6594 (by decide) v hb
mask_input "6594|4574794782079782486016|4951760157141521099597545472"
def inputClause6595 : CNF.NClause := [(51,false),(20,false),(67,true),(68,false),(69,false),(70,false),(71,false),(92,true)]
theorem inputList6595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6595 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6595 (by decide) v hb
mask_input "6595|4427220829490107121664|4951760304715473689272909824"
def inputClause6596 : CNF.NClause := [(51,false),(20,true),(67,true),(68,false),(69,false),(70,false),(71,false),(92,true)]
theorem inputList6596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6596 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6596 (by decide) v hb
mask_input "6596|4427220829490106073088|4951760304715473689273958400"
end Percolation.MaskChain
