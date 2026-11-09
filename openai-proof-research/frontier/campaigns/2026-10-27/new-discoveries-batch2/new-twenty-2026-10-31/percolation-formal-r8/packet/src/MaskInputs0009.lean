import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause588 : CNF.NClause := [(71,true),(1,true),(7,true),(13,false),(19,true),(20,false),(26,false)]
theorem inputList588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause588 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause588 (by decide) v hb
mask_input "588|68165632|2361183241434823131266"
def inputClause589 : CNF.NClause := [(71,true),(1,false),(7,false),(13,true),(19,true),(20,false),(26,false)]
theorem inputList589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause589 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause589 (by decide) v hb
mask_input "589|68157570|2361183241434823139328"
def inputClause590 : CNF.NClause := [(71,true),(1,true),(7,false),(13,true),(19,true),(20,false),(26,false)]
theorem inputList590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause590 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause590 (by decide) v hb
mask_input "590|68157568|2361183241434823139330"
def inputClause591 : CNF.NClause := [(71,true),(1,false),(7,true),(13,true),(19,true),(20,false),(26,false)]
theorem inputList591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause591 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause591 (by decide) v hb
mask_input "591|68157442|2361183241434823139456"
def inputClause592 : CNF.NClause := [(71,true),(1,true),(7,true),(13,true),(19,true),(20,false),(26,false)]
theorem inputList592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause592 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause592 (by decide) v hb
mask_input "592|68157440|2361183241434823139458"
def inputClause593 : CNF.NClause := [(71,true),(1,false),(7,false),(13,false),(19,false),(20,true),(26,false)]
theorem inputList593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause593 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause593 (by decide) v hb
mask_input "593|67641474|2361183241434823655424"
def inputClause594 : CNF.NClause := [(71,true),(1,true),(7,false),(13,false),(19,false),(20,true),(26,false)]
theorem inputList594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause594 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause594 (by decide) v hb
mask_input "594|67641472|2361183241434823655426"
def inputClause595 : CNF.NClause := [(71,true),(1,false),(7,true),(13,false),(19,false),(20,true),(26,false)]
theorem inputList595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause595 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause595 (by decide) v hb
mask_input "595|67641346|2361183241434823655552"
def inputClause596 : CNF.NClause := [(71,true),(1,true),(7,true),(13,false),(19,false),(20,true),(26,false)]
theorem inputList596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause596 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause596 (by decide) v hb
mask_input "596|67641344|2361183241434823655554"
def inputClause597 : CNF.NClause := [(71,true),(1,false),(7,false),(13,true),(19,false),(20,true),(26,false)]
theorem inputList597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause597 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause597 (by decide) v hb
mask_input "597|67633282|2361183241434823663616"
def inputClause598 : CNF.NClause := [(71,true),(1,true),(7,false),(13,true),(19,false),(20,true),(26,false)]
theorem inputList598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause598 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause598 (by decide) v hb
mask_input "598|67633280|2361183241434823663618"
def inputClause599 : CNF.NClause := [(71,true),(1,false),(7,true),(13,true),(19,false),(20,true),(26,false)]
theorem inputList599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause599 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause599 (by decide) v hb
mask_input "599|67633154|2361183241434823663744"
def inputClause600 : CNF.NClause := [(71,true),(1,true),(7,true),(13,true),(19,false),(20,true),(26,false)]
theorem inputList600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause600 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause600 (by decide) v hb
mask_input "600|67633152|2361183241434823663746"
def inputClause601 : CNF.NClause := [(71,true),(1,false),(7,false),(13,false),(19,true),(20,true),(26,false)]
theorem inputList601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause601 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause601 (by decide) v hb
mask_input "601|67117186|2361183241434824179712"
def inputClause602 : CNF.NClause := [(71,true),(1,true),(7,false),(13,false),(19,true),(20,true),(26,false)]
theorem inputList602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause602 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause602 (by decide) v hb
mask_input "602|67117184|2361183241434824179714"
def inputClause603 : CNF.NClause := [(71,true),(1,false),(7,true),(13,false),(19,true),(20,true),(26,false)]
theorem inputList603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause603 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause603 (by decide) v hb
mask_input "603|67117058|2361183241434824179840"
def inputClause604 : CNF.NClause := [(71,true),(1,true),(7,true),(13,false),(19,true),(20,true),(26,false)]
theorem inputList604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause604 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause604 (by decide) v hb
mask_input "604|67117056|2361183241434824179842"
def inputClause605 : CNF.NClause := [(71,true),(1,false),(7,false),(13,true),(19,true),(20,true),(26,false)]
theorem inputList605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause605 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause605 (by decide) v hb
mask_input "605|67108994|2361183241434824187904"
def inputClause606 : CNF.NClause := [(71,true),(1,true),(7,false),(13,true),(19,true),(20,true),(26,false)]
theorem inputList606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause606 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause606 (by decide) v hb
mask_input "606|67108992|2361183241434824187906"
def inputClause607 : CNF.NClause := [(71,true),(1,false),(7,true),(13,true),(19,true),(20,true),(26,false)]
theorem inputList607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause607 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause607 (by decide) v hb
mask_input "607|67108866|2361183241434824188032"
def inputClause608 : CNF.NClause := [(71,false),(1,true),(7,true),(13,true),(19,true),(20,true),(26,false)]
theorem inputList608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause608 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause608 (by decide) v hb
mask_input "608|2361183241434889715712|1581186"
def inputClause609 : CNF.NClause := [(71,true),(1,false),(7,false),(13,false),(19,false),(20,false),(26,true)]
theorem inputList609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause609 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause609 (by decide) v hb
mask_input "609|1581186|2361183241434889715712"
def inputClause610 : CNF.NClause := [(71,true),(1,true),(7,false),(13,false),(19,false),(20,false),(26,true)]
theorem inputList610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause610 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause610 (by decide) v hb
mask_input "610|1581184|2361183241434889715714"
def inputClause611 : CNF.NClause := [(71,true),(1,false),(7,true),(13,false),(19,false),(20,false),(26,true)]
theorem inputList611 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause611 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause611 (by decide) v hb
mask_input "611|1581058|2361183241434889715840"
def inputClause612 : CNF.NClause := [(71,true),(1,true),(7,true),(13,false),(19,false),(20,false),(26,true)]
theorem inputList612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause612 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause612 (by decide) v hb
mask_input "612|1581056|2361183241434889715842"
def inputClause613 : CNF.NClause := [(71,true),(1,false),(7,false),(13,true),(19,false),(20,false),(26,true)]
theorem inputList613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause613 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause613 (by decide) v hb
mask_input "613|1572994|2361183241434889723904"
def inputClause614 : CNF.NClause := [(71,true),(1,true),(7,false),(13,true),(19,false),(20,false),(26,true)]
theorem inputList614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause614 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause614 (by decide) v hb
mask_input "614|1572992|2361183241434889723906"
def inputClause615 : CNF.NClause := [(71,true),(1,false),(7,true),(13,true),(19,false),(20,false),(26,true)]
theorem inputList615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause615 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause615 (by decide) v hb
mask_input "615|1572866|2361183241434889724032"
def inputClause616 : CNF.NClause := [(71,true),(1,true),(7,true),(13,true),(19,false),(20,false),(26,true)]
theorem inputList616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause616 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause616 (by decide) v hb
mask_input "616|1572864|2361183241434889724034"
def inputClause617 : CNF.NClause := [(71,true),(1,false),(7,false),(13,false),(19,true),(20,false),(26,true)]
theorem inputList617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause617 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause617 (by decide) v hb
mask_input "617|1056898|2361183241434890240000"
def inputClause618 : CNF.NClause := [(71,true),(1,true),(7,false),(13,false),(19,true),(20,false),(26,true)]
theorem inputList618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause618 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause618 (by decide) v hb
mask_input "618|1056896|2361183241434890240002"
def inputClause619 : CNF.NClause := [(71,true),(1,false),(7,true),(13,false),(19,true),(20,false),(26,true)]
theorem inputList619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause619 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause619 (by decide) v hb
mask_input "619|1056770|2361183241434890240128"
def inputClause620 : CNF.NClause := [(71,true),(1,true),(7,true),(13,false),(19,true),(20,false),(26,true)]
theorem inputList620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause620 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause620 (by decide) v hb
mask_input "620|1056768|2361183241434890240130"
def inputClause621 : CNF.NClause := [(71,true),(1,false),(7,false),(13,true),(19,true),(20,false),(26,true)]
theorem inputList621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause621 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause621 (by decide) v hb
mask_input "621|1048706|2361183241434890248192"
def inputClause622 : CNF.NClause := [(71,true),(1,true),(7,false),(13,true),(19,true),(20,false),(26,true)]
theorem inputList622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause622 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause622 (by decide) v hb
mask_input "622|1048704|2361183241434890248194"
def inputClause623 : CNF.NClause := [(71,true),(1,false),(7,true),(13,true),(19,true),(20,false),(26,true)]
theorem inputList623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause623 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause623 (by decide) v hb
mask_input "623|1048578|2361183241434890248320"
def inputClause625 : CNF.NClause := [(71,true),(1,false),(7,false),(13,false),(19,false),(20,true),(26,true)]
theorem inputList625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause625 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause625 (by decide) v hb
mask_input "625|532610|2361183241434890764288"
def inputClause626 : CNF.NClause := [(71,true),(1,true),(7,false),(13,false),(19,false),(20,true),(26,true)]
theorem inputList626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause626 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause626 (by decide) v hb
mask_input "626|532608|2361183241434890764290"
def inputClause627 : CNF.NClause := [(71,true),(1,false),(7,true),(13,false),(19,false),(20,true),(26,true)]
theorem inputList627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause627 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause627 (by decide) v hb
mask_input "627|532482|2361183241434890764416"
def inputClause628 : CNF.NClause := [(71,true),(1,true),(7,true),(13,false),(19,false),(20,true),(26,true)]
theorem inputList628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause628 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause628 (by decide) v hb
mask_input "628|532480|2361183241434890764418"
end Percolation.MaskChain
