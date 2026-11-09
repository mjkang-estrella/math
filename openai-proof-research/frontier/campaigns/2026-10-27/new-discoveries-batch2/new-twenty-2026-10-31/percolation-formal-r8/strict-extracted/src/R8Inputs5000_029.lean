import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause5604 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(72,false),(81,false),(85,true),(91,true)]
theorem inputList5604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5604 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5604 (by decide) v hb
mask_input "5604|2422869153626103440474112|2514565723245172757098401792"
def inputClause5605 : CNF.NClause := [(43,false),(12,false),(64,false),(68,true),(72,false),(81,false),(85,true),(91,true)]
theorem inputList5605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5605 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5605 (by decide) v hb
mask_input "5605|2422592452464997797203968|2514565999946333862741671936"
def inputClause5606 : CNF.NClause := [(43,false),(12,true),(64,false),(68,true),(72,false),(81,false),(85,true),(91,true)]
theorem inputList5606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5606 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5606 (by decide) v hb
mask_input "5606|2422592452464997797199872|2514565999946333862741676032"
def inputClause5607 : CNF.NClause := [(43,false),(12,false),(64,true),(68,true),(72,false),(81,false),(85,true),(91,true)]
theorem inputList5607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5607 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5607 (by decide) v hb
mask_input "5607|2422574005720924087652352|2514566018393077936451223552"
def inputClause5608 : CNF.NClause := [(43,false),(12,true),(64,true),(68,true),(72,false),(81,false),(85,true),(91,true)]
theorem inputList5608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5608 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5608 (by decide) v hb
mask_input "5608|2422574005720924087648256|2514566018393077936451227648"
def inputClause5609 : CNF.NClause := [(43,false),(12,false),(64,false),(68,false),(72,true),(81,false),(85,true),(91,true)]
theorem inputList5609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5609 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5609 (by decide) v hb
mask_input "5609|2418165233887307504816128|2514570427164911553034059776"
def inputClause5610 : CNF.NClause := [(43,false),(12,true),(64,false),(68,false),(72,true),(81,false),(85,true),(91,true)]
theorem inputList5610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5610 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5610 (by decide) v hb
mask_input "5610|2418165233887307504812032|2514570427164911553034063872"
def inputClause5612 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(72,true),(81,false),(85,true),(91,true)]
theorem inputList5612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5612 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5612 (by decide) v hb
mask_input "5612|2418146787143233795260416|2514570445611655626743615488"
def inputClause5613 : CNF.NClause := [(43,false),(12,false),(64,false),(68,true),(72,true),(81,false),(85,true),(91,true)]
theorem inputList5613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5613 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5613 (by decide) v hb
mask_input "5613|2417870085982128151990272|2514570722312816732386885632"
def inputClause5614 : CNF.NClause := [(43,false),(12,true),(64,false),(68,true),(72,true),(81,false),(85,true),(91,true)]
theorem inputList5614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5614 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5614 (by decide) v hb
mask_input "5614|2417870085982128151986176|2514570722312816732386889728"
def inputClause5615 : CNF.NClause := [(43,false),(12,false),(64,true),(68,true),(72,true),(81,false),(85,true),(91,true)]
theorem inputList5615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5615 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5615 (by decide) v hb
mask_input "5615|2417851639238054442438656|2514570740759560806096437248"
def inputClause5616 : CNF.NClause := [(43,false),(12,true),(64,true),(68,true),(72,true),(81,false),(85,true),(91,true)]
theorem inputList5616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5616 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5616 (by decide) v hb
mask_input "5616|2417851639238054442434560|2514570740759560806096441344"
def inputClause5617 : CNF.NClause := [(43,false),(12,false),(64,false),(68,false),(72,false),(81,true),(85,true),(91,true)]
theorem inputList5617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5617 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5617 (by decide) v hb
mask_input "5617|5035961140918800617472|2516983556437657941738258432"
def inputClause5618 : CNF.NClause := [(43,false),(12,true),(64,false),(68,false),(72,false),(81,true),(85,true),(91,true)]
theorem inputList5618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5618 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5618 (by decide) v hb
mask_input "5618|5035961140918800613376|2516983556437657941738262528"
def inputClause5619 : CNF.NClause := [(43,false),(12,false),(64,true),(68,false),(72,false),(81,true),(85,true),(91,true)]
theorem inputList5619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5619 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5619 (by decide) v hb
mask_input "5619|5017514396845091065856|2516983574884402015447810048"
def inputClause5620 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(72,false),(81,true),(85,true),(91,true)]
theorem inputList5620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5620 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5620 (by decide) v hb
mask_input "5620|5017514396845091061760|2516983574884402015447814144"
def inputClause5621 : CNF.NClause := [(43,false),(12,false),(64,false),(68,true),(72,false),(81,true),(85,true),(91,true)]
theorem inputList5621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5621 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5621 (by decide) v hb
mask_input "5621|4740813235739447791616|2516983851585563121091084288"
def inputClause5622 : CNF.NClause := [(43,false),(12,true),(64,false),(68,true),(72,false),(81,true),(85,true),(91,true)]
theorem inputList5622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5622 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5622 (by decide) v hb
mask_input "5622|4740813235739447787520|2516983851585563121091088384"
def inputClause5623 : CNF.NClause := [(43,false),(12,false),(64,true),(68,true),(72,false),(81,true),(85,true),(91,true)]
theorem inputList5623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5623 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5623 (by decide) v hb
mask_input "5623|4722366491665738240000|2516983870032307194800635904"
def inputClause5624 : CNF.NClause := [(43,false),(12,true),(64,true),(68,true),(72,false),(81,true),(85,true),(91,true)]
theorem inputList5624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5624 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5624 (by decide) v hb
mask_input "5624|4722366491665738235904|2516983870032307194800640000"
def inputClause5626 : CNF.NClause := [(43,false),(12,true),(64,false),(68,false),(72,true),(81,true),(85,true),(91,true)]
theorem inputList5626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5626 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5626 (by decide) v hb
mask_input "5626|313594658049155399680|2516988278804140811383476224"
def inputClause5628 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(72,true),(81,true),(85,true),(91,true)]
theorem inputList5628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5628 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5628 (by decide) v hb
mask_input "5628|295147913975445848064|2516988297250884885093027840"
def inputClause5629 : CNF.NClause := [(43,false),(12,false),(64,false),(68,true),(72,true),(81,true),(85,true),(91,true)]
theorem inputList5629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5629 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5629 (by decide) v hb
mask_input "5629|18446752869802577920|2516988573952045990736297984"
def inputClause5630 : CNF.NClause := [(43,false),(12,true),(64,false),(68,true),(72,true),(81,true),(85,true),(91,true)]
theorem inputList5630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5630 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5630 (by decide) v hb
mask_input "5630|18446752869802573824|2516988573952045990736302080"
def inputClause5632 : CNF.NClause := [(43,false),(12,true),(64,true),(68,true),(72,true),(81,true),(85,true),(91,true)]
theorem inputList5632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5632 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 12) (spread_mem 12) inputClause5632 (by decide) v hb
mask_input "5632|8796093022208|2516988592398790064445853696"
def inputClause5633 : CNF.NClause := [(44,true),(13,false),(65,false),(71,false),(72,false),(78,false),(84,false),(88,false)]
theorem inputList5633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5633 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5633 (by decide) v hb
mask_input "5633|329137174833295244700688384|17592186044416"
def inputClause5635 : CNF.NClause := [(44,false),(13,false),(65,true),(71,false),(72,false),(78,false),(84,false),(88,false)]
theorem inputList5635 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5635 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5635 (by decide) v hb
mask_input "5635|329137137939824689467629568|36893488147419103232"
def inputClause5636 : CNF.NClause := [(44,false),(13,true),(65,true),(71,false),(72,false),(78,false),(84,false),(88,false)]
theorem inputList5636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5636 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5636 (by decide) v hb
mask_input "5636|329137137939824689467621376|36893488147419111424"
def inputClause5637 : CNF.NClause := [(44,false),(13,false),(65,false),(71,true),(72,false),(78,false),(84,false),(88,false)]
theorem inputList5637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5637 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5637 (by decide) v hb
mask_input "5637|329134813650071402064125952|2361183241434822606848"
def inputClause5638 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,false),(78,false),(84,false),(88,false)]
theorem inputList5638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5638 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5638 (by decide) v hb
mask_input "5638|329134813650071402064117760|2361183241434822615040"
def inputClause5639 : CNF.NClause := [(44,false),(13,false),(65,true),(71,true),(72,false),(78,false),(84,false),(88,false)]
theorem inputList5639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5639 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5639 (by decide) v hb
mask_input "5639|329134776756583254645022720|2398076729582241710080"
def inputClause5640 : CNF.NClause := [(44,false),(13,true),(65,true),(71,true),(72,false),(78,false),(84,false),(88,false)]
theorem inputList5640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5640 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5640 (by decide) v hb
mask_input "5640|329134776756583254645014528|2398076729582241718272"
def inputClause5641 : CNF.NClause := [(44,false),(13,false),(65,false),(71,false),(72,true),(78,false),(84,false),(88,false)]
theorem inputList5641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5641 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5641 (by decide) v hb
mask_input "5641|329132452466829967241519104|4722366482869645213696"
def inputClause5642 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,true),(78,false),(84,false),(88,false)]
theorem inputList5642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5642 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5642 (by decide) v hb
mask_input "5642|329132452466829967241510912|4722366482869645221888"
def inputClause5643 : CNF.NClause := [(44,false),(13,false),(65,true),(71,false),(72,true),(78,false),(84,false),(88,false)]
theorem inputList5643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5643 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5643 (by decide) v hb
mask_input "5643|329132415573341819822415872|4759259971017064316928"
def inputClause5644 : CNF.NClause := [(44,false),(13,true),(65,true),(71,false),(72,true),(78,false),(84,false),(88,false)]
theorem inputList5644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5644 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5644 (by decide) v hb
mask_input "5644|329132415573341819822407680|4759259971017064325120"
def inputClause5645 : CNF.NClause := [(44,false),(13,false),(65,false),(71,true),(72,true),(78,false),(84,false),(88,false)]
theorem inputList5645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5645 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5645 (by decide) v hb
mask_input "5645|329130091283588532418912256|7083549724304467820544"
def inputClause5646 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,true),(78,false),(84,false),(88,false)]
theorem inputList5646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5646 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5646 (by decide) v hb
mask_input "5646|329130091283588532418904064|7083549724304467828736"
def inputClause5647 : CNF.NClause := [(44,false),(13,false),(65,true),(71,true),(72,true),(78,false),(84,false),(88,false)]
theorem inputList5647 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5647 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5647 (by decide) v hb
mask_input "5647|329130054390100384999809024|7120443212451886923776"
def inputClause5648 : CNF.NClause := [(44,false),(13,true),(65,true),(71,true),(72,true),(78,false),(84,false),(88,false)]
theorem inputList5648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5648 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5648 (by decide) v hb
mask_input "5648|329130054390100384999800832|7120443212451886931968"
end Percolation.MaskChain
