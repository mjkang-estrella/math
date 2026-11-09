import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause541 : CNF.NClause := [(70,true),(3,false),(6,false),(14,true),(17,true),(20,true),(28,false)]
theorem inputList541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause541 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause541 (by decide) v hb
mask_input "541|268435528|1180591620717412499456"
def inputClause542 : CNF.NClause := [(70,true),(3,true),(6,false),(14,true),(17,true),(20,true),(28,false)]
theorem inputList542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause542 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause542 (by decide) v hb
mask_input "542|268435520|1180591620717412499464"
def inputClause543 : CNF.NClause := [(70,true),(3,false),(6,true),(14,true),(17,true),(20,true),(28,false)]
theorem inputList543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause543 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause543 (by decide) v hb
mask_input "543|268435464|1180591620717412499520"
def inputClause545 : CNF.NClause := [(70,true),(3,false),(6,false),(14,false),(17,false),(20,false),(28,true)]
theorem inputList545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause545 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause545 (by decide) v hb
mask_input "545|1196104|1180591620717679738880"
def inputClause546 : CNF.NClause := [(70,true),(3,true),(6,false),(14,false),(17,false),(20,false),(28,true)]
theorem inputList546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause546 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause546 (by decide) v hb
mask_input "546|1196096|1180591620717679738888"
def inputClause547 : CNF.NClause := [(70,true),(3,false),(6,true),(14,false),(17,false),(20,false),(28,true)]
theorem inputList547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause547 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause547 (by decide) v hb
mask_input "547|1196040|1180591620717679738944"
def inputClause548 : CNF.NClause := [(70,true),(3,true),(6,true),(14,false),(17,false),(20,false),(28,true)]
theorem inputList548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause548 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause548 (by decide) v hb
mask_input "548|1196032|1180591620717679738952"
def inputClause549 : CNF.NClause := [(70,true),(3,false),(6,false),(14,true),(17,false),(20,false),(28,true)]
theorem inputList549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause549 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause549 (by decide) v hb
mask_input "549|1179720|1180591620717679755264"
def inputClause550 : CNF.NClause := [(70,true),(3,true),(6,false),(14,true),(17,false),(20,false),(28,true)]
theorem inputList550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause550 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause550 (by decide) v hb
mask_input "550|1179712|1180591620717679755272"
def inputClause551 : CNF.NClause := [(70,true),(3,false),(6,true),(14,true),(17,false),(20,false),(28,true)]
theorem inputList551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause551 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause551 (by decide) v hb
mask_input "551|1179656|1180591620717679755328"
def inputClause552 : CNF.NClause := [(70,true),(3,true),(6,true),(14,true),(17,false),(20,false),(28,true)]
theorem inputList552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause552 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause552 (by decide) v hb
mask_input "552|1179648|1180591620717679755336"
def inputClause553 : CNF.NClause := [(70,true),(3,false),(6,false),(14,false),(17,true),(20,false),(28,true)]
theorem inputList553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause553 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause553 (by decide) v hb
mask_input "553|1065032|1180591620717679869952"
def inputClause554 : CNF.NClause := [(70,true),(3,true),(6,false),(14,false),(17,true),(20,false),(28,true)]
theorem inputList554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause554 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause554 (by decide) v hb
mask_input "554|1065024|1180591620717679869960"
def inputClause555 : CNF.NClause := [(70,true),(3,false),(6,true),(14,false),(17,true),(20,false),(28,true)]
theorem inputList555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause555 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause555 (by decide) v hb
mask_input "555|1064968|1180591620717679870016"
def inputClause556 : CNF.NClause := [(70,true),(3,true),(6,true),(14,false),(17,true),(20,false),(28,true)]
theorem inputList556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause556 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause556 (by decide) v hb
mask_input "556|1064960|1180591620717679870024"
def inputClause557 : CNF.NClause := [(70,true),(3,false),(6,false),(14,true),(17,true),(20,false),(28,true)]
theorem inputList557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause557 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause557 (by decide) v hb
mask_input "557|1048648|1180591620717679886336"
def inputClause558 : CNF.NClause := [(70,true),(3,true),(6,false),(14,true),(17,true),(20,false),(28,true)]
theorem inputList558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause558 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause558 (by decide) v hb
mask_input "558|1048640|1180591620717679886344"
def inputClause559 : CNF.NClause := [(70,true),(3,false),(6,true),(14,true),(17,true),(20,false),(28,true)]
theorem inputList559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause559 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause559 (by decide) v hb
mask_input "559|1048584|1180591620717679886400"
def inputClause561 : CNF.NClause := [(70,true),(3,false),(6,false),(14,false),(17,false),(20,true),(28,true)]
theorem inputList561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause561 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause561 (by decide) v hb
mask_input "561|147528|1180591620717680787456"
def inputClause562 : CNF.NClause := [(70,true),(3,true),(6,false),(14,false),(17,false),(20,true),(28,true)]
theorem inputList562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause562 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause562 (by decide) v hb
mask_input "562|147520|1180591620717680787464"
def inputClause563 : CNF.NClause := [(70,true),(3,false),(6,true),(14,false),(17,false),(20,true),(28,true)]
theorem inputList563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause563 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause563 (by decide) v hb
mask_input "563|147464|1180591620717680787520"
def inputClause564 : CNF.NClause := [(70,true),(3,true),(6,true),(14,false),(17,false),(20,true),(28,true)]
theorem inputList564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause564 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause564 (by decide) v hb
mask_input "564|147456|1180591620717680787528"
def inputClause565 : CNF.NClause := [(70,true),(3,false),(6,false),(14,true),(17,false),(20,true),(28,true)]
theorem inputList565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause565 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause565 (by decide) v hb
mask_input "565|131144|1180591620717680803840"
def inputClause566 : CNF.NClause := [(70,true),(3,true),(6,false),(14,true),(17,false),(20,true),(28,true)]
theorem inputList566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause566 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause566 (by decide) v hb
mask_input "566|131136|1180591620717680803848"
def inputClause567 : CNF.NClause := [(70,true),(3,false),(6,true),(14,true),(17,false),(20,true),(28,true)]
theorem inputList567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause567 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause567 (by decide) v hb
mask_input "567|131080|1180591620717680803904"
def inputClause569 : CNF.NClause := [(70,true),(3,false),(6,false),(14,false),(17,true),(20,true),(28,true)]
theorem inputList569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause569 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause569 (by decide) v hb
mask_input "569|16456|1180591620717680918528"
def inputClause570 : CNF.NClause := [(70,true),(3,true),(6,false),(14,false),(17,true),(20,true),(28,true)]
theorem inputList570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause570 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause570 (by decide) v hb
mask_input "570|16448|1180591620717680918536"
def inputClause571 : CNF.NClause := [(70,true),(3,false),(6,true),(14,false),(17,true),(20,true),(28,true)]
theorem inputList571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause571 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause571 (by decide) v hb
mask_input "571|16392|1180591620717680918592"
def inputClause573 : CNF.NClause := [(70,true),(3,false),(6,false),(14,true),(17,true),(20,true),(28,true)]
theorem inputList573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause573 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 8) 8) (activationA_mem 8) inputClause573 (by decide) v hb
mask_input "573|72|1180591620717680934912"
def inputClause577 : CNF.NClause := [(71,true),(1,false),(7,false),(13,false),(19,false),(20,false),(26,false)]
theorem inputList577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause577 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause577 (by decide) v hb
mask_input "577|68690050|2361183241434822606848"
def inputClause578 : CNF.NClause := [(71,true),(1,true),(7,false),(13,false),(19,false),(20,false),(26,false)]
theorem inputList578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause578 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause578 (by decide) v hb
mask_input "578|68690048|2361183241434822606850"
def inputClause579 : CNF.NClause := [(71,true),(1,false),(7,true),(13,false),(19,false),(20,false),(26,false)]
theorem inputList579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause579 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause579 (by decide) v hb
mask_input "579|68689922|2361183241434822606976"
def inputClause580 : CNF.NClause := [(71,true),(1,true),(7,true),(13,false),(19,false),(20,false),(26,false)]
theorem inputList580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause580 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause580 (by decide) v hb
mask_input "580|68689920|2361183241434822606978"
def inputClause581 : CNF.NClause := [(71,true),(1,false),(7,false),(13,true),(19,false),(20,false),(26,false)]
theorem inputList581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause581 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause581 (by decide) v hb
mask_input "581|68681858|2361183241434822615040"
def inputClause582 : CNF.NClause := [(71,true),(1,true),(7,false),(13,true),(19,false),(20,false),(26,false)]
theorem inputList582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause582 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause582 (by decide) v hb
mask_input "582|68681856|2361183241434822615042"
def inputClause583 : CNF.NClause := [(71,true),(1,false),(7,true),(13,true),(19,false),(20,false),(26,false)]
theorem inputList583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause583 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause583 (by decide) v hb
mask_input "583|68681730|2361183241434822615168"
def inputClause584 : CNF.NClause := [(71,true),(1,true),(7,true),(13,true),(19,false),(20,false),(26,false)]
theorem inputList584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause584 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause584 (by decide) v hb
mask_input "584|68681728|2361183241434822615170"
def inputClause585 : CNF.NClause := [(71,true),(1,false),(7,false),(13,false),(19,true),(20,false),(26,false)]
theorem inputList585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause585 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause585 (by decide) v hb
mask_input "585|68165762|2361183241434823131136"
def inputClause586 : CNF.NClause := [(71,true),(1,true),(7,false),(13,false),(19,true),(20,false),(26,false)]
theorem inputList586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause586 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause586 (by decide) v hb
mask_input "586|68165760|2361183241434823131138"
def inputClause587 : CNF.NClause := [(71,true),(1,false),(7,true),(13,false),(19,true),(20,false),(26,false)]
theorem inputList587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause587 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) inputClause587 (by decide) v hb
mask_input "587|68165634|2361183241434823131264"
end Percolation.MaskChain
