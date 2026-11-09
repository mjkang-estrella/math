import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause4632 : CNF.NClause := [(36,false),(5,true),(82,true),(83,true),(84,false),(85,true),(86,false),(92,false)]
theorem inputList4632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4632 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4632 (by decide) v hb
mask_input "4632|5048474222710691502292467712|53192736063043683687071776"
def inputClause4633 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(84,true),(85,true),(86,false),(92,false)]
theorem inputList4633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4633 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4633 (by decide) v hb
mask_input "4633|5043638519432232985593643040|58028439341502200385896448"
def inputClause4634 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,true),(85,true),(86,false),(92,false)]
theorem inputList4634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4634 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4634 (by decide) v hb
mask_input "4634|5043638519432232985593643008|58028439341502200385896480"
def inputClause4635 : CNF.NClause := [(36,false),(5,false),(82,true),(83,false),(84,true),(85,true),(86,false),(92,false)]
theorem inputList4635 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4635 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4635 (by decide) v hb
mask_input "4635|5038802816153774468894818336|62864142619960717084721152"
def inputClause4636 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,true),(85,true),(86,false),(92,false)]
theorem inputList4636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4636 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4636 (by decide) v hb
mask_input "4636|5038802816153774468894818304|62864142619960717084721184"
def inputClause4637 : CNF.NClause := [(36,false),(5,false),(82,false),(83,true),(84,true),(85,true),(86,false),(92,false)]
theorem inputList4637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4637 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4637 (by decide) v hb
mask_input "4637|5033967112875315952195993632|67699845898419233783545856"
def inputClause4638 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,true),(85,true),(86,false),(92,false)]
theorem inputList4638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4638 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4638 (by decide) v hb
mask_input "4638|5033967112875315952195993600|67699845898419233783545888"
def inputClause4639 : CNF.NClause := [(36,false),(5,false),(82,true),(83,true),(84,true),(85,true),(86,false),(92,false)]
theorem inputList4639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4639 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4639 (by decide) v hb
mask_input "4639|5029131409596857435497168928|72535549176877750482370560"
def inputClause4640 : CNF.NClause := [(36,false),(5,true),(82,true),(83,true),(84,true),(85,true),(86,false),(92,false)]
theorem inputList4640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4640 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4640 (by decide) v hb
mask_input "4640|5029131409596857435497168896|72535549176877750482370592"
def inputClause4641 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(84,false),(85,false),(86,true),(92,false)]
theorem inputList4641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4641 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4641 (by decide) v hb
mask_input "4641|5024295706318398918798344224|77371252455336267181195264"
def inputClause4642 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,false),(85,false),(86,true),(92,false)]
theorem inputList4642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4642 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4642 (by decide) v hb
mask_input "4642|5024295706318398918798344192|77371252455336267181195296"
def inputClause4643 : CNF.NClause := [(36,false),(5,false),(82,true),(83,false),(84,false),(85,false),(86,true),(92,false)]
theorem inputList4643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4643 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4643 (by decide) v hb
mask_input "4643|5019460003039940402099519520|82206955733794783880019968"
def inputClause4644 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,false),(85,false),(86,true),(92,false)]
theorem inputList4644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4644 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4644 (by decide) v hb
mask_input "4644|5019460003039940402099519488|82206955733794783880020000"
def inputClause4645 : CNF.NClause := [(36,false),(5,false),(82,false),(83,true),(84,false),(85,false),(86,true),(92,false)]
theorem inputList4645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4645 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4645 (by decide) v hb
mask_input "4645|5014624299761481885400694816|87042659012253300578844672"
def inputClause4646 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,false),(85,false),(86,true),(92,false)]
theorem inputList4646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4646 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4646 (by decide) v hb
mask_input "4646|5014624299761481885400694784|87042659012253300578844704"
def inputClause4647 : CNF.NClause := [(36,false),(5,false),(82,true),(83,true),(84,false),(85,false),(86,true),(92,false)]
theorem inputList4647 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4647 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4647 (by decide) v hb
mask_input "4647|5009788596483023368701870112|91878362290711817277669376"
def inputClause4648 : CNF.NClause := [(36,false),(5,true),(82,true),(83,true),(84,false),(85,false),(86,true),(92,false)]
theorem inputList4648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4648 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4648 (by decide) v hb
mask_input "4648|5009788596483023368701870080|91878362290711817277669408"
def inputClause4649 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(84,true),(85,false),(86,true),(92,false)]
theorem inputList4649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4649 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4649 (by decide) v hb
mask_input "4649|5004952893204564852003045408|96714065569170333976494080"
def inputClause4650 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,true),(85,false),(86,true),(92,false)]
theorem inputList4650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4650 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4650 (by decide) v hb
mask_input "4650|5004952893204564852003045376|96714065569170333976494112"
def inputClause4651 : CNF.NClause := [(36,false),(5,false),(82,true),(83,false),(84,true),(85,false),(86,true),(92,false)]
theorem inputList4651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4651 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4651 (by decide) v hb
mask_input "4651|5000117189926106335304220704|101549768847628850675318784"
def inputClause4652 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,true),(85,false),(86,true),(92,false)]
theorem inputList4652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4652 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4652 (by decide) v hb
mask_input "4652|5000117189926106335304220672|101549768847628850675318816"
def inputClause4653 : CNF.NClause := [(36,false),(5,false),(82,false),(83,true),(84,true),(85,false),(86,true),(92,false)]
theorem inputList4653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4653 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4653 (by decide) v hb
mask_input "4653|4995281486647647818605396000|106385472126087367374143488"
def inputClause4654 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,true),(85,false),(86,true),(92,false)]
theorem inputList4654 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4654 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4654 (by decide) v hb
mask_input "4654|4995281486647647818605395968|106385472126087367374143520"
def inputClause4655 : CNF.NClause := [(36,false),(5,false),(82,true),(83,true),(84,true),(85,false),(86,true),(92,false)]
theorem inputList4655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4655 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4655 (by decide) v hb
mask_input "4655|4990445783369189301906571296|111221175404545884072968192"
def inputClause4656 : CNF.NClause := [(36,false),(5,true),(82,true),(83,true),(84,true),(85,false),(86,true),(92,false)]
theorem inputList4656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4656 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4656 (by decide) v hb
mask_input "4656|4990445783369189301906571264|111221175404545884072968224"
def inputClause4657 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(84,false),(85,true),(86,true),(92,false)]
theorem inputList4657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4657 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4657 (by decide) v hb
mask_input "4657|4985610080090730785207746592|116056878683004400771792896"
def inputClause4658 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,false),(85,true),(86,true),(92,false)]
theorem inputList4658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4658 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4658 (by decide) v hb
mask_input "4658|4985610080090730785207746560|116056878683004400771792928"
def inputClause4659 : CNF.NClause := [(36,false),(5,false),(82,true),(83,false),(84,false),(85,true),(86,true),(92,false)]
theorem inputList4659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4659 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4659 (by decide) v hb
mask_input "4659|4980774376812272268508921888|120892581961462917470617600"
def inputClause4660 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,false),(85,true),(86,true),(92,false)]
theorem inputList4660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4660 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4660 (by decide) v hb
mask_input "4660|4980774376812272268508921856|120892581961462917470617632"
def inputClause4661 : CNF.NClause := [(36,false),(5,false),(82,false),(83,true),(84,false),(85,true),(86,true),(92,false)]
theorem inputList4661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4661 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4661 (by decide) v hb
mask_input "4661|4975938673533813751810097184|125728285239921434169442304"
def inputClause4662 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,false),(85,true),(86,true),(92,false)]
theorem inputList4662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4662 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4662 (by decide) v hb
mask_input "4662|4975938673533813751810097152|125728285239921434169442336"
def inputClause4663 : CNF.NClause := [(36,false),(5,false),(82,true),(83,true),(84,false),(85,true),(86,true),(92,false)]
theorem inputList4663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4663 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4663 (by decide) v hb
mask_input "4663|4971102970255355235111272480|130563988518379950868267008"
def inputClause4664 : CNF.NClause := [(36,false),(5,true),(82,true),(83,true),(84,false),(85,true),(86,true),(92,false)]
theorem inputList4664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4664 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4664 (by decide) v hb
mask_input "4664|4971102970255355235111272448|130563988518379950868267040"
def inputClause4665 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(84,true),(85,true),(86,true),(92,false)]
theorem inputList4665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4665 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4665 (by decide) v hb
mask_input "4665|4966267266976896718412447776|135399691796838467567091712"
def inputClause4666 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,true),(85,true),(86,true),(92,false)]
theorem inputList4666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4666 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4666 (by decide) v hb
mask_input "4666|4966267266976896718412447744|135399691796838467567091744"
def inputClause4667 : CNF.NClause := [(36,false),(5,false),(82,true),(83,false),(84,true),(85,true),(86,true),(92,false)]
theorem inputList4667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4667 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4667 (by decide) v hb
mask_input "4667|4961431563698438201713623072|140235395075296984265916416"
def inputClause4668 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,true),(85,true),(86,true),(92,false)]
theorem inputList4668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4668 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4668 (by decide) v hb
mask_input "4668|4961431563698438201713623040|140235395075296984265916448"
def inputClause4669 : CNF.NClause := [(36,false),(5,false),(82,false),(83,true),(84,true),(85,true),(86,true),(92,false)]
theorem inputList4669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4669 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4669 (by decide) v hb
mask_input "4669|4956595860419979685014798368|145071098353755500964741120"
def inputClause4670 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,true),(85,true),(86,true),(92,false)]
theorem inputList4670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4670 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4670 (by decide) v hb
mask_input "4670|4956595860419979685014798336|145071098353755500964741152"
def inputClause4671 : CNF.NClause := [(36,false),(5,false),(82,true),(83,true),(84,true),(85,true),(86,true),(92,false)]
theorem inputList4671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4671 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4671 (by decide) v hb
mask_input "4671|4951760157141521168315973664|149906801632214017663565824"
end Percolation.MaskChain
