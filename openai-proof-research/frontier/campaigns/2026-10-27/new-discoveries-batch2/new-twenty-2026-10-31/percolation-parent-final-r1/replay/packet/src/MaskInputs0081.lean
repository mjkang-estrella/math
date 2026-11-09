import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause4672 : CNF.NClause := [(36,false),(5,true),(82,true),(83,true),(84,true),(85,true),(86,true),(92,false)]
theorem inputList4672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4672 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4672 (by decide) v hb
mask_input "4672|4951760157141521168315973632|149906801632214017663565856"
def inputClause4673 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(84,false),(85,false),(86,false),(92,true)]
theorem inputList4673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4673 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4673 (by decide) v hb
mask_input "4673|149906801632214086383042592|4951760157141521099596496896"
def inputClause4674 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,false),(85,false),(86,false),(92,true)]
theorem inputList4674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4674 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4674 (by decide) v hb
mask_input "4674|149906801632214086383042560|4951760157141521099596496928"
def inputClause4675 : CNF.NClause := [(36,false),(5,false),(82,true),(83,false),(84,false),(85,false),(86,false),(92,true)]
theorem inputList4675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4675 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4675 (by decide) v hb
mask_input "4675|145071098353755569684217888|4956595860419979616295321600"
def inputClause4676 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,false),(85,false),(86,false),(92,true)]
theorem inputList4676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4676 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4676 (by decide) v hb
mask_input "4676|145071098353755569684217856|4956595860419979616295321632"
def inputClause4677 : CNF.NClause := [(36,false),(5,false),(82,false),(83,true),(84,false),(85,false),(86,false),(92,true)]
theorem inputList4677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4677 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4677 (by decide) v hb
mask_input "4677|140235395075297052985393184|4961431563698438132994146304"
def inputClause4678 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,false),(85,false),(86,false),(92,true)]
theorem inputList4678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4678 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4678 (by decide) v hb
mask_input "4678|140235395075297052985393152|4961431563698438132994146336"
def inputClause4679 : CNF.NClause := [(36,false),(5,false),(82,true),(83,true),(84,false),(85,false),(86,false),(92,true)]
theorem inputList4679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4679 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4679 (by decide) v hb
mask_input "4679|135399691796838536286568480|4966267266976896649692971008"
def inputClause4680 : CNF.NClause := [(36,false),(5,true),(82,true),(83,true),(84,false),(85,false),(86,false),(92,true)]
theorem inputList4680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4680 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4680 (by decide) v hb
mask_input "4680|135399691796838536286568448|4966267266976896649692971040"
def inputClause4681 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(84,true),(85,false),(86,false),(92,true)]
theorem inputList4681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4681 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4681 (by decide) v hb
mask_input "4681|130563988518380019587743776|4971102970255355166391795712"
def inputClause4682 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,true),(85,false),(86,false),(92,true)]
theorem inputList4682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4682 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4682 (by decide) v hb
mask_input "4682|130563988518380019587743744|4971102970255355166391795744"
def inputClause4683 : CNF.NClause := [(36,false),(5,false),(82,true),(83,false),(84,true),(85,false),(86,false),(92,true)]
theorem inputList4683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4683 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4683 (by decide) v hb
mask_input "4683|125728285239921502888919072|4975938673533813683090620416"
def inputClause4684 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,true),(85,false),(86,false),(92,true)]
theorem inputList4684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4684 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4684 (by decide) v hb
mask_input "4684|125728285239921502888919040|4975938673533813683090620448"
def inputClause4685 : CNF.NClause := [(36,false),(5,false),(82,false),(83,true),(84,true),(85,false),(86,false),(92,true)]
theorem inputList4685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4685 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4685 (by decide) v hb
mask_input "4685|120892581961462986190094368|4980774376812272199789445120"
def inputClause4686 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,true),(85,false),(86,false),(92,true)]
theorem inputList4686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4686 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4686 (by decide) v hb
mask_input "4686|120892581961462986190094336|4980774376812272199789445152"
def inputClause4687 : CNF.NClause := [(36,false),(5,false),(82,true),(83,true),(84,true),(85,false),(86,false),(92,true)]
theorem inputList4687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4687 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4687 (by decide) v hb
mask_input "4687|116056878683004469491269664|4985610080090730716488269824"
def inputClause4688 : CNF.NClause := [(36,false),(5,true),(82,true),(83,true),(84,true),(85,false),(86,false),(92,true)]
theorem inputList4688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4688 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4688 (by decide) v hb
mask_input "4688|116056878683004469491269632|4985610080090730716488269856"
def inputClause4689 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(84,false),(85,true),(86,false),(92,true)]
theorem inputList4689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4689 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4689 (by decide) v hb
mask_input "4689|111221175404545952792444960|4990445783369189233187094528"
def inputClause4690 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,false),(85,true),(86,false),(92,true)]
theorem inputList4690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4690 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4690 (by decide) v hb
mask_input "4690|111221175404545952792444928|4990445783369189233187094560"
def inputClause4691 : CNF.NClause := [(36,false),(5,false),(82,true),(83,false),(84,false),(85,true),(86,false),(92,true)]
theorem inputList4691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4691 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4691 (by decide) v hb
mask_input "4691|106385472126087436093620256|4995281486647647749885919232"
def inputClause4692 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,false),(85,true),(86,false),(92,true)]
theorem inputList4692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4692 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4692 (by decide) v hb
mask_input "4692|106385472126087436093620224|4995281486647647749885919264"
def inputClause4693 : CNF.NClause := [(36,false),(5,false),(82,false),(83,true),(84,false),(85,true),(86,false),(92,true)]
theorem inputList4693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4693 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4693 (by decide) v hb
mask_input "4693|101549768847628919394795552|5000117189926106266584743936"
def inputClause4694 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,false),(85,true),(86,false),(92,true)]
theorem inputList4694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4694 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4694 (by decide) v hb
mask_input "4694|101549768847628919394795520|5000117189926106266584743968"
def inputClause4695 : CNF.NClause := [(36,false),(5,false),(82,true),(83,true),(84,false),(85,true),(86,false),(92,true)]
theorem inputList4695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4695 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4695 (by decide) v hb
mask_input "4695|96714065569170402695970848|5004952893204564783283568640"
def inputClause4696 : CNF.NClause := [(36,false),(5,true),(82,true),(83,true),(84,false),(85,true),(86,false),(92,true)]
theorem inputList4696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4696 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4696 (by decide) v hb
mask_input "4696|96714065569170402695970816|5004952893204564783283568672"
def inputClause4697 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(84,true),(85,true),(86,false),(92,true)]
theorem inputList4697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4697 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4697 (by decide) v hb
mask_input "4697|91878362290711885997146144|5009788596483023299982393344"
def inputClause4698 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,true),(85,true),(86,false),(92,true)]
theorem inputList4698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4698 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4698 (by decide) v hb
mask_input "4698|91878362290711885997146112|5009788596483023299982393376"
def inputClause4699 : CNF.NClause := [(36,false),(5,false),(82,true),(83,false),(84,true),(85,true),(86,false),(92,true)]
theorem inputList4699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4699 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4699 (by decide) v hb
mask_input "4699|87042659012253369298321440|5014624299761481816681218048"
def inputClause4700 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,true),(85,true),(86,false),(92,true)]
theorem inputList4700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4700 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4700 (by decide) v hb
mask_input "4700|87042659012253369298321408|5014624299761481816681218080"
def inputClause4701 : CNF.NClause := [(36,false),(5,false),(82,false),(83,true),(84,true),(85,true),(86,false),(92,true)]
theorem inputList4701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4701 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4701 (by decide) v hb
mask_input "4701|82206955733794852599496736|5019460003039940333380042752"
def inputClause4702 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,true),(85,true),(86,false),(92,true)]
theorem inputList4702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4702 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4702 (by decide) v hb
mask_input "4702|82206955733794852599496704|5019460003039940333380042784"
def inputClause4703 : CNF.NClause := [(36,false),(5,false),(82,true),(83,true),(84,true),(85,true),(86,false),(92,true)]
theorem inputList4703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4703 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4703 (by decide) v hb
mask_input "4703|77371252455336335900672032|5024295706318398850078867456"
def inputClause4704 : CNF.NClause := [(36,false),(5,true),(82,true),(83,true),(84,true),(85,true),(86,false),(92,true)]
theorem inputList4704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4704 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4704 (by decide) v hb
mask_input "4704|77371252455336335900672000|5024295706318398850078867488"
def inputClause4705 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(84,false),(85,false),(86,true),(92,true)]
theorem inputList4705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4705 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4705 (by decide) v hb
mask_input "4705|72535549176877819201847328|5029131409596857366777692160"
def inputClause4706 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,false),(85,false),(86,true),(92,true)]
theorem inputList4706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4706 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4706 (by decide) v hb
mask_input "4706|72535549176877819201847296|5029131409596857366777692192"
def inputClause4707 : CNF.NClause := [(36,false),(5,false),(82,true),(83,false),(84,false),(85,false),(86,true),(92,true)]
theorem inputList4707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4707 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4707 (by decide) v hb
mask_input "4707|67699845898419302503022624|5033967112875315883476516864"
def inputClause4708 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,false),(85,false),(86,true),(92,true)]
theorem inputList4708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4708 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4708 (by decide) v hb
mask_input "4708|67699845898419302503022592|5033967112875315883476516896"
def inputClause4709 : CNF.NClause := [(36,false),(5,false),(82,false),(83,true),(84,false),(85,false),(86,true),(92,true)]
theorem inputList4709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4709 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4709 (by decide) v hb
mask_input "4709|62864142619960785804197920|5038802816153774400175341568"
def inputClause4710 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,false),(85,false),(86,true),(92,true)]
theorem inputList4710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4710 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4710 (by decide) v hb
mask_input "4710|62864142619960785804197888|5038802816153774400175341600"
def inputClause4711 : CNF.NClause := [(36,false),(5,false),(82,true),(83,true),(84,false),(85,false),(86,true),(92,true)]
theorem inputList4711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4711 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4711 (by decide) v hb
mask_input "4711|58028439341502269105373216|5043638519432232916874166272"
end Percolation.MaskChain
