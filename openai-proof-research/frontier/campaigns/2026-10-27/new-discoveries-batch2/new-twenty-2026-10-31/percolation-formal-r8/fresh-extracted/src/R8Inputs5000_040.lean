import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause6101 : CNF.NClause := [(47,false),(16,false),(66,false),(68,true),(75,false),(77,true),(84,false),(89,true)]
theorem inputList6101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6101 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6101 (by decide) v hb
mask_input "6101|19380665832814056283635712|619121430518047145449226240"
def inputClause6104 : CNF.NClause := [(47,false),(16,true),(66,true),(68,true),(75,false),(77,true),(84,false),(89,true)]
theorem inputList6104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6104 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6104 (by decide) v hb
mask_input "6104|19380592045837761445363712|619121504305023440287498240"
def inputClause6105 : CNF.NClause := [(47,false),(16,false),(66,false),(68,false),(75,true),(77,true),(84,false),(89,true)]
theorem inputList6105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6105 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6105 (by decide) v hb
mask_input "6105|19343182048856278474752000|619158914302004923258109952"
def inputClause6106 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,true),(77,true),(84,false),(89,true)]
theorem inputList6106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6106 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6106 (by decide) v hb
mask_input "6106|19343182048856278474686464|619158914302004923258175488"
def inputClause6107 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(75,true),(77,true),(84,false),(89,true)]
theorem inputList6107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6107 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6107 (by decide) v hb
mask_input "6107|19343108261879983636545536|619158988088981218096316416"
def inputClause6108 : CNF.NClause := [(47,false),(16,true),(66,true),(68,false),(75,true),(77,true),(84,false),(89,true)]
theorem inputList6108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6108 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6108 (by decide) v hb
mask_input "6108|19343108261879983636480000|619158988088981218096381952"
def inputClause6109 : CNF.NClause := [(47,false),(16,false),(66,false),(68,true),(75,true),(77,true),(84,false),(89,true)]
theorem inputList6109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6109 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6109 (by decide) v hb
mask_input "6109|19342886900951099121926144|619159209449910102610935808"
def inputClause6111 : CNF.NClause := [(47,false),(16,false),(66,true),(68,true),(75,true),(77,true),(84,false),(89,true)]
theorem inputList6111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6111 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6111 (by decide) v hb
mask_input "6111|19342813113974804283719680|619159283236886397449142272"
def inputClause6112 : CNF.NClause := [(47,false),(16,true),(66,true),(68,true),(75,true),(77,true),(84,false),(89,true)]
theorem inputList6112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6112 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6112 (by decide) v hb
mask_input "6112|19342813113974804283654144|619159283236886397449207808"
def inputClause6113 : CNF.NClause := [(47,false),(16,false),(66,false),(68,false),(75,false),(77,false),(84,true),(89,true)]
theorem inputList6113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6113 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6113 (by decide) v hb
mask_input "6113|189263594336997488001024|638312832756524204244860928"
def inputClause6114 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,false),(77,false),(84,true),(89,true)]
theorem inputList6114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6114 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6114 (by decide) v hb
mask_input "6114|189263594336997487935488|638312832756524204244926464"
def inputClause6115 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(75,false),(77,false),(84,true),(89,true)]
theorem inputList6115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6115 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6115 (by decide) v hb
mask_input "6115|189189807360702649794560|638312906543500499083067392"
def inputClause6116 : CNF.NClause := [(47,false),(16,true),(66,true),(68,false),(75,false),(77,false),(84,true),(89,true)]
theorem inputList6116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6116 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6116 (by decide) v hb
mask_input "6116|189189807360702649729024|638312906543500499083132928"
def inputClause6117 : CNF.NClause := [(47,false),(16,false),(66,false),(68,true),(75,false),(77,false),(84,true),(89,true)]
theorem inputList6117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6117 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6117 (by decide) v hb
mask_input "6117|188968446431818135175168|638313127904429383597686784"
def inputClause6119 : CNF.NClause := [(47,false),(16,false),(66,true),(68,true),(75,false),(77,false),(84,true),(89,true)]
theorem inputList6119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6119 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6119 (by decide) v hb
mask_input "6119|188894659455523296968704|638313201691405678435893248"
def inputClause6120 : CNF.NClause := [(47,false),(16,true),(66,true),(68,true),(75,false),(77,false),(84,true),(89,true)]
theorem inputList6120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6120 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6120 (by decide) v hb
mask_input "6120|188894659455523296903168|638313201691405678435958784"
def inputClause6121 : CNF.NClause := [(47,false),(16,false),(66,false),(68,false),(75,true),(77,false),(84,true),(89,true)]
theorem inputList6121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6121 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6121 (by decide) v hb
mask_input "6121|151484662474040326291456|638350611688387161406570496"
def inputClause6122 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,true),(77,false),(84,true),(89,true)]
theorem inputList6122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6122 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6122 (by decide) v hb
mask_input "6122|151484662474040326225920|638350611688387161406636032"
def inputClause6123 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(75,true),(77,false),(84,true),(89,true)]
theorem inputList6123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6123 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6123 (by decide) v hb
mask_input "6123|151410875497745488084992|638350685475363456244776960"
def inputClause6124 : CNF.NClause := [(47,false),(16,true),(66,true),(68,false),(75,true),(77,false),(84,true),(89,true)]
theorem inputList6124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6124 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6124 (by decide) v hb
mask_input "6124|151410875497745488019456|638350685475363456244842496"
def inputClause6125 : CNF.NClause := [(47,false),(16,false),(66,false),(68,true),(75,true),(77,false),(84,true),(89,true)]
theorem inputList6125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6125 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6125 (by decide) v hb
mask_input "6125|151189514568860973465600|638350906836292340759396352"
def inputClause6127 : CNF.NClause := [(47,false),(16,false),(66,true),(68,true),(75,true),(77,false),(84,true),(89,true)]
theorem inputList6127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6127 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6127 (by decide) v hb
mask_input "6127|151115727592566135259136|638350980623268635597602816"
def inputClause6128 : CNF.NClause := [(47,false),(16,true),(66,true),(68,true),(75,true),(77,false),(84,true),(89,true)]
theorem inputList6128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6128 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6128 (by decide) v hb
mask_input "6128|151115727592566135193600|638350980623268635597668352"
def inputClause6129 : CNF.NClause := [(47,false),(16,false),(66,false),(68,false),(75,false),(77,true),(84,true),(89,true)]
theorem inputList6129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6129 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6129 (by decide) v hb
mask_input "6129|38147866885168841162752|638463948483976032891699200"
def inputClause6130 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,false),(77,true),(84,true),(89,true)]
theorem inputList6130 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6130 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6130 (by decide) v hb
mask_input "6130|38147866885168841097216|638463948483976032891764736"
def inputClause6131 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(75,false),(77,true),(84,true),(89,true)]
theorem inputList6131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6131 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6131 (by decide) v hb
mask_input "6131|38074079908874002956288|638464022270952327729905664"
def inputClause6132 : CNF.NClause := [(47,false),(16,true),(66,true),(68,false),(75,false),(77,true),(84,true),(89,true)]
theorem inputList6132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6132 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6132 (by decide) v hb
mask_input "6132|38074079908874002890752|638464022270952327729971200"
def inputClause6133 : CNF.NClause := [(47,false),(16,false),(66,false),(68,true),(75,false),(77,true),(84,true),(89,true)]
theorem inputList6133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6133 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6133 (by decide) v hb
mask_input "6133|37852718979989488336896|638464243631881212244525056"
def inputClause6136 : CNF.NClause := [(47,false),(16,true),(66,true),(68,true),(75,false),(77,true),(84,true),(89,true)]
theorem inputList6136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6136 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6136 (by decide) v hb
mask_input "6136|37778932003694650064896|638464317418857507082797056"
def inputClause6137 : CNF.NClause := [(47,false),(16,false),(66,false),(68,false),(75,true),(77,true),(84,true),(89,true)]
theorem inputList6137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6137 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6137 (by decide) v hb
mask_input "6137|368935022211679453184|638501727415838990053408768"
def inputClause6138 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,true),(77,true),(84,true),(89,true)]
theorem inputList6138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6138 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6138 (by decide) v hb
mask_input "6138|368935022211679387648|638501727415838990053474304"
def inputClause6139 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(75,true),(77,true),(84,true),(89,true)]
theorem inputList6139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6139 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6139 (by decide) v hb
mask_input "6139|295148045916841246720|638501801202815284891615232"
def inputClause6140 : CNF.NClause := [(47,false),(16,true),(66,true),(68,false),(75,true),(77,true),(84,true),(89,true)]
theorem inputList6140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6140 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6140 (by decide) v hb
mask_input "6140|295148045916841181184|638501801202815284891680768"
def inputClause6141 : CNF.NClause := [(47,false),(16,false),(66,false),(68,true),(75,true),(77,true),(84,true),(89,true)]
theorem inputList6141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6141 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6141 (by decide) v hb
mask_input "6141|73787117032326627328|638502022563744169406234624"
def inputClause6143 : CNF.NClause := [(47,false),(16,false),(66,true),(68,true),(75,true),(77,true),(84,true),(89,true)]
theorem inputList6143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6143 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6143 (by decide) v hb
mask_input "6143|140737488420864|638502096350720464244441088"
def inputClause6144 : CNF.NClause := [(47,false),(16,true),(66,true),(68,true),(75,true),(77,true),(84,true),(89,true)]
theorem inputList6144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6144 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6144 (by decide) v hb
mask_input "6144|140737488355328|638502096350720464244506624"
def inputClause6145 : CNF.NClause := [(48,true),(17,false),(64,false),(70,false),(76,false),(77,false),(83,false),(88,false)]
theorem inputList6145 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6145 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6145 (by decide) v hb
mask_input "6145|319384289007804636213673984|281474976710656"
def inputClause6147 : CNF.NClause := [(48,false),(17,false),(64,true),(70,false),(76,false),(77,false),(83,false),(88,false)]
theorem inputList6147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6147 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6147 (by decide) v hb
mask_input "6147|319384270561342037480833024|18446744073709551616"
def inputClause6148 : CNF.NClause := [(48,false),(17,true),(64,true),(70,false),(76,false),(77,false),(83,false),(88,false)]
theorem inputList6148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6148 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6148 (by decide) v hb
mask_input "6148|319384270561342037480701952|18446744073709682688"
def inputClause6149 : CNF.NClause := [(48,false),(17,false),(64,false),(70,true),(76,false),(77,false),(83,false),(88,false)]
theorem inputList6149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6149 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6149 (by decide) v hb
mask_input "6149|319383108416465393779081216|1180591620717411303424"
end Percolation.MaskChain
