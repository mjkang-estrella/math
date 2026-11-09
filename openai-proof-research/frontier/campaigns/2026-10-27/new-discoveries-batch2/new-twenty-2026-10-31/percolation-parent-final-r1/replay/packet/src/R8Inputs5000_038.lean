import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause6008 : CNF.NClause := [(46,false),(15,true),(77,true),(78,true),(79,false),(80,true),(81,true),(92,true)]
theorem inputList6008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6008 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause6008 (by decide) v hb
mask_input "6008|604462909877683331530752|4955840281782720473061163008"
def inputClause6009 : CNF.NClause := [(46,false),(15,false),(77,false),(78,false),(79,true),(80,true),(81,true),(92,true)]
theorem inputList6009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6009 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause6009 (by decide) v hb
mask_input "6009|453347182425854684725248|4955991397510172301707968512"
def inputClause6010 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,true),(80,true),(81,true),(92,true)]
theorem inputList6010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6010 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause6010 (by decide) v hb
mask_input "6010|453347182425854684692480|4955991397510172301708001280"
def inputClause6011 : CNF.NClause := [(46,false),(15,false),(77,true),(78,false),(79,true),(80,true),(81,true),(92,true)]
theorem inputList6011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6011 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause6011 (by decide) v hb
mask_input "6011|302231454974026037886976|4956142513237624130354806784"
def inputClause6012 : CNF.NClause := [(46,false),(15,true),(77,true),(78,false),(79,true),(80,true),(81,true),(92,true)]
theorem inputList6012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6012 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause6012 (by decide) v hb
mask_input "6012|302231454974026037854208|4956142513237624130354839552"
def inputClause6013 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(79,true),(80,true),(81,true),(92,true)]
theorem inputList6013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6013 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause6013 (by decide) v hb
mask_input "6013|151115727522197391048704|4956293628965075959001645056"
def inputClause6014 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(79,true),(80,true),(81,true),(92,true)]
theorem inputList6014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6014 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause6014 (by decide) v hb
mask_input "6014|151115727522197391015936|4956293628965075959001677824"
def inputClause6015 : CNF.NClause := [(46,false),(15,false),(77,true),(78,true),(79,true),(80,true),(81,true),(92,true)]
theorem inputList6015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6015 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause6015 (by decide) v hb
mask_input "6015|70368744210432|4956444744692527787648483328"
def inputClause6016 : CNF.NClause := [(46,false),(15,true),(77,true),(78,true),(79,true),(80,true),(81,true),(92,true)]
theorem inputList6016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6016 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause6016 (by decide) v hb
mask_input "6016|70368744177664|4956444744692527787648516096"
def inputClause6017 : CNF.NClause := [(47,true),(16,false),(66,false),(68,false),(75,false),(77,false),(84,false),(89,false)]
theorem inputList6017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6017 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6017 (by decide) v hb
mask_input "6017|638502096350720464244506624|140737488355328"
def inputClause6019 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(75,false),(77,false),(84,false),(89,false)]
theorem inputList6019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6019 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6019 (by decide) v hb
mask_input "6019|638502022563884906894655488|73786976294838206464"
def inputClause6020 : CNF.NClause := [(47,false),(16,true),(66,true),(68,false),(75,false),(77,false),(84,false),(89,false)]
theorem inputList6020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6020 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6020 (by decide) v hb
mask_input "6020|638502022563884906894589952|73786976294838272000"
def inputClause6021 : CNF.NClause := [(47,false),(16,false),(66,false),(68,true),(75,false),(77,false),(84,false),(89,false)]
theorem inputList6021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6021 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6021 (by decide) v hb
mask_input "6021|638501801202956022380036096|295147905179352825856"
def inputClause6023 : CNF.NClause := [(47,false),(16,false),(66,true),(68,true),(75,false),(77,false),(84,false),(89,false)]
theorem inputList6023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6023 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6023 (by decide) v hb
mask_input "6023|638501727415979727541829632|368934881474191032320"
def inputClause6024 : CNF.NClause := [(47,false),(16,true),(66,true),(68,true),(75,false),(77,false),(84,false),(89,false)]
theorem inputList6024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6024 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6024 (by decide) v hb
mask_input "6024|638501727415979727541764096|368934881474191097856"
def inputClause6025 : CNF.NClause := [(47,false),(16,false),(66,false),(68,false),(75,true),(77,false),(84,false),(89,false)]
theorem inputList6025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6025 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6025 (by decide) v hb
mask_input "6025|638464317418998244571152384|37778931862957161709568"
def inputClause6026 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,true),(77,false),(84,false),(89,false)]
theorem inputList6026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6026 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6026 (by decide) v hb
mask_input "6026|638464317418998244571086848|37778931862957161775104"
def inputClause6027 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(75,true),(77,false),(84,false),(89,false)]
theorem inputList6027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6027 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6027 (by decide) v hb
mask_input "6027|638464243632021949732945920|37852718839251999916032"
def inputClause6028 : CNF.NClause := [(47,false),(16,true),(66,true),(68,false),(75,true),(77,false),(84,false),(89,false)]
theorem inputList6028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6028 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6028 (by decide) v hb
mask_input "6028|638464243632021949732880384|37852718839251999981568"
def inputClause6029 : CNF.NClause := [(47,false),(16,false),(66,false),(68,true),(75,true),(77,false),(84,false),(89,false)]
theorem inputList6029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6029 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6029 (by decide) v hb
mask_input "6029|638464022271093065218326528|38074079768136514535424"
def inputClause6031 : CNF.NClause := [(47,false),(16,false),(66,true),(68,true),(75,true),(77,false),(84,false),(89,false)]
theorem inputList6031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6031 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6031 (by decide) v hb
mask_input "6031|638463948484116770380120064|38147866744431352741888"
def inputClause6032 : CNF.NClause := [(47,false),(16,true),(66,true),(68,true),(75,true),(77,false),(84,false),(89,false)]
theorem inputList6032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6032 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6032 (by decide) v hb
mask_input "6032|638463948484116770380054528|38147866744431352807424"
def inputClause6035 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(75,false),(77,true),(84,false),(89,false)]
theorem inputList6035 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6035 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6035 (by decide) v hb
mask_input "6035|638350906836433078247817216|151189514428123485044736"
def inputClause6036 : CNF.NClause := [(47,false),(16,true),(66,true),(68,false),(75,false),(77,true),(84,false),(89,false)]
theorem inputList6036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6036 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6036 (by decide) v hb
mask_input "6036|638350906836433078247751680|151189514428123485110272"
def inputClause6037 : CNF.NClause := [(47,false),(16,false),(66,false),(68,true),(75,false),(77,true),(84,false),(89,false)]
theorem inputList6037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6037 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6037 (by decide) v hb
mask_input "6037|638350685475504193733197824|151410875357007999664128"
def inputClause6039 : CNF.NClause := [(47,false),(16,false),(66,true),(68,true),(75,false),(77,true),(84,false),(89,false)]
theorem inputList6039 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6039 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6039 (by decide) v hb
mask_input "6039|638350611688527898894991360|151484662333302837870592"
def inputClause6040 : CNF.NClause := [(47,false),(16,true),(66,true),(68,true),(75,false),(77,true),(84,false),(89,false)]
theorem inputList6040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6040 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6040 (by decide) v hb
mask_input "6040|638350611688527898894925824|151484662333302837936128"
def inputClause6041 : CNF.NClause := [(47,false),(16,false),(66,false),(68,false),(75,true),(77,true),(84,false),(89,false)]
theorem inputList6041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6041 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6041 (by decide) v hb
mask_input "6041|638313201691546415924314112|188894659314785808547840"
def inputClause6042 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,true),(77,true),(84,false),(89,false)]
theorem inputList6042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6042 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6042 (by decide) v hb
mask_input "6042|638313201691546415924248576|188894659314785808613376"
def inputClause6043 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(75,true),(77,true),(84,false),(89,false)]
theorem inputList6043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6043 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6043 (by decide) v hb
mask_input "6043|638313127904570121086107648|188968446291080646754304"
def inputClause6044 : CNF.NClause := [(47,false),(16,true),(66,true),(68,false),(75,true),(77,true),(84,false),(89,false)]
theorem inputList6044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6044 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6044 (by decide) v hb
mask_input "6044|638313127904570121086042112|188968446291080646819840"
def inputClause6045 : CNF.NClause := [(47,false),(16,false),(66,false),(68,true),(75,true),(77,true),(84,false),(89,false)]
theorem inputList6045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6045 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6045 (by decide) v hb
mask_input "6045|638312906543641236571488256|189189807219965161373696"
def inputClause6047 : CNF.NClause := [(47,false),(16,false),(66,true),(68,true),(75,true),(77,true),(84,false),(89,false)]
theorem inputList6047 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6047 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6047 (by decide) v hb
mask_input "6047|638312832756664941733281792|189263594196259999580160"
def inputClause6048 : CNF.NClause := [(47,false),(16,true),(66,true),(68,true),(75,true),(77,true),(84,false),(89,false)]
theorem inputList6048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6048 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6048 (by decide) v hb
mask_input "6048|638312832756664941733216256|189263594196259999645696"
def inputClause6049 : CNF.NClause := [(47,false),(16,false),(66,false),(68,false),(75,false),(77,false),(84,true),(89,false)]
theorem inputList6049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6049 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6049 (by decide) v hb
mask_input "6049|619159283237027134937563136|19342813113834066795298816"
def inputClause6050 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,false),(77,false),(84,true),(89,false)]
theorem inputList6050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6050 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6050 (by decide) v hb
mask_input "6050|619159283237027134937497600|19342813113834066795364352"
def inputClause6051 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(75,false),(77,false),(84,true),(89,false)]
theorem inputList6051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6051 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6051 (by decide) v hb
mask_input "6051|619159209450050840099356672|19342886900810361633505280"
def inputClause6052 : CNF.NClause := [(47,false),(16,true),(66,true),(68,false),(75,false),(77,false),(84,true),(89,false)]
theorem inputList6052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6052 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6052 (by decide) v hb
mask_input "6052|619159209450050840099291136|19342886900810361633570816"
def inputClause6053 : CNF.NClause := [(47,false),(16,false),(66,false),(68,true),(75,false),(77,false),(84,true),(89,false)]
theorem inputList6053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6053 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6053 (by decide) v hb
mask_input "6053|619158988089121955584737280|19343108261739246148124672"
def inputClause6055 : CNF.NClause := [(47,false),(16,false),(66,true),(68,true),(75,false),(77,false),(84,true),(89,false)]
theorem inputList6055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6055 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6055 (by decide) v hb
mask_input "6055|619158914302145660746530816|19343182048715540986331136"
end Percolation.MaskChain
