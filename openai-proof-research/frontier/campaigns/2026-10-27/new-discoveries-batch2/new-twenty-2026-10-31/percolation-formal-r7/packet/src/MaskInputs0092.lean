import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause5794 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,false),(79,false),(86,true),(89,false)]
theorem inputList5794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5794 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5794 (by decide) v hb
mask_input "5794|619580394734008260320296960|77371252455336267181211648"
def inputClause5798 : CNF.NClause := [(45,false),(14,true),(63,false),(70,true),(72,false),(79,false),(86,true),(89,false)]
theorem inputList5798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5798 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5798 (by decide) v hb
mask_input "5798|619579214142387542908993536|77372433046956984592515072"
def inputClause5806 : CNF.NClause := [(45,false),(14,true),(63,false),(70,true),(72,true),(79,false),(86,true),(89,false)]
theorem inputList5806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5806 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5806 (by decide) v hb
mask_input "5806|619574491775904673263779840|77377155413439854237728768"
def inputClause5814 : CNF.NClause := [(45,false),(14,true),(63,false),(70,true),(72,false),(79,true),(86,true),(89,false)]
theorem inputList5814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5814 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5814 (by decide) v hb
mask_input "5814|618974751232580228321640448|77976895956764299179868160"
def inputClause5822 : CNF.NClause := [(45,false),(14,true),(63,false),(70,true),(72,true),(79,true),(86,true),(89,false)]
theorem inputList5822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5822 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5822 (by decide) v hb
mask_input "5822|618970028866097358676426752|77981618323247168825081856"
def inputClause5830 : CNF.NClause := [(45,false),(14,true),(63,false),(70,true),(72,false),(79,false),(86,false),(89,true)]
theorem inputList5830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5830 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5830 (by decide) v hb
mask_input "5830|77980446955033672640626688|618971200234310854860881920"
def inputClause5838 : CNF.NClause := [(45,false),(14,true),(63,false),(70,true),(72,true),(79,false),(86,false),(89,true)]
theorem inputList5838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5838 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5838 (by decide) v hb
mask_input "5838|77975724588550802995412992|618975922600793724506095616"
def inputClause5846 : CNF.NClause := [(45,false),(14,true),(63,false),(70,true),(72,false),(79,true),(86,false),(89,true)]
theorem inputList5846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5846 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5846 (by decide) v hb
mask_input "5846|77375984045226358053273600|619575663144118169448235008"
def inputClause5854 : CNF.NClause := [(45,false),(14,true),(63,false),(70,true),(72,true),(79,true),(86,false),(89,true)]
theorem inputList5854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5854 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5854 (by decide) v hb
mask_input "5854|77371261678743488408059904|619580385510601039093448704"
def inputClause5858 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,false),(79,false),(86,true),(89,true)]
theorem inputList5858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5858 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5858 (by decide) v hb
mask_input "5858|610375091318122870734848|696341272098026404630773760"
def inputClause5862 : CNF.NClause := [(45,false),(14,true),(63,false),(70,true),(72,false),(79,false),(86,true),(89,true)]
theorem inputList5862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5862 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5862 (by decide) v hb
mask_input "5862|609194499697405459431424|696342452689647122042077184"
def inputClause5870 : CNF.NClause := [(45,false),(14,true),(63,false),(70,true),(72,true),(79,false),(86,true),(89,true)]
theorem inputList5870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5870 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5870 (by decide) v hb
mask_input "5870|604472133214535814217728|696347175056129991687290880"
def inputClause5878 : CNF.NClause := [(45,false),(14,true),(63,false),(70,true),(72,false),(79,true),(86,true),(89,true)]
theorem inputList5878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5878 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5878 (by decide) v hb
mask_input "5878|4731589890090872078336|696946915599454436629430272"
def inputClause5886 : CNF.NClause := [(45,false),(14,true),(63,false),(70,true),(72,true),(79,true),(86,true),(89,true)]
theorem inputList5886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5886 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5886 (by decide) v hb
mask_input "5886|9223407221226864640|696951637965937306274643968"
def inputClause5891 : CNF.NClause := [(46,false),(15,false),(77,true),(78,false),(79,false),(80,false),(81,false),(92,false)]
theorem inputList5891 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5891 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5891 (by decide) v hb
mask_input "5891|4956293628965146327745855488|151115727451828646838272"
def inputClause5907 : CNF.NClause := [(46,false),(15,false),(77,true),(78,false),(79,false),(80,true),(81,false),(92,false)]
theorem inputList5907 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5907 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5907 (by decide) v hb
mask_input "5907|4955084703145531698571149312|1360041547066457821544448"
def inputClause5939 : CNF.NClause := [(46,false),(15,false),(77,true),(78,false),(79,false),(80,true),(81,true),(92,false)]
theorem inputList5939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5939 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5939 (by decide) v hb
mask_input "5939|4952666851506302440221736960|3777893186295716170956800"
def inputClause5955 : CNF.NClause := [(46,false),(15,false),(77,true),(78,false),(79,false),(80,false),(81,false),(92,true)]
theorem inputList5955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5955 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5955 (by decide) v hb
mask_input "5955|4533471823625228149358592|4951911272868972928243335168"
def inputClause5971 : CNF.NClause := [(46,false),(15,false),(77,true),(78,false),(79,false),(80,true),(81,false),(92,true)]
theorem inputList5971 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5971 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5971 (by decide) v hb
mask_input "5971|3324546004010598974652416|4953120198688587557418041344"
def inputClause6003 : CNF.NClause := [(46,false),(15,false),(77,true),(78,false),(79,false),(80,true),(81,true),(92,true)]
theorem inputList6003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6003 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause6003 (by decide) v hb
mask_input "6003|906694364781340625240064|4955538050327816815767453696"
def inputClause6018 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,false),(77,false),(84,false),(89,false)]
theorem inputList6018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6018 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6018 (by decide) v hb
mask_input "6018|638502096350861201732796416|65536"
def inputClause6022 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true),(75,false),(77,false),(84,false),(89,false)]
theorem inputList6022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6022 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6022 (by decide) v hb
mask_input "6022|638501801202956022379970560|295147905179352891392"
def inputClause6030 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true),(75,true),(77,false),(84,false),(89,false)]
theorem inputList6030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6030 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6030 (by decide) v hb
mask_input "6030|638464022271093065218260992|38074079768136514600960"
def inputClause6033 : CNF.NClause := [(47,false),(16,false),(66,false),(68,false),(75,false),(77,true),(84,false),(89,false)]
theorem inputList6033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6033 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6033 (by decide) v hb
mask_input "6033|638350980623409373086023680|151115727451828646838272"
def inputClause6034 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,false),(77,true),(84,false),(89,false)]
theorem inputList6034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6034 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6034 (by decide) v hb
mask_input "6034|638350980623409373085958144|151115727451828646903808"
def inputClause6038 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true),(75,false),(77,true),(84,false),(89,false)]
theorem inputList6038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6038 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6038 (by decide) v hb
mask_input "6038|638350685475504193733132288|151410875357007999729664"
def inputClause6046 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true),(75,true),(77,true),(84,false),(89,false)]
theorem inputList6046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6046 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6046 (by decide) v hb
mask_input "6046|638312906543641236571422720|189189807219965161439232"
def inputClause6054 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true),(75,false),(77,false),(84,true),(89,false)]
theorem inputList6054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6054 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6054 (by decide) v hb
mask_input "6054|619158988089121955584671744|19343108261739246148190208"
def inputClause6062 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true),(75,true),(77,false),(84,true),(89,false)]
theorem inputList6062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6062 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6062 (by decide) v hb
mask_input "6062|619121209157258998422962176|19380887193602203309899776"
def inputClause6070 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true),(75,false),(77,true),(84,true),(89,false)]
theorem inputList6070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6070 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6070 (by decide) v hb
mask_input "6070|619007872361670126937833472|19494223989191074795028480"
def inputClause6078 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true),(75,true),(77,true),(84,true),(89,false)]
theorem inputList6078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6078 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6078 (by decide) v hb
mask_input "6078|618970093429807169776123904|19532002921054031956738048"
def inputClause6086 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true),(75,false),(77,false),(84,false),(89,true)]
theorem inputList6086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6086 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6086 (by decide) v hb
mask_input "6086|19531781560265884930408448|618970314790595316802453504"
def inputClause6094 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true),(75,true),(77,false),(84,false),(89,true)]
theorem inputList6094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6094 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6094 (by decide) v hb
mask_input "6094|19494002628402927768698880|619008093722458273964163072"
def inputClause6102 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true),(75,false),(77,true),(84,false),(89,true)]
theorem inputList6102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6102 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6102 (by decide) v hb
mask_input "6102|19380665832814056283570176|619121430518047145449291776"
def inputClause6110 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true),(75,true),(77,true),(84,false),(89,true)]
theorem inputList6110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6110 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6110 (by decide) v hb
mask_input "6110|19342886900951099121860608|619159209449910102611001344"
def inputClause6118 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true),(75,false),(77,false),(84,true),(89,true)]
theorem inputList6118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6118 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6118 (by decide) v hb
mask_input "6118|188968446431818135109632|638313127904429383597752320"
def inputClause6126 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true),(75,true),(77,false),(84,true),(89,true)]
theorem inputList6126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6126 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6126 (by decide) v hb
mask_input "6126|151189514568860973400064|638350906836292340759461888"
def inputClause6134 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true),(75,false),(77,true),(84,true),(89,true)]
theorem inputList6134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6134 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6134 (by decide) v hb
mask_input "6134|37852718979989488271360|638464243631881212244590592"
def inputClause6142 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true),(75,true),(77,true),(84,true),(89,true)]
theorem inputList6142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6142 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) inputClause6142 (by decide) v hb
mask_input "6142|73787117032326561792|638502022563744169406300160"
def inputClause6146 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,false),(77,false),(83,false),(88,false)]
theorem inputList6146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6146 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6146 (by decide) v hb
mask_input "6146|319384289008086111190253568|131072"
end Percolation.MaskChain
