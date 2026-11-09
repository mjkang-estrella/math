import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause5966 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(79,true),(80,false),(81,false),(92,true)]
theorem inputList5966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5966 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5966 (by decide) v hb
mask_input "5966|3777893186366084915134464|4952666851506232071477559296"
def inputClause5967 : CNF.NClause := [(46,false),(15,false),(77,true),(78,true),(79,true),(80,false),(81,false),(92,true)]
theorem inputList5967 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5967 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5967 (by decide) v hb
mask_input "5967|3626777458914256268328960|4952817967233683900124364800"
def inputClause5968 : CNF.NClause := [(46,false),(15,true),(77,true),(78,true),(79,true),(80,false),(81,false),(92,true)]
theorem inputList5968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5968 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5968 (by decide) v hb
mask_input "5968|3626777458914256268296192|4952817967233683900124397568"
def inputClause5969 : CNF.NClause := [(46,false),(15,false),(77,false),(78,false),(79,false),(80,true),(81,false),(92,true)]
theorem inputList5969 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5969 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5969 (by decide) v hb
mask_input "5969|3475661731462427621490688|4952969082961135728771203072"
def inputClause5970 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,false),(80,true),(81,false),(92,true)]
theorem inputList5970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5970 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5970 (by decide) v hb
mask_input "5970|3475661731462427621457920|4952969082961135728771235840"
def inputClause5972 : CNF.NClause := [(46,false),(15,true),(77,true),(78,false),(79,false),(80,true),(81,false),(92,true)]
theorem inputList5972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5972 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5972 (by decide) v hb
mask_input "5972|3324546004010598974619648|4953120198688587557418074112"
def inputClause5973 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(79,false),(80,true),(81,false),(92,true)]
theorem inputList5973 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5973 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5973 (by decide) v hb
mask_input "5973|3173430276558770327814144|4953271314416039386064879616"
def inputClause5974 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(79,false),(80,true),(81,false),(92,true)]
theorem inputList5974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5974 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5974 (by decide) v hb
mask_input "5974|3173430276558770327781376|4953271314416039386064912384"
def inputClause5975 : CNF.NClause := [(46,false),(15,false),(77,true),(78,true),(79,false),(80,true),(81,false),(92,true)]
theorem inputList5975 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5975 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5975 (by decide) v hb
mask_input "5975|3022314549106941680975872|4953422430143491214711717888"
def inputClause5976 : CNF.NClause := [(46,false),(15,true),(77,true),(78,true),(79,false),(80,true),(81,false),(92,true)]
theorem inputList5976 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5976 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5976 (by decide) v hb
mask_input "5976|3022314549106941680943104|4953422430143491214711750656"
def inputClause5977 : CNF.NClause := [(46,false),(15,false),(77,false),(78,false),(79,true),(80,true),(81,false),(92,true)]
theorem inputList5977 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5977 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5977 (by decide) v hb
mask_input "5977|2871198821655113034137600|4953573545870943043358556160"
def inputClause5978 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,true),(80,true),(81,false),(92,true)]
theorem inputList5978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5978 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5978 (by decide) v hb
mask_input "5978|2871198821655113034104832|4953573545870943043358588928"
def inputClause5979 : CNF.NClause := [(46,false),(15,false),(77,true),(78,false),(79,true),(80,true),(81,false),(92,true)]
theorem inputList5979 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5979 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5979 (by decide) v hb
mask_input "5979|2720083094203284387299328|4953724661598394872005394432"
def inputClause5980 : CNF.NClause := [(46,false),(15,true),(77,true),(78,false),(79,true),(80,true),(81,false),(92,true)]
theorem inputList5980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5980 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5980 (by decide) v hb
mask_input "5980|2720083094203284387266560|4953724661598394872005427200"
def inputClause5981 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(79,true),(80,true),(81,false),(92,true)]
theorem inputList5981 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5981 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5981 (by decide) v hb
mask_input "5981|2568967366751455740461056|4953875777325846700652232704"
def inputClause5982 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(79,true),(80,true),(81,false),(92,true)]
theorem inputList5982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5982 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5982 (by decide) v hb
mask_input "5982|2568967366751455740428288|4953875777325846700652265472"
def inputClause5983 : CNF.NClause := [(46,false),(15,false),(77,true),(78,true),(79,true),(80,true),(81,false),(92,true)]
theorem inputList5983 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5983 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5983 (by decide) v hb
mask_input "5983|2417851639299627093622784|4954026893053298529299070976"
def inputClause5984 : CNF.NClause := [(46,false),(15,true),(77,true),(78,true),(79,true),(80,true),(81,false),(92,true)]
theorem inputList5984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5984 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5984 (by decide) v hb
mask_input "5984|2417851639299627093590016|4954026893053298529299103744"
def inputClause5985 : CNF.NClause := [(46,false),(15,false),(77,false),(78,false),(79,false),(80,false),(81,true),(92,true)]
theorem inputList5985 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5985 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5985 (by decide) v hb
mask_input "5985|2266735911847798446784512|4954178008780750357945909248"
def inputClause5986 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,false),(80,false),(81,true),(92,true)]
theorem inputList5986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5986 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5986 (by decide) v hb
mask_input "5986|2266735911847798446751744|4954178008780750357945942016"
def inputClause5987 : CNF.NClause := [(46,false),(15,false),(77,true),(78,false),(79,false),(80,false),(81,true),(92,true)]
theorem inputList5987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5987 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5987 (by decide) v hb
mask_input "5987|2115620184395969799946240|4954329124508202186592747520"
def inputClause5988 : CNF.NClause := [(46,false),(15,true),(77,true),(78,false),(79,false),(80,false),(81,true),(92,true)]
theorem inputList5988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5988 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5988 (by decide) v hb
mask_input "5988|2115620184395969799913472|4954329124508202186592780288"
def inputClause5989 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(79,false),(80,false),(81,true),(92,true)]
theorem inputList5989 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5989 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5989 (by decide) v hb
mask_input "5989|1964504456944141153107968|4954480240235654015239585792"
def inputClause5990 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(79,false),(80,false),(81,true),(92,true)]
theorem inputList5990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5990 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5990 (by decide) v hb
mask_input "5990|1964504456944141153075200|4954480240235654015239618560"
def inputClause5991 : CNF.NClause := [(46,false),(15,false),(77,true),(78,true),(79,false),(80,false),(81,true),(92,true)]
theorem inputList5991 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5991 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5991 (by decide) v hb
mask_input "5991|1813388729492312506269696|4954631355963105843886424064"
def inputClause5992 : CNF.NClause := [(46,false),(15,true),(77,true),(78,true),(79,false),(80,false),(81,true),(92,true)]
theorem inputList5992 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5992 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5992 (by decide) v hb
mask_input "5992|1813388729492312506236928|4954631355963105843886456832"
def inputClause5993 : CNF.NClause := [(46,false),(15,false),(77,false),(78,false),(79,true),(80,false),(81,true),(92,true)]
theorem inputList5993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5993 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5993 (by decide) v hb
mask_input "5993|1662273002040483859431424|4954782471690557672533262336"
def inputClause5994 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,true),(80,false),(81,true),(92,true)]
theorem inputList5994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5994 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5994 (by decide) v hb
mask_input "5994|1662273002040483859398656|4954782471690557672533295104"
def inputClause5995 : CNF.NClause := [(46,false),(15,false),(77,true),(78,false),(79,true),(80,false),(81,true),(92,true)]
theorem inputList5995 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5995 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5995 (by decide) v hb
mask_input "5995|1511157274588655212593152|4954933587418009501180100608"
def inputClause5996 : CNF.NClause := [(46,false),(15,true),(77,true),(78,false),(79,true),(80,false),(81,true),(92,true)]
theorem inputList5996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5996 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5996 (by decide) v hb
mask_input "5996|1511157274588655212560384|4954933587418009501180133376"
def inputClause5997 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(79,true),(80,false),(81,true),(92,true)]
theorem inputList5997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5997 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5997 (by decide) v hb
mask_input "5997|1360041547136826565754880|4955084703145461329826938880"
def inputClause5998 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(79,true),(80,false),(81,true),(92,true)]
theorem inputList5998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5998 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5998 (by decide) v hb
mask_input "5998|1360041547136826565722112|4955084703145461329826971648"
def inputClause5999 : CNF.NClause := [(46,false),(15,false),(77,true),(78,true),(79,true),(80,false),(81,true),(92,true)]
theorem inputList5999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5999 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5999 (by decide) v hb
mask_input "5999|1208925819684997918916608|4955235818872913158473777152"
def inputClause6000 : CNF.NClause := [(46,false),(15,true),(77,true),(78,true),(79,true),(80,false),(81,true),(92,true)]
theorem inputList6000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6000 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause6000 (by decide) v hb
mask_input "6000|1208925819684997918883840|4955235818872913158473809920"
def inputClause6001 : CNF.NClause := [(46,false),(15,false),(77,false),(78,false),(79,false),(80,true),(81,true),(92,true)]
theorem inputList6001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6001 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause6001 (by decide) v hb
mask_input "6001|1057810092233169272078336|4955386934600364987120615424"
def inputClause6002 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,false),(80,true),(81,true),(92,true)]
theorem inputList6002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6002 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause6002 (by decide) v hb
mask_input "6002|1057810092233169272045568|4955386934600364987120648192"
def inputClause6004 : CNF.NClause := [(46,false),(15,true),(77,true),(78,false),(79,false),(80,true),(81,true),(92,true)]
theorem inputList6004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6004 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause6004 (by decide) v hb
mask_input "6004|906694364781340625207296|4955538050327816815767486464"
def inputClause6005 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(79,false),(80,true),(81,true),(92,true)]
theorem inputList6005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6005 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause6005 (by decide) v hb
mask_input "6005|755578637329511978401792|4955689166055268644414291968"
def inputClause6006 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(79,false),(80,true),(81,true),(92,true)]
theorem inputList6006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6006 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause6006 (by decide) v hb
mask_input "6006|755578637329511978369024|4955689166055268644414324736"
def inputClause6007 : CNF.NClause := [(46,false),(15,false),(77,true),(78,true),(79,false),(80,true),(81,true),(92,true)]
theorem inputList6007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6007 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause6007 (by decide) v hb
mask_input "6007|604462909877683331563520|4955840281782720473061130240"
end Percolation.MaskChain
