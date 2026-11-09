import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause34 : CNF.NClause := [(62,true),(25,true),(26,false),(27,false),(28,false),(29,false),(30,true)]
theorem inputList34 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause34 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 0) 0) (activationA_mem 0) inputClause34 (by decide) v hb
mask_input "34|1006632960|4611686019534684160"
def inputClause36 : CNF.NClause := [(62,true),(25,true),(26,true),(27,false),(28,false),(29,false),(30,true)]
theorem inputList36 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause36 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 0) 0) (activationA_mem 0) inputClause36 (by decide) v hb
mask_input "36|939524096|4611686019601793024"
def inputClause38 : CNF.NClause := [(62,true),(25,true),(26,false),(27,true),(28,false),(29,false),(30,true)]
theorem inputList38 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause38 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 0) 0) (activationA_mem 0) inputClause38 (by decide) v hb
mask_input "38|872415232|4611686019668901888"
def inputClause40 : CNF.NClause := [(62,true),(25,true),(26,true),(27,true),(28,false),(29,false),(30,true)]
theorem inputList40 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause40 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 0) 0) (activationA_mem 0) inputClause40 (by decide) v hb
mask_input "40|805306368|4611686019736010752"
def inputClause42 : CNF.NClause := [(62,true),(25,true),(26,false),(27,false),(28,true),(29,false),(30,true)]
theorem inputList42 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause42 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 0) 0) (activationA_mem 0) inputClause42 (by decide) v hb
mask_input "42|738197504|4611686019803119616"
def inputClause44 : CNF.NClause := [(62,true),(25,true),(26,true),(27,false),(28,true),(29,false),(30,true)]
theorem inputList44 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause44 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 0) 0) (activationA_mem 0) inputClause44 (by decide) v hb
mask_input "44|671088640|4611686019870228480"
def inputClause46 : CNF.NClause := [(62,true),(25,true),(26,false),(27,true),(28,true),(29,false),(30,true)]
theorem inputList46 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause46 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 0) 0) (activationA_mem 0) inputClause46 (by decide) v hb
mask_input "46|603979776|4611686019937337344"
def inputClause48 : CNF.NClause := [(62,false),(25,true),(26,true),(27,true),(28,true),(29,false),(30,true)]
theorem inputList48 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause48 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 0) 0) (activationA_mem 0) inputClause48 (by decide) v hb
mask_input "48|4611686018964258816|1577058304"
def inputClause50 : CNF.NClause := [(62,true),(25,true),(26,false),(27,false),(28,false),(29,true),(30,true)]
theorem inputList50 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause50 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 0) 0) (activationA_mem 0) inputClause50 (by decide) v hb
mask_input "50|469762048|4611686020071555072"
def inputClause52 : CNF.NClause := [(62,true),(25,true),(26,true),(27,false),(28,false),(29,true),(30,true)]
theorem inputList52 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause52 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 0) 0) (activationA_mem 0) inputClause52 (by decide) v hb
mask_input "52|402653184|4611686020138663936"
def inputClause54 : CNF.NClause := [(62,true),(25,true),(26,false),(27,true),(28,false),(29,true),(30,true)]
theorem inputList54 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause54 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 0) 0) (activationA_mem 0) inputClause54 (by decide) v hb
mask_input "54|335544320|4611686020205772800"
def inputClause56 : CNF.NClause := [(62,false),(25,true),(26,true),(27,true),(28,false),(29,true),(30,true)]
theorem inputList56 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause56 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 0) 0) (activationA_mem 0) inputClause56 (by decide) v hb
mask_input "56|4611686018695823360|1845493760"
def inputClause58 : CNF.NClause := [(62,true),(25,true),(26,false),(27,false),(28,true),(29,true),(30,true)]
theorem inputList58 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause58 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 0) 0) (activationA_mem 0) inputClause58 (by decide) v hb
mask_input "58|201326592|4611686020339990528"
def inputClause60 : CNF.NClause := [(62,false),(25,true),(26,true),(27,false),(28,true),(29,true),(30,true)]
theorem inputList60 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause60 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 0) 0) (activationA_mem 0) inputClause60 (by decide) v hb
mask_input "60|4611686018561605632|1979711488"
def inputClause62 : CNF.NClause := [(62,false),(25,true),(26,false),(27,true),(28,true),(29,true),(30,true)]
theorem inputList62 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause62 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 0) 0) (activationA_mem 0) inputClause62 (by decide) v hb
mask_input "62|4611686018494496768|2046820352"
def inputClause97 : CNF.NClause := [(63,true),(4,false),(9,false),(14,false),(19,false),(24,false),(25,true)]
theorem inputList97 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause97 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) inputClause97 (by decide) v hb
mask_input "97|17318416|9223372036888330240"
def inputClause98 : CNF.NClause := [(63,true),(4,true),(9,false),(14,false),(19,false),(24,false),(25,true)]
theorem inputList98 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause98 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) inputClause98 (by decide) v hb
mask_input "98|17318400|9223372036888330256"
def inputClause99 : CNF.NClause := [(63,true),(4,false),(9,true),(14,false),(19,false),(24,false),(25,true)]
theorem inputList99 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause99 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) inputClause99 (by decide) v hb
mask_input "99|17317904|9223372036888330752"
def inputClause100 : CNF.NClause := [(63,true),(4,true),(9,true),(14,false),(19,false),(24,false),(25,true)]
theorem inputList100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause100 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) inputClause100 (by decide) v hb
mask_input "100|17317888|9223372036888330768"
def inputClause101 : CNF.NClause := [(63,true),(4,false),(9,false),(14,true),(19,false),(24,false),(25,true)]
theorem inputList101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause101 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) inputClause101 (by decide) v hb
mask_input "101|17302032|9223372036888346624"
def inputClause102 : CNF.NClause := [(63,true),(4,true),(9,false),(14,true),(19,false),(24,false),(25,true)]
theorem inputList102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause102 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) inputClause102 (by decide) v hb
mask_input "102|17302016|9223372036888346640"
def inputClause103 : CNF.NClause := [(63,true),(4,false),(9,true),(14,true),(19,false),(24,false),(25,true)]
theorem inputList103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause103 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) inputClause103 (by decide) v hb
mask_input "103|17301520|9223372036888347136"
def inputClause104 : CNF.NClause := [(63,true),(4,true),(9,true),(14,true),(19,false),(24,false),(25,true)]
theorem inputList104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause104 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) inputClause104 (by decide) v hb
mask_input "104|17301504|9223372036888347152"
def inputClause105 : CNF.NClause := [(63,true),(4,false),(9,false),(14,false),(19,true),(24,false),(25,true)]
theorem inputList105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause105 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) inputClause105 (by decide) v hb
mask_input "105|16794128|9223372036888854528"
def inputClause106 : CNF.NClause := [(63,true),(4,true),(9,false),(14,false),(19,true),(24,false),(25,true)]
theorem inputList106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause106 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) inputClause106 (by decide) v hb
mask_input "106|16794112|9223372036888854544"
def inputClause107 : CNF.NClause := [(63,true),(4,false),(9,true),(14,false),(19,true),(24,false),(25,true)]
theorem inputList107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause107 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) inputClause107 (by decide) v hb
mask_input "107|16793616|9223372036888855040"
def inputClause108 : CNF.NClause := [(63,true),(4,true),(9,true),(14,false),(19,true),(24,false),(25,true)]
theorem inputList108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause108 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) inputClause108 (by decide) v hb
mask_input "108|16793600|9223372036888855056"
def inputClause109 : CNF.NClause := [(63,true),(4,false),(9,false),(14,true),(19,true),(24,false),(25,true)]
theorem inputList109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause109 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) inputClause109 (by decide) v hb
mask_input "109|16777744|9223372036888870912"
def inputClause110 : CNF.NClause := [(63,true),(4,true),(9,false),(14,true),(19,true),(24,false),(25,true)]
theorem inputList110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause110 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) inputClause110 (by decide) v hb
mask_input "110|16777728|9223372036888870928"
def inputClause111 : CNF.NClause := [(63,true),(4,false),(9,true),(14,true),(19,true),(24,false),(25,true)]
theorem inputList111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause111 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) inputClause111 (by decide) v hb
mask_input "111|16777232|9223372036888871424"
def inputClause112 : CNF.NClause := [(63,false),(4,true),(9,true),(14,true),(19,true),(24,false),(25,true)]
theorem inputList112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause112 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) inputClause112 (by decide) v hb
mask_input "112|9223372036871553024|34095632"
def inputClause113 : CNF.NClause := [(63,true),(4,false),(9,false),(14,false),(19,false),(24,true),(25,true)]
theorem inputList113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause113 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) inputClause113 (by decide) v hb
mask_input "113|541200|9223372036905107456"
def inputClause114 : CNF.NClause := [(63,true),(4,true),(9,false),(14,false),(19,false),(24,true),(25,true)]
theorem inputList114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause114 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) inputClause114 (by decide) v hb
mask_input "114|541184|9223372036905107472"
def inputClause115 : CNF.NClause := [(63,true),(4,false),(9,true),(14,false),(19,false),(24,true),(25,true)]
theorem inputList115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause115 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) inputClause115 (by decide) v hb
mask_input "115|540688|9223372036905107968"
def inputClause116 : CNF.NClause := [(63,true),(4,true),(9,true),(14,false),(19,false),(24,true),(25,true)]
theorem inputList116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause116 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) inputClause116 (by decide) v hb
mask_input "116|540672|9223372036905107984"
def inputClause117 : CNF.NClause := [(63,true),(4,false),(9,false),(14,true),(19,false),(24,true),(25,true)]
theorem inputList117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause117 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) inputClause117 (by decide) v hb
mask_input "117|524816|9223372036905123840"
def inputClause118 : CNF.NClause := [(63,true),(4,true),(9,false),(14,true),(19,false),(24,true),(25,true)]
theorem inputList118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause118 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) inputClause118 (by decide) v hb
mask_input "118|524800|9223372036905123856"
def inputClause119 : CNF.NClause := [(63,true),(4,false),(9,true),(14,true),(19,false),(24,true),(25,true)]
theorem inputList119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause119 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) inputClause119 (by decide) v hb
mask_input "119|524304|9223372036905124352"
def inputClause120 : CNF.NClause := [(63,false),(4,true),(9,true),(14,true),(19,false),(24,true),(25,true)]
theorem inputList120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause120 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) inputClause120 (by decide) v hb
mask_input "120|9223372036855300096|50348560"
def inputClause121 : CNF.NClause := [(63,true),(4,false),(9,false),(14,false),(19,true),(24,true),(25,true)]
theorem inputList121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause121 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) inputClause121 (by decide) v hb
mask_input "121|16912|9223372036905631744"
end Percolation.MaskChain
