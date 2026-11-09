import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause997 : CNF.NClause := [(77,true),(15,false),(16,false),(17,true),(18,false),(19,false),(30,true)]
theorem inputList997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause997 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) inputClause997 (by decide) v hb
mask_input "997|884736|151115727451829720711168"
def inputClause998 : CNF.NClause := [(77,true),(15,true),(16,false),(17,true),(18,false),(19,false),(30,true)]
theorem inputList998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause998 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) inputClause998 (by decide) v hb
mask_input "998|851968|151115727451829720743936"
def inputClause999 : CNF.NClause := [(77,true),(15,false),(16,true),(17,true),(18,false),(19,false),(30,true)]
theorem inputList999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause999 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) inputClause999 (by decide) v hb
mask_input "999|819200|151115727451829720776704"
def inputClause1000 : CNF.NClause := [(77,true),(15,true),(16,true),(17,true),(18,false),(19,false),(30,true)]
theorem inputList1000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1000 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) inputClause1000 (by decide) v hb
mask_input "1000|786432|151115727451829720809472"
def inputClause1001 : CNF.NClause := [(77,true),(15,false),(16,false),(17,false),(18,true),(19,false),(30,true)]
theorem inputList1001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1001 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) inputClause1001 (by decide) v hb
mask_input "1001|753664|151115727451829720842240"
def inputClause1002 : CNF.NClause := [(77,true),(15,true),(16,false),(17,false),(18,true),(19,false),(30,true)]
theorem inputList1002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1002 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) inputClause1002 (by decide) v hb
mask_input "1002|720896|151115727451829720875008"
def inputClause1003 : CNF.NClause := [(77,true),(15,false),(16,true),(17,false),(18,true),(19,false),(30,true)]
theorem inputList1003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1003 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) inputClause1003 (by decide) v hb
mask_input "1003|688128|151115727451829720907776"
def inputClause1004 : CNF.NClause := [(77,true),(15,true),(16,true),(17,false),(18,true),(19,false),(30,true)]
theorem inputList1004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1004 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) inputClause1004 (by decide) v hb
mask_input "1004|655360|151115727451829720940544"
def inputClause1005 : CNF.NClause := [(77,true),(15,false),(16,false),(17,true),(18,true),(19,false),(30,true)]
theorem inputList1005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1005 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) inputClause1005 (by decide) v hb
mask_input "1005|622592|151115727451829720973312"
def inputClause1006 : CNF.NClause := [(77,true),(15,true),(16,false),(17,true),(18,true),(19,false),(30,true)]
theorem inputList1006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1006 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) inputClause1006 (by decide) v hb
mask_input "1006|589824|151115727451829721006080"
def inputClause1007 : CNF.NClause := [(77,true),(15,false),(16,true),(17,true),(18,true),(19,false),(30,true)]
theorem inputList1007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1007 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) inputClause1007 (by decide) v hb
mask_input "1007|557056|151115727451829721038848"
def inputClause1008 : CNF.NClause := [(77,false),(15,true),(16,true),(17,true),(18,true),(19,false),(30,true)]
theorem inputList1008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1008 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) inputClause1008 (by decide) v hb
mask_input "1008|151115727451828647362560|1074233344"
def inputClause1009 : CNF.NClause := [(77,true),(15,false),(16,false),(17,false),(18,false),(19,true),(30,true)]
theorem inputList1009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1009 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) inputClause1009 (by decide) v hb
mask_input "1009|491520|151115727451829721104384"
def inputClause1010 : CNF.NClause := [(77,true),(15,true),(16,false),(17,false),(18,false),(19,true),(30,true)]
theorem inputList1010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1010 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) inputClause1010 (by decide) v hb
mask_input "1010|458752|151115727451829721137152"
def inputClause1011 : CNF.NClause := [(77,true),(15,false),(16,true),(17,false),(18,false),(19,true),(30,true)]
theorem inputList1011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1011 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) inputClause1011 (by decide) v hb
mask_input "1011|425984|151115727451829721169920"
def inputClause1012 : CNF.NClause := [(77,true),(15,true),(16,true),(17,false),(18,false),(19,true),(30,true)]
theorem inputList1012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1012 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) inputClause1012 (by decide) v hb
mask_input "1012|393216|151115727451829721202688"
def inputClause1013 : CNF.NClause := [(77,true),(15,false),(16,false),(17,true),(18,false),(19,true),(30,true)]
theorem inputList1013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1013 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) inputClause1013 (by decide) v hb
mask_input "1013|360448|151115727451829721235456"
def inputClause1014 : CNF.NClause := [(77,true),(15,true),(16,false),(17,true),(18,false),(19,true),(30,true)]
theorem inputList1014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1014 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) inputClause1014 (by decide) v hb
mask_input "1014|327680|151115727451829721268224"
def inputClause1015 : CNF.NClause := [(77,true),(15,false),(16,true),(17,true),(18,false),(19,true),(30,true)]
theorem inputList1015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1015 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) inputClause1015 (by decide) v hb
mask_input "1015|294912|151115727451829721300992"
def inputClause1016 : CNF.NClause := [(77,false),(15,true),(16,true),(17,true),(18,false),(19,true),(30,true)]
theorem inputList1016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1016 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) inputClause1016 (by decide) v hb
mask_input "1016|151115727451828647100416|1074495488"
def inputClause1017 : CNF.NClause := [(77,true),(15,false),(16,false),(17,false),(18,true),(19,true),(30,true)]
theorem inputList1017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1017 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) inputClause1017 (by decide) v hb
mask_input "1017|229376|151115727451829721366528"
def inputClause1018 : CNF.NClause := [(77,true),(15,true),(16,false),(17,false),(18,true),(19,true),(30,true)]
theorem inputList1018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1018 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) inputClause1018 (by decide) v hb
mask_input "1018|196608|151115727451829721399296"
def inputClause1019 : CNF.NClause := [(77,true),(15,false),(16,true),(17,false),(18,true),(19,true),(30,true)]
theorem inputList1019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1019 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) inputClause1019 (by decide) v hb
mask_input "1019|163840|151115727451829721432064"
def inputClause1020 : CNF.NClause := [(77,false),(15,true),(16,true),(17,false),(18,true),(19,true),(30,true)]
theorem inputList1020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1020 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) inputClause1020 (by decide) v hb
mask_input "1020|151115727451828646969344|1074626560"
def inputClause1021 : CNF.NClause := [(77,true),(15,false),(16,false),(17,true),(18,true),(19,true),(30,true)]
theorem inputList1021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1021 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) inputClause1021 (by decide) v hb
mask_input "1021|98304|151115727451829721497600"
def inputClause1022 : CNF.NClause := [(77,false),(15,true),(16,false),(17,true),(18,true),(19,true),(30,true)]
theorem inputList1022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1022 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) inputClause1022 (by decide) v hb
mask_input "1022|151115727451828646903808|1074692096"
def inputClause1023 : CNF.NClause := [(77,false),(15,false),(16,true),(17,true),(18,true),(19,true),(30,true)]
theorem inputList1023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1023 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) inputClause1023 (by decide) v hb
mask_input "1023|151115727451828646871040|1074724864"
def inputClause1024 : CNF.NClause := [(77,false),(15,true),(16,true),(17,true),(18,true),(19,true),(30,true)]
theorem inputList1024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1024 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) inputClause1024 (by decide) v hb
mask_input "1024|151115727451828646838272|1074757632"
def inputClause1025 : CNF.NClause := [(78,true),(4,false),(6,false),(13,false),(15,false),(22,false),(27,false)]
theorem inputList1025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1025 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1025 (by decide) v hb
mask_input "1025|138453072|302231454903657293676544"
def inputClause1026 : CNF.NClause := [(78,true),(4,true),(6,false),(13,false),(15,false),(22,false),(27,false)]
theorem inputList1026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1026 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1026 (by decide) v hb
mask_input "1026|138453056|302231454903657293676560"
def inputClause1027 : CNF.NClause := [(78,true),(4,false),(6,true),(13,false),(15,false),(22,false),(27,false)]
theorem inputList1027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1027 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1027 (by decide) v hb
mask_input "1027|138453008|302231454903657293676608"
def inputClause1028 : CNF.NClause := [(78,true),(4,true),(6,true),(13,false),(15,false),(22,false),(27,false)]
theorem inputList1028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1028 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1028 (by decide) v hb
mask_input "1028|138452992|302231454903657293676624"
def inputClause1029 : CNF.NClause := [(78,true),(4,false),(6,false),(13,true),(15,false),(22,false),(27,false)]
theorem inputList1029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1029 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1029 (by decide) v hb
mask_input "1029|138444880|302231454903657293684736"
def inputClause1030 : CNF.NClause := [(78,true),(4,true),(6,false),(13,true),(15,false),(22,false),(27,false)]
theorem inputList1030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1030 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1030 (by decide) v hb
mask_input "1030|138444864|302231454903657293684752"
def inputClause1031 : CNF.NClause := [(78,true),(4,false),(6,true),(13,true),(15,false),(22,false),(27,false)]
theorem inputList1031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1031 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1031 (by decide) v hb
mask_input "1031|138444816|302231454903657293684800"
def inputClause1032 : CNF.NClause := [(78,true),(4,true),(6,true),(13,true),(15,false),(22,false),(27,false)]
theorem inputList1032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1032 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1032 (by decide) v hb
mask_input "1032|138444800|302231454903657293684816"
def inputClause1033 : CNF.NClause := [(78,true),(4,false),(6,false),(13,false),(15,true),(22,false),(27,false)]
theorem inputList1033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1033 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1033 (by decide) v hb
mask_input "1033|138420304|302231454903657293709312"
def inputClause1034 : CNF.NClause := [(78,true),(4,true),(6,false),(13,false),(15,true),(22,false),(27,false)]
theorem inputList1034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1034 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1034 (by decide) v hb
mask_input "1034|138420288|302231454903657293709328"
def inputClause1035 : CNF.NClause := [(78,true),(4,false),(6,true),(13,false),(15,true),(22,false),(27,false)]
theorem inputList1035 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1035 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1035 (by decide) v hb
mask_input "1035|138420240|302231454903657293709376"
def inputClause1036 : CNF.NClause := [(78,true),(4,true),(6,true),(13,false),(15,true),(22,false),(27,false)]
theorem inputList1036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1036 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1036 (by decide) v hb
mask_input "1036|138420224|302231454903657293709392"
end Percolation.MaskChain
