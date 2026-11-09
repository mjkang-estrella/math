import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause1037 : CNF.NClause := [(78,true),(4,false),(6,false),(13,true),(15,true),(22,false),(27,false)]
theorem inputList1037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1037 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1037 (by decide) v hb
mask_input "1037|138412112|302231454903657293717504"
def inputClause1038 : CNF.NClause := [(78,true),(4,true),(6,false),(13,true),(15,true),(22,false),(27,false)]
theorem inputList1038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1038 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1038 (by decide) v hb
mask_input "1038|138412096|302231454903657293717520"
def inputClause1039 : CNF.NClause := [(78,true),(4,false),(6,true),(13,true),(15,true),(22,false),(27,false)]
theorem inputList1039 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1039 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1039 (by decide) v hb
mask_input "1039|138412048|302231454903657293717568"
def inputClause1040 : CNF.NClause := [(78,true),(4,true),(6,true),(13,true),(15,true),(22,false),(27,false)]
theorem inputList1040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1040 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1040 (by decide) v hb
mask_input "1040|138412032|302231454903657293717584"
def inputClause1041 : CNF.NClause := [(78,true),(4,false),(6,false),(13,false),(15,false),(22,true),(27,false)]
theorem inputList1041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1041 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1041 (by decide) v hb
mask_input "1041|134258768|302231454903657297870848"
def inputClause1042 : CNF.NClause := [(78,true),(4,true),(6,false),(13,false),(15,false),(22,true),(27,false)]
theorem inputList1042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1042 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1042 (by decide) v hb
mask_input "1042|134258752|302231454903657297870864"
def inputClause1043 : CNF.NClause := [(78,true),(4,false),(6,true),(13,false),(15,false),(22,true),(27,false)]
theorem inputList1043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1043 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1043 (by decide) v hb
mask_input "1043|134258704|302231454903657297870912"
def inputClause1044 : CNF.NClause := [(78,true),(4,true),(6,true),(13,false),(15,false),(22,true),(27,false)]
theorem inputList1044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1044 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1044 (by decide) v hb
mask_input "1044|134258688|302231454903657297870928"
def inputClause1045 : CNF.NClause := [(78,true),(4,false),(6,false),(13,true),(15,false),(22,true),(27,false)]
theorem inputList1045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1045 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1045 (by decide) v hb
mask_input "1045|134250576|302231454903657297879040"
def inputClause1046 : CNF.NClause := [(78,true),(4,true),(6,false),(13,true),(15,false),(22,true),(27,false)]
theorem inputList1046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1046 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1046 (by decide) v hb
mask_input "1046|134250560|302231454903657297879056"
def inputClause1047 : CNF.NClause := [(78,true),(4,false),(6,true),(13,true),(15,false),(22,true),(27,false)]
theorem inputList1047 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1047 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1047 (by decide) v hb
mask_input "1047|134250512|302231454903657297879104"
def inputClause1048 : CNF.NClause := [(78,true),(4,true),(6,true),(13,true),(15,false),(22,true),(27,false)]
theorem inputList1048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1048 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1048 (by decide) v hb
mask_input "1048|134250496|302231454903657297879120"
def inputClause1049 : CNF.NClause := [(78,true),(4,false),(6,false),(13,false),(15,true),(22,true),(27,false)]
theorem inputList1049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1049 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1049 (by decide) v hb
mask_input "1049|134226000|302231454903657297903616"
def inputClause1050 : CNF.NClause := [(78,true),(4,true),(6,false),(13,false),(15,true),(22,true),(27,false)]
theorem inputList1050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1050 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1050 (by decide) v hb
mask_input "1050|134225984|302231454903657297903632"
def inputClause1051 : CNF.NClause := [(78,true),(4,false),(6,true),(13,false),(15,true),(22,true),(27,false)]
theorem inputList1051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1051 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1051 (by decide) v hb
mask_input "1051|134225936|302231454903657297903680"
def inputClause1052 : CNF.NClause := [(78,true),(4,true),(6,true),(13,false),(15,true),(22,true),(27,false)]
theorem inputList1052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1052 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1052 (by decide) v hb
mask_input "1052|134225920|302231454903657297903696"
def inputClause1053 : CNF.NClause := [(78,true),(4,false),(6,false),(13,true),(15,true),(22,true),(27,false)]
theorem inputList1053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1053 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1053 (by decide) v hb
mask_input "1053|134217808|302231454903657297911808"
def inputClause1054 : CNF.NClause := [(78,true),(4,true),(6,false),(13,true),(15,true),(22,true),(27,false)]
theorem inputList1054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1054 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1054 (by decide) v hb
mask_input "1054|134217792|302231454903657297911824"
def inputClause1055 : CNF.NClause := [(78,true),(4,false),(6,true),(13,true),(15,true),(22,true),(27,false)]
theorem inputList1055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1055 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1055 (by decide) v hb
mask_input "1055|134217744|302231454903657297911872"
def inputClause1056 : CNF.NClause := [(78,false),(4,true),(6,true),(13,true),(15,true),(22,true),(27,false)]
theorem inputList1056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1056 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1056 (by decide) v hb
mask_input "1056|302231454903657427894272|4235344"
def inputClause1057 : CNF.NClause := [(78,true),(4,false),(6,false),(13,false),(15,false),(22,false),(27,true)]
theorem inputList1057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1057 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1057 (by decide) v hb
mask_input "1057|4235344|302231454903657427894272"
def inputClause1058 : CNF.NClause := [(78,true),(4,true),(6,false),(13,false),(15,false),(22,false),(27,true)]
theorem inputList1058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1058 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1058 (by decide) v hb
mask_input "1058|4235328|302231454903657427894288"
def inputClause1059 : CNF.NClause := [(78,true),(4,false),(6,true),(13,false),(15,false),(22,false),(27,true)]
theorem inputList1059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1059 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1059 (by decide) v hb
mask_input "1059|4235280|302231454903657427894336"
def inputClause1060 : CNF.NClause := [(78,true),(4,true),(6,true),(13,false),(15,false),(22,false),(27,true)]
theorem inputList1060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1060 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1060 (by decide) v hb
mask_input "1060|4235264|302231454903657427894352"
def inputClause1061 : CNF.NClause := [(78,true),(4,false),(6,false),(13,true),(15,false),(22,false),(27,true)]
theorem inputList1061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1061 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1061 (by decide) v hb
mask_input "1061|4227152|302231454903657427902464"
def inputClause1062 : CNF.NClause := [(78,true),(4,true),(6,false),(13,true),(15,false),(22,false),(27,true)]
theorem inputList1062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1062 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1062 (by decide) v hb
mask_input "1062|4227136|302231454903657427902480"
def inputClause1063 : CNF.NClause := [(78,true),(4,false),(6,true),(13,true),(15,false),(22,false),(27,true)]
theorem inputList1063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1063 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1063 (by decide) v hb
mask_input "1063|4227088|302231454903657427902528"
def inputClause1064 : CNF.NClause := [(78,true),(4,true),(6,true),(13,true),(15,false),(22,false),(27,true)]
theorem inputList1064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1064 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1064 (by decide) v hb
mask_input "1064|4227072|302231454903657427902544"
def inputClause1065 : CNF.NClause := [(78,true),(4,false),(6,false),(13,false),(15,true),(22,false),(27,true)]
theorem inputList1065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1065 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1065 (by decide) v hb
mask_input "1065|4202576|302231454903657427927040"
def inputClause1066 : CNF.NClause := [(78,true),(4,true),(6,false),(13,false),(15,true),(22,false),(27,true)]
theorem inputList1066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1066 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1066 (by decide) v hb
mask_input "1066|4202560|302231454903657427927056"
def inputClause1067 : CNF.NClause := [(78,true),(4,false),(6,true),(13,false),(15,true),(22,false),(27,true)]
theorem inputList1067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1067 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1067 (by decide) v hb
mask_input "1067|4202512|302231454903657427927104"
def inputClause1068 : CNF.NClause := [(78,true),(4,true),(6,true),(13,false),(15,true),(22,false),(27,true)]
theorem inputList1068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1068 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1068 (by decide) v hb
mask_input "1068|4202496|302231454903657427927120"
def inputClause1069 : CNF.NClause := [(78,true),(4,false),(6,false),(13,true),(15,true),(22,false),(27,true)]
theorem inputList1069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1069 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1069 (by decide) v hb
mask_input "1069|4194384|302231454903657427935232"
def inputClause1070 : CNF.NClause := [(78,true),(4,true),(6,false),(13,true),(15,true),(22,false),(27,true)]
theorem inputList1070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1070 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1070 (by decide) v hb
mask_input "1070|4194368|302231454903657427935248"
def inputClause1071 : CNF.NClause := [(78,true),(4,false),(6,true),(13,true),(15,true),(22,false),(27,true)]
theorem inputList1071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1071 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1071 (by decide) v hb
mask_input "1071|4194320|302231454903657427935296"
def inputClause1073 : CNF.NClause := [(78,true),(4,false),(6,false),(13,false),(15,false),(22,true),(27,true)]
theorem inputList1073 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1073 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1073 (by decide) v hb
mask_input "1073|41040|302231454903657432088576"
def inputClause1074 : CNF.NClause := [(78,true),(4,true),(6,false),(13,false),(15,false),(22,true),(27,true)]
theorem inputList1074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1074 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1074 (by decide) v hb
mask_input "1074|41024|302231454903657432088592"
def inputClause1075 : CNF.NClause := [(78,true),(4,false),(6,true),(13,false),(15,false),(22,true),(27,true)]
theorem inputList1075 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1075 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1075 (by decide) v hb
mask_input "1075|40976|302231454903657432088640"
def inputClause1076 : CNF.NClause := [(78,true),(4,true),(6,true),(13,false),(15,false),(22,true),(27,true)]
theorem inputList1076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1076 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1076 (by decide) v hb
mask_input "1076|40960|302231454903657432088656"
def inputClause1077 : CNF.NClause := [(78,true),(4,false),(6,false),(13,true),(15,false),(22,true),(27,true)]
theorem inputList1077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1077 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) inputClause1077 (by decide) v hb
mask_input "1077|32848|302231454903657432096768"
end Percolation.MaskChain
