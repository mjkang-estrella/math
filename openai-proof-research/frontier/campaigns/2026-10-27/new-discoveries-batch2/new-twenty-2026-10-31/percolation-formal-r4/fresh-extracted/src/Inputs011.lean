import Inputs010
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_995 : CNF.NClause := [(77,true),(15,false),(16,true),(17,false),(18,false),(19,false),(30,true)]
theorem inp_995 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_995 := by
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_995 (by decide) v h
def cl_996 : CNF.NClause := [(77,true),(15,true),(16,true),(17,false),(18,false),(19,false),(30,true)]
theorem inp_996 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_996 := by
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_996 (by decide) v h
def cl_997 : CNF.NClause := [(77,true),(15,false),(16,false),(17,true),(18,false),(19,false),(30,true)]
theorem inp_997 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_997 := by
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_997 (by decide) v h
def cl_999 : CNF.NClause := [(77,true),(15,false),(16,true),(17,true),(18,false),(19,false),(30,true)]
theorem inp_999 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_999 := by
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_999 (by decide) v h
def cl_1000 : CNF.NClause := [(77,true),(15,true),(16,true),(17,true),(18,false),(19,false),(30,true)]
theorem inp_1000 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1000 := by
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_1000 (by decide) v h
def cl_1003 : CNF.NClause := [(77,true),(15,false),(16,true),(17,false),(18,true),(19,false),(30,true)]
theorem inp_1003 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1003 := by
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_1003 (by decide) v h
def cl_1004 : CNF.NClause := [(77,true),(15,true),(16,true),(17,false),(18,true),(19,false),(30,true)]
theorem inp_1004 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1004 := by
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_1004 (by decide) v h
def cl_1005 : CNF.NClause := [(77,true),(15,false),(16,false),(17,true),(18,true),(19,false),(30,true)]
theorem inp_1005 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1005 := by
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_1005 (by decide) v h
def cl_1008 : CNF.NClause := [(77,false),(15,true),(16,true),(17,true),(18,true),(19,false),(30,true)]
theorem inp_1008 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1008 := by
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_1008 (by decide) v h
def cl_1009 : CNF.NClause := [(77,true),(15,false),(16,false),(17,false),(18,false),(19,true),(30,true)]
theorem inp_1009 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1009 := by
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_1009 (by decide) v h
def cl_1011 : CNF.NClause := [(77,true),(15,false),(16,true),(17,false),(18,false),(19,true),(30,true)]
theorem inp_1011 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1011 := by
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_1011 (by decide) v h
def cl_1012 : CNF.NClause := [(77,true),(15,true),(16,true),(17,false),(18,false),(19,true),(30,true)]
theorem inp_1012 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1012 := by
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_1012 (by decide) v h
def cl_1013 : CNF.NClause := [(77,true),(15,false),(16,false),(17,true),(18,false),(19,true),(30,true)]
theorem inp_1013 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1013 := by
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_1013 (by decide) v h
def cl_1015 : CNF.NClause := [(77,true),(15,false),(16,true),(17,true),(18,false),(19,true),(30,true)]
theorem inp_1015 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1015 := by
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_1015 (by decide) v h
def cl_1016 : CNF.NClause := [(77,false),(15,true),(16,true),(17,true),(18,false),(19,true),(30,true)]
theorem inp_1016 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1016 := by
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_1016 (by decide) v h
def cl_1019 : CNF.NClause := [(77,true),(15,false),(16,true),(17,false),(18,true),(19,true),(30,true)]
theorem inp_1019 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1019 := by
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_1019 (by decide) v h
def cl_1020 : CNF.NClause := [(77,false),(15,true),(16,true),(17,false),(18,true),(19,true),(30,true)]
theorem inp_1020 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1020 := by
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_1020 (by decide) v h
def cl_1021 : CNF.NClause := [(77,true),(15,false),(16,false),(17,true),(18,true),(19,true),(30,true)]
theorem inp_1021 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1021 := by
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_1021 (by decide) v h
def cl_1022 : CNF.NClause := [(77,false),(15,true),(16,false),(17,true),(18,true),(19,true),(30,true)]
theorem inp_1022 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1022 := by
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_1022 (by decide) v h
def cl_1023 : CNF.NClause := [(77,false),(15,false),(16,true),(17,true),(18,true),(19,true),(30,true)]
theorem inp_1023 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1023 := by
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_1023 (by decide) v h
def cl_1024 : CNF.NClause := [(77,false),(15,true),(16,true),(17,true),(18,true),(19,true),(30,true)]
theorem inp_1024 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1024 := by
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_1024 (by decide) v h
def cl_1025 : CNF.NClause := [(78,true),(4,false),(6,false),(13,false),(15,false),(22,false),(27,false)]
theorem inp_1025 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1025 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1025 (by decide) v h
def cl_1026 : CNF.NClause := [(78,true),(4,true),(6,false),(13,false),(15,false),(22,false),(27,false)]
theorem inp_1026 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1026 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1026 (by decide) v h
def cl_1027 : CNF.NClause := [(78,true),(4,false),(6,true),(13,false),(15,false),(22,false),(27,false)]
theorem inp_1027 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1027 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1027 (by decide) v h
def cl_1028 : CNF.NClause := [(78,true),(4,true),(6,true),(13,false),(15,false),(22,false),(27,false)]
theorem inp_1028 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1028 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1028 (by decide) v h
def cl_1029 : CNF.NClause := [(78,true),(4,false),(6,false),(13,true),(15,false),(22,false),(27,false)]
theorem inp_1029 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1029 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1029 (by decide) v h
def cl_1030 : CNF.NClause := [(78,true),(4,true),(6,false),(13,true),(15,false),(22,false),(27,false)]
theorem inp_1030 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1030 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1030 (by decide) v h
def cl_1031 : CNF.NClause := [(78,true),(4,false),(6,true),(13,true),(15,false),(22,false),(27,false)]
theorem inp_1031 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1031 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1031 (by decide) v h
def cl_1034 : CNF.NClause := [(78,true),(4,true),(6,false),(13,false),(15,true),(22,false),(27,false)]
theorem inp_1034 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1034 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1034 (by decide) v h
def cl_1037 : CNF.NClause := [(78,true),(4,false),(6,false),(13,true),(15,true),(22,false),(27,false)]
theorem inp_1037 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1037 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1037 (by decide) v h
def cl_1038 : CNF.NClause := [(78,true),(4,true),(6,false),(13,true),(15,true),(22,false),(27,false)]
theorem inp_1038 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1038 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1038 (by decide) v h
def cl_1042 : CNF.NClause := [(78,true),(4,true),(6,false),(13,false),(15,false),(22,true),(27,false)]
theorem inp_1042 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1042 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1042 (by decide) v h
def cl_1045 : CNF.NClause := [(78,true),(4,false),(6,false),(13,true),(15,false),(22,true),(27,false)]
theorem inp_1045 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1045 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1045 (by decide) v h
def cl_1046 : CNF.NClause := [(78,true),(4,true),(6,false),(13,true),(15,false),(22,true),(27,false)]
theorem inp_1046 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1046 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1046 (by decide) v h
def cl_1047 : CNF.NClause := [(78,true),(4,false),(6,true),(13,true),(15,false),(22,true),(27,false)]
theorem inp_1047 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1047 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1047 (by decide) v h
def cl_1050 : CNF.NClause := [(78,true),(4,true),(6,false),(13,false),(15,true),(22,true),(27,false)]
theorem inp_1050 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1050 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1050 (by decide) v h
def cl_1053 : CNF.NClause := [(78,true),(4,false),(6,false),(13,true),(15,true),(22,true),(27,false)]
theorem inp_1053 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1053 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1053 (by decide) v h
def cl_1054 : CNF.NClause := [(78,true),(4,true),(6,false),(13,true),(15,true),(22,true),(27,false)]
theorem inp_1054 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1054 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1054 (by decide) v h
def cl_1056 : CNF.NClause := [(78,false),(4,true),(6,true),(13,true),(15,true),(22,true),(27,false)]
theorem inp_1056 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1056 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1056 (by decide) v h
def cl_1057 : CNF.NClause := [(78,true),(4,false),(6,false),(13,false),(15,false),(22,false),(27,true)]
theorem inp_1057 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1057 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1057 (by decide) v h
def cl_1058 : CNF.NClause := [(78,true),(4,true),(6,false),(13,false),(15,false),(22,false),(27,true)]
theorem inp_1058 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1058 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1058 (by decide) v h
def cl_1059 : CNF.NClause := [(78,true),(4,false),(6,true),(13,false),(15,false),(22,false),(27,true)]
theorem inp_1059 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1059 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1059 (by decide) v h
def cl_1060 : CNF.NClause := [(78,true),(4,true),(6,true),(13,false),(15,false),(22,false),(27,true)]
theorem inp_1060 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1060 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1060 (by decide) v h
def cl_1061 : CNF.NClause := [(78,true),(4,false),(6,false),(13,true),(15,false),(22,false),(27,true)]
theorem inp_1061 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1061 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1061 (by decide) v h
def cl_1062 : CNF.NClause := [(78,true),(4,true),(6,false),(13,true),(15,false),(22,false),(27,true)]
theorem inp_1062 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1062 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1062 (by decide) v h
def cl_1063 : CNF.NClause := [(78,true),(4,false),(6,true),(13,true),(15,false),(22,false),(27,true)]
theorem inp_1063 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1063 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1063 (by decide) v h
def cl_1064 : CNF.NClause := [(78,true),(4,true),(6,true),(13,true),(15,false),(22,false),(27,true)]
theorem inp_1064 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1064 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1064 (by decide) v h
def cl_1065 : CNF.NClause := [(78,true),(4,false),(6,false),(13,false),(15,true),(22,false),(27,true)]
theorem inp_1065 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1065 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1065 (by decide) v h
def cl_1066 : CNF.NClause := [(78,true),(4,true),(6,false),(13,false),(15,true),(22,false),(27,true)]
theorem inp_1066 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1066 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1066 (by decide) v h
def cl_1067 : CNF.NClause := [(78,true),(4,false),(6,true),(13,false),(15,true),(22,false),(27,true)]
theorem inp_1067 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1067 := by
  exact input_gate (activationGate5 SatVar.a (.i 16) 16) (activationA_mem 16) cl_1067 (by decide) v h
end Percolation.Replay
