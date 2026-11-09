import NInputs013
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_944 : CNF.NClause := [(76,false),(1,true),(8,true),(10,true),(17,true),(24,false),(27,true)]
theorem inp_944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_944 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_944 v hb
def cl_945 : CNF.NClause := [(76,true),(1,false),(8,false),(10,false),(17,false),(24,true),(27,true)]
theorem inp_945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_945 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_945 (by decide) v hb
def cl_946 : CNF.NClause := [(76,true),(1,true),(8,false),(10,false),(17,false),(24,true),(27,true)]
theorem inp_946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_946 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_946 (by decide) v hb
def cl_947 : CNF.NClause := [(76,true),(1,false),(8,true),(10,false),(17,false),(24,true),(27,true)]
theorem inp_947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_947 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_947 v hb
def cl_948 : CNF.NClause := [(76,true),(1,true),(8,true),(10,false),(17,false),(24,true),(27,true)]
theorem inp_948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_948 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_948 v hb
def cl_949 : CNF.NClause := [(76,true),(1,false),(8,false),(10,true),(17,false),(24,true),(27,true)]
theorem inp_949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_949 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_949 (by decide) v hb
def cl_950 : CNF.NClause := [(76,true),(1,true),(8,false),(10,true),(17,false),(24,true),(27,true)]
theorem inp_950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_950 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_950 (by decide) v hb
def cl_951 : CNF.NClause := [(76,true),(1,false),(8,true),(10,true),(17,false),(24,true),(27,true)]
theorem inp_951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_951 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_951 v hb
def cl_952 : CNF.NClause := [(76,false),(1,true),(8,true),(10,true),(17,false),(24,true),(27,true)]
theorem inp_952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_952 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_952 v hb
def cl_953 : CNF.NClause := [(76,true),(1,false),(8,false),(10,false),(17,true),(24,true),(27,true)]
theorem inp_953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_953 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_953 v hb
def cl_954 : CNF.NClause := [(76,true),(1,true),(8,false),(10,false),(17,true),(24,true),(27,true)]
theorem inp_954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_954 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_954 (by decide) v hb
def cl_955 : CNF.NClause := [(76,true),(1,false),(8,true),(10,false),(17,true),(24,true),(27,true)]
theorem inp_955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_955 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_955 v hb
def cl_956 : CNF.NClause := [(76,false),(1,true),(8,true),(10,false),(17,true),(24,true),(27,true)]
theorem inp_956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_956 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_956 v hb
def cl_957 : CNF.NClause := [(76,true),(1,false),(8,false),(10,true),(17,true),(24,true),(27,true)]
theorem inp_957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_957 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_957 v hb
def cl_958 : CNF.NClause := [(76,false),(1,true),(8,false),(10,true),(17,true),(24,true),(27,true)]
theorem inp_958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_958 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_958 v hb
def cl_959 : CNF.NClause := [(76,false),(1,false),(8,true),(10,true),(17,true),(24,true),(27,true)]
theorem inp_959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_959 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_959 v hb
def cl_960 : CNF.NClause := [(76,false),(1,true),(8,true),(10,true),(17,true),(24,true),(27,true)]
theorem inp_960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_960 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_960 v hb
def cl_993 : CNF.NClause := [(77,true),(15,false),(16,false),(17,false),(18,false),(19,false),(30,true)]
theorem inp_993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_993 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_993 (by decide) v hb
def cl_994 : CNF.NClause := [(77,true),(15,true),(16,false),(17,false),(18,false),(19,false),(30,true)]
theorem inp_994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_994 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_994 (by decide) v hb
def cl_995 : CNF.NClause := [(77,true),(15,false),(16,true),(17,false),(18,false),(19,false),(30,true)]
theorem inp_995 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_995 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_995 v hb
def cl_996 : CNF.NClause := [(77,true),(15,true),(16,true),(17,false),(18,false),(19,false),(30,true)]
theorem inp_996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_996 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_996 v hb
def cl_997 : CNF.NClause := [(77,true),(15,false),(16,false),(17,true),(18,false),(19,false),(30,true)]
theorem inp_997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_997 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_997 v hb
def cl_998 : CNF.NClause := [(77,true),(15,true),(16,false),(17,true),(18,false),(19,false),(30,true)]
theorem inp_998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_998 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_998 (by decide) v hb
def cl_999 : CNF.NClause := [(77,true),(15,false),(16,true),(17,true),(18,false),(19,false),(30,true)]
theorem inp_999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_999 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_999 v hb
def cl_1000 : CNF.NClause := [(77,true),(15,true),(16,true),(17,true),(18,false),(19,false),(30,true)]
theorem inp_1000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1000 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1000 v hb
def cl_1001 : CNF.NClause := [(77,true),(15,false),(16,false),(17,false),(18,true),(19,false),(30,true)]
theorem inp_1001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1001 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_1001 (by decide) v hb
def cl_1002 : CNF.NClause := [(77,true),(15,true),(16,false),(17,false),(18,true),(19,false),(30,true)]
theorem inp_1002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1002 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_1002 (by decide) v hb
def cl_1003 : CNF.NClause := [(77,true),(15,false),(16,true),(17,false),(18,true),(19,false),(30,true)]
theorem inp_1003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1003 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1003 v hb
def cl_1004 : CNF.NClause := [(77,true),(15,true),(16,true),(17,false),(18,true),(19,false),(30,true)]
theorem inp_1004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1004 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1004 v hb
def cl_1005 : CNF.NClause := [(77,true),(15,false),(16,false),(17,true),(18,true),(19,false),(30,true)]
theorem inp_1005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1005 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1005 v hb
def cl_1006 : CNF.NClause := [(77,true),(15,true),(16,false),(17,true),(18,true),(19,false),(30,true)]
theorem inp_1006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1006 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_1006 (by decide) v hb
def cl_1007 : CNF.NClause := [(77,true),(15,false),(16,true),(17,true),(18,true),(19,false),(30,true)]
theorem inp_1007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1007 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_1007 (by decide) v hb
def cl_1008 : CNF.NClause := [(77,false),(15,true),(16,true),(17,true),(18,true),(19,false),(30,true)]
theorem inp_1008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1008 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1008 v hb
def cl_1009 : CNF.NClause := [(77,true),(15,false),(16,false),(17,false),(18,false),(19,true),(30,true)]
theorem inp_1009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1009 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1009 v hb
def cl_1010 : CNF.NClause := [(77,true),(15,true),(16,false),(17,false),(18,false),(19,true),(30,true)]
theorem inp_1010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1010 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_1010 (by decide) v hb
def cl_1011 : CNF.NClause := [(77,true),(15,false),(16,true),(17,false),(18,false),(19,true),(30,true)]
theorem inp_1011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1011 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1011 v hb
def cl_1012 : CNF.NClause := [(77,true),(15,true),(16,true),(17,false),(18,false),(19,true),(30,true)]
theorem inp_1012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1012 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1012 v hb
def cl_1013 : CNF.NClause := [(77,true),(15,false),(16,false),(17,true),(18,false),(19,true),(30,true)]
theorem inp_1013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1013 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1013 v hb
def cl_1014 : CNF.NClause := [(77,true),(15,true),(16,false),(17,true),(18,false),(19,true),(30,true)]
theorem inp_1014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1014 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_1014 (by decide) v hb
def cl_1015 : CNF.NClause := [(77,true),(15,false),(16,true),(17,true),(18,false),(19,true),(30,true)]
theorem inp_1015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1015 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1015 v hb
def cl_1016 : CNF.NClause := [(77,false),(15,true),(16,true),(17,true),(18,false),(19,true),(30,true)]
theorem inp_1016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1016 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1016 v hb
def cl_1017 : CNF.NClause := [(77,true),(15,false),(16,false),(17,false),(18,true),(19,true),(30,true)]
theorem inp_1017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1017 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_1017 (by decide) v hb
def cl_1018 : CNF.NClause := [(77,true),(15,true),(16,false),(17,false),(18,true),(19,true),(30,true)]
theorem inp_1018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1018 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_1018 (by decide) v hb
def cl_1019 : CNF.NClause := [(77,true),(15,false),(16,true),(17,false),(18,true),(19,true),(30,true)]
theorem inp_1019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1019 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1019 v hb
def cl_1020 : CNF.NClause := [(77,false),(15,true),(16,true),(17,false),(18,true),(19,true),(30,true)]
theorem inp_1020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1020 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1020 v hb
def cl_1021 : CNF.NClause := [(77,true),(15,false),(16,false),(17,true),(18,true),(19,true),(30,true)]
theorem inp_1021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1021 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1021 v hb
def cl_1022 : CNF.NClause := [(77,false),(15,true),(16,false),(17,true),(18,true),(19,true),(30,true)]
theorem inp_1022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1022 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1022 v hb
def cl_1023 : CNF.NClause := [(77,false),(15,false),(16,true),(17,true),(18,true),(19,true),(30,true)]
theorem inp_1023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1023 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1023 v hb
def cl_1024 : CNF.NClause := [(77,false),(15,true),(16,true),(17,true),(18,true),(19,true),(30,true)]
theorem inp_1024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1024 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1024 v hb
def cl_1025 : CNF.NClause := [(78,true),(4,false),(6,false),(13,false),(15,false),(22,false),(27,false)]
theorem inp_1025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1025 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_1025 v hb
end Percolation.NReplay
