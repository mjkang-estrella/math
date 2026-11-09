import NormalizedLink
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_34 : CNF.NClause := [(62,true),(25,true),(26,false),(27,false),(28,false),(29,false),(30,true)]
theorem inp_34 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 0) 0) (activationA_mem 0) cl_34 (by decide) v hb
def cl_36 : CNF.NClause := [(62,true),(25,true),(26,true),(27,false),(28,false),(29,false),(30,true)]
theorem inp_36 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_36 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 0) 0) (activationA_mem 0) cl_36 (by decide) v hb
def cl_38 : CNF.NClause := [(62,true),(25,true),(26,false),(27,true),(28,false),(29,false),(30,true)]
theorem inp_38 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_38 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 0) 0) (activationA_mem 0) cl_38 (by decide) v hb
def cl_40 : CNF.NClause := [(62,true),(25,true),(26,true),(27,true),(28,false),(29,false),(30,true)]
theorem inp_40 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_40 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_40 v hb
def cl_42 : CNF.NClause := [(62,true),(25,true),(26,false),(27,false),(28,true),(29,false),(30,true)]
theorem inp_42 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_42 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 0) 0) (activationA_mem 0) cl_42 (by decide) v hb
def cl_44 : CNF.NClause := [(62,true),(25,true),(26,true),(27,false),(28,true),(29,false),(30,true)]
theorem inp_44 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_44 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 0) 0) (activationA_mem 0) cl_44 (by decide) v hb
def cl_46 : CNF.NClause := [(62,true),(25,true),(26,false),(27,true),(28,true),(29,false),(30,true)]
theorem inp_46 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_46 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 0) 0) (activationA_mem 0) cl_46 (by decide) v hb
def cl_48 : CNF.NClause := [(62,false),(25,true),(26,true),(27,true),(28,true),(29,false),(30,true)]
theorem inp_48 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_48 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 0) 0) (activationA_mem 0) cl_48 (by decide) v hb
def cl_50 : CNF.NClause := [(62,true),(25,true),(26,false),(27,false),(28,false),(29,true),(30,true)]
theorem inp_50 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 0) 0) (activationA_mem 0) cl_50 (by decide) v hb
def cl_52 : CNF.NClause := [(62,true),(25,true),(26,true),(27,false),(28,false),(29,true),(30,true)]
theorem inp_52 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 0) 0) (activationA_mem 0) cl_52 (by decide) v hb
def cl_54 : CNF.NClause := [(62,true),(25,true),(26,false),(27,true),(28,false),(29,true),(30,true)]
theorem inp_54 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_54 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_54 v hb
def cl_56 : CNF.NClause := [(62,false),(25,true),(26,true),(27,true),(28,false),(29,true),(30,true)]
theorem inp_56 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_56 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 0) 0) (activationA_mem 0) cl_56 (by decide) v hb
def cl_58 : CNF.NClause := [(62,true),(25,true),(26,false),(27,false),(28,true),(29,true),(30,true)]
theorem inp_58 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_58 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 0) 0) (activationA_mem 0) cl_58 (by decide) v hb
def cl_60 : CNF.NClause := [(62,false),(25,true),(26,true),(27,false),(28,true),(29,true),(30,true)]
theorem inp_60 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_60 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 0) 0) (activationA_mem 0) cl_60 (by decide) v hb
def cl_62 : CNF.NClause := [(62,false),(25,true),(26,false),(27,true),(28,true),(29,true),(30,true)]
theorem inp_62 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 0) 0) (activationA_mem 0) cl_62 (by decide) v hb
def cl_97 : CNF.NClause := [(63,true),(4,false),(9,false),(14,false),(19,false),(24,false),(25,true)]
theorem inp_97 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_97 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_97 (by decide) v hb
def cl_98 : CNF.NClause := [(63,true),(4,true),(9,false),(14,false),(19,false),(24,false),(25,true)]
theorem inp_98 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_98 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_98 (by decide) v hb
def cl_99 : CNF.NClause := [(63,true),(4,false),(9,true),(14,false),(19,false),(24,false),(25,true)]
theorem inp_99 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_99 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_99 v hb
def cl_100 : CNF.NClause := [(63,true),(4,true),(9,true),(14,false),(19,false),(24,false),(25,true)]
theorem inp_100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_100 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_100 v hb
def cl_101 : CNF.NClause := [(63,true),(4,false),(9,false),(14,true),(19,false),(24,false),(25,true)]
theorem inp_101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_101 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_101 (by decide) v hb
def cl_102 : CNF.NClause := [(63,true),(4,true),(9,false),(14,true),(19,false),(24,false),(25,true)]
theorem inp_102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_102 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_102 (by decide) v hb
def cl_103 : CNF.NClause := [(63,true),(4,false),(9,true),(14,true),(19,false),(24,false),(25,true)]
theorem inp_103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_103 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_103 v hb
def cl_104 : CNF.NClause := [(63,true),(4,true),(9,true),(14,true),(19,false),(24,false),(25,true)]
theorem inp_104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_104 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_104 v hb
def cl_105 : CNF.NClause := [(63,true),(4,false),(9,false),(14,false),(19,true),(24,false),(25,true)]
theorem inp_105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_105 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_105 (by decide) v hb
def cl_106 : CNF.NClause := [(63,true),(4,true),(9,false),(14,false),(19,true),(24,false),(25,true)]
theorem inp_106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_106 v hb
def cl_107 : CNF.NClause := [(63,true),(4,false),(9,true),(14,false),(19,true),(24,false),(25,true)]
theorem inp_107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_107 v hb
def cl_108 : CNF.NClause := [(63,true),(4,true),(9,true),(14,false),(19,true),(24,false),(25,true)]
theorem inp_108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_108 v hb
def cl_109 : CNF.NClause := [(63,true),(4,false),(9,false),(14,true),(19,true),(24,false),(25,true)]
theorem inp_109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_109 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_109 (by decide) v hb
def cl_110 : CNF.NClause := [(63,true),(4,true),(9,false),(14,true),(19,true),(24,false),(25,true)]
theorem inp_110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_110 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_110 (by decide) v hb
def cl_111 : CNF.NClause := [(63,true),(4,false),(9,true),(14,true),(19,true),(24,false),(25,true)]
theorem inp_111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_111 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_111 v hb
def cl_112 : CNF.NClause := [(63,false),(4,true),(9,true),(14,true),(19,true),(24,false),(25,true)]
theorem inp_112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_112 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_112 v hb
def cl_113 : CNF.NClause := [(63,true),(4,false),(9,false),(14,false),(19,false),(24,true),(25,true)]
theorem inp_113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_113 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_113 (by decide) v hb
def cl_114 : CNF.NClause := [(63,true),(4,true),(9,false),(14,false),(19,false),(24,true),(25,true)]
theorem inp_114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_114 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_114 (by decide) v hb
def cl_115 : CNF.NClause := [(63,true),(4,false),(9,true),(14,false),(19,false),(24,true),(25,true)]
theorem inp_115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_115 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_115 v hb
def cl_116 : CNF.NClause := [(63,true),(4,true),(9,true),(14,false),(19,false),(24,true),(25,true)]
theorem inp_116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_116 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_116 v hb
def cl_117 : CNF.NClause := [(63,true),(4,false),(9,false),(14,true),(19,false),(24,true),(25,true)]
theorem inp_117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_117 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_117 (by decide) v hb
def cl_118 : CNF.NClause := [(63,true),(4,true),(9,false),(14,true),(19,false),(24,true),(25,true)]
theorem inp_118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_118 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_118 (by decide) v hb
def cl_119 : CNF.NClause := [(63,true),(4,false),(9,true),(14,true),(19,false),(24,true),(25,true)]
theorem inp_119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_119 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_119 v hb
def cl_120 : CNF.NClause := [(63,false),(4,true),(9,true),(14,true),(19,false),(24,true),(25,true)]
theorem inp_120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_120 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_120 v hb
def cl_121 : CNF.NClause := [(63,true),(4,false),(9,false),(14,false),(19,true),(24,true),(25,true)]
theorem inp_121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_121 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_121 (by decide) v hb
def cl_122 : CNF.NClause := [(63,true),(4,true),(9,false),(14,false),(19,true),(24,true),(25,true)]
theorem inp_122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_122 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_122 (by decide) v hb
def cl_123 : CNF.NClause := [(63,true),(4,false),(9,true),(14,false),(19,true),(24,true),(25,true)]
theorem inp_123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_123 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_123 v hb
def cl_124 : CNF.NClause := [(63,false),(4,true),(9,true),(14,false),(19,true),(24,true),(25,true)]
theorem inp_124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_124 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_124 v hb
def cl_125 : CNF.NClause := [(63,true),(4,false),(9,false),(14,true),(19,true),(24,true),(25,true)]
theorem inp_125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_125 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_125 (by decide) v hb
def cl_126 : CNF.NClause := [(63,false),(4,true),(9,false),(14,true),(19,true),(24,true),(25,true)]
theorem inp_126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_126 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_126 (by decide) v hb
def cl_127 : CNF.NClause := [(63,false),(4,false),(9,true),(14,true),(19,true),(24,true),(25,true)]
theorem inp_127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_127 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_127 v hb
def cl_128 : CNF.NClause := [(63,false),(4,true),(9,true),(14,true),(19,true),(24,true),(25,true)]
theorem inp_128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_128 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_128 v hb
def cl_161 : CNF.NClause := [(64,true),(2,false),(7,false),(12,false),(17,false),(22,false),(25,true)]
theorem inp_161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_161 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_161 v hb
def cl_162 : CNF.NClause := [(64,true),(2,true),(7,false),(12,false),(17,false),(22,false),(25,true)]
theorem inp_162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_162 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_162 v hb
def cl_163 : CNF.NClause := [(64,true),(2,false),(7,true),(12,false),(17,false),(22,false),(25,true)]
theorem inp_163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_163 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_163 v hb
end Percolation.NReplay
