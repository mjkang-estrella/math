import InputLink
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_39 : CNF.NClause := [(62,true),(25,false),(26,true),(27,true),(28,false),(29,false),(30,true)]
theorem inp_39 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_39 := by
  exact input_gate (activationGate5 SatVar.a (.i 0) 0) (activationA_mem 0) cl_39 (by decide) v h
def cl_40 : CNF.NClause := [(62,true),(25,true),(26,true),(27,true),(28,false),(29,false),(30,true)]
theorem inp_40 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_40 := by
  exact input_gate (activationGate5 SatVar.a (.i 0) 0) (activationA_mem 0) cl_40 (by decide) v h
def cl_53 : CNF.NClause := [(62,true),(25,false),(26,false),(27,true),(28,false),(29,true),(30,true)]
theorem inp_53 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_53 := by
  exact input_gate (activationGate5 SatVar.a (.i 0) 0) (activationA_mem 0) cl_53 (by decide) v h
def cl_54 : CNF.NClause := [(62,true),(25,true),(26,false),(27,true),(28,false),(29,true),(30,true)]
theorem inp_54 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_54 := by
  exact input_gate (activationGate5 SatVar.a (.i 0) 0) (activationA_mem 0) cl_54 (by decide) v h
def cl_55 : CNF.NClause := [(62,true),(25,false),(26,true),(27,true),(28,false),(29,true),(30,true)]
theorem inp_55 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_55 := by
  exact input_gate (activationGate5 SatVar.a (.i 0) 0) (activationA_mem 0) cl_55 (by decide) v h
def cl_65 : CNF.NClause := [(63,true),(4,false),(9,false),(14,false),(19,false),(24,false),(25,false)]
theorem inp_65 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_65 (by decide) v h
def cl_66 : CNF.NClause := [(63,true),(4,true),(9,false),(14,false),(19,false),(24,false),(25,false)]
theorem inp_66 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_66 (by decide) v h
def cl_67 : CNF.NClause := [(63,true),(4,false),(9,true),(14,false),(19,false),(24,false),(25,false)]
theorem inp_67 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_67 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_67 (by decide) v h
def cl_68 : CNF.NClause := [(63,true),(4,true),(9,true),(14,false),(19,false),(24,false),(25,false)]
theorem inp_68 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_68 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_68 (by decide) v h
def cl_71 : CNF.NClause := [(63,true),(4,false),(9,true),(14,true),(19,false),(24,false),(25,false)]
theorem inp_71 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_71 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_71 (by decide) v h
def cl_72 : CNF.NClause := [(63,true),(4,true),(9,true),(14,true),(19,false),(24,false),(25,false)]
theorem inp_72 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_72 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_72 (by decide) v h
def cl_74 : CNF.NClause := [(63,true),(4,true),(9,false),(14,false),(19,true),(24,false),(25,false)]
theorem inp_74 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_74 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_74 (by decide) v h
def cl_75 : CNF.NClause := [(63,true),(4,false),(9,true),(14,false),(19,true),(24,false),(25,false)]
theorem inp_75 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_75 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_75 (by decide) v h
def cl_76 : CNF.NClause := [(63,true),(4,true),(9,true),(14,false),(19,true),(24,false),(25,false)]
theorem inp_76 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_76 (by decide) v h
def cl_78 : CNF.NClause := [(63,true),(4,true),(9,false),(14,true),(19,true),(24,false),(25,false)]
theorem inp_78 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_78 (by decide) v h
def cl_79 : CNF.NClause := [(63,true),(4,false),(9,true),(14,true),(19,true),(24,false),(25,false)]
theorem inp_79 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_79 (by decide) v h
def cl_80 : CNF.NClause := [(63,true),(4,true),(9,true),(14,true),(19,true),(24,false),(25,false)]
theorem inp_80 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_80 (by decide) v h
def cl_83 : CNF.NClause := [(63,true),(4,false),(9,true),(14,false),(19,false),(24,true),(25,false)]
theorem inp_83 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_83 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_83 (by decide) v h
def cl_84 : CNF.NClause := [(63,true),(4,true),(9,true),(14,false),(19,false),(24,true),(25,false)]
theorem inp_84 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_84 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_84 (by decide) v h
def cl_87 : CNF.NClause := [(63,true),(4,false),(9,true),(14,true),(19,false),(24,true),(25,false)]
theorem inp_87 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_87 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_87 (by decide) v h
def cl_88 : CNF.NClause := [(63,true),(4,true),(9,true),(14,true),(19,false),(24,true),(25,false)]
theorem inp_88 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_88 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_88 (by decide) v h
def cl_91 : CNF.NClause := [(63,true),(4,false),(9,true),(14,false),(19,true),(24,true),(25,false)]
theorem inp_91 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_91 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_91 (by decide) v h
def cl_92 : CNF.NClause := [(63,true),(4,true),(9,true),(14,false),(19,true),(24,true),(25,false)]
theorem inp_92 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_92 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_92 (by decide) v h
def cl_95 : CNF.NClause := [(63,true),(4,false),(9,true),(14,true),(19,true),(24,true),(25,false)]
theorem inp_95 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_95 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_95 (by decide) v h
def cl_99 : CNF.NClause := [(63,true),(4,false),(9,true),(14,false),(19,false),(24,false),(25,true)]
theorem inp_99 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_99 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_99 (by decide) v h
def cl_100 : CNF.NClause := [(63,true),(4,true),(9,true),(14,false),(19,false),(24,false),(25,true)]
theorem inp_100 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_100 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_100 (by decide) v h
def cl_103 : CNF.NClause := [(63,true),(4,false),(9,true),(14,true),(19,false),(24,false),(25,true)]
theorem inp_103 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_103 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_103 (by decide) v h
def cl_104 : CNF.NClause := [(63,true),(4,true),(9,true),(14,true),(19,false),(24,false),(25,true)]
theorem inp_104 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_104 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_104 (by decide) v h
def cl_106 : CNF.NClause := [(63,true),(4,true),(9,false),(14,false),(19,true),(24,false),(25,true)]
theorem inp_106 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_106 (by decide) v h
def cl_107 : CNF.NClause := [(63,true),(4,false),(9,true),(14,false),(19,true),(24,false),(25,true)]
theorem inp_107 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_107 (by decide) v h
def cl_108 : CNF.NClause := [(63,true),(4,true),(9,true),(14,false),(19,true),(24,false),(25,true)]
theorem inp_108 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_108 (by decide) v h
def cl_111 : CNF.NClause := [(63,true),(4,false),(9,true),(14,true),(19,true),(24,false),(25,true)]
theorem inp_111 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_111 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_111 (by decide) v h
def cl_112 : CNF.NClause := [(63,false),(4,true),(9,true),(14,true),(19,true),(24,false),(25,true)]
theorem inp_112 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_112 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_112 (by decide) v h
def cl_115 : CNF.NClause := [(63,true),(4,false),(9,true),(14,false),(19,false),(24,true),(25,true)]
theorem inp_115 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_115 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_115 (by decide) v h
def cl_116 : CNF.NClause := [(63,true),(4,true),(9,true),(14,false),(19,false),(24,true),(25,true)]
theorem inp_116 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_116 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_116 (by decide) v h
def cl_119 : CNF.NClause := [(63,true),(4,false),(9,true),(14,true),(19,false),(24,true),(25,true)]
theorem inp_119 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_119 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_119 (by decide) v h
def cl_120 : CNF.NClause := [(63,false),(4,true),(9,true),(14,true),(19,false),(24,true),(25,true)]
theorem inp_120 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_120 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_120 (by decide) v h
def cl_123 : CNF.NClause := [(63,true),(4,false),(9,true),(14,false),(19,true),(24,true),(25,true)]
theorem inp_123 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_123 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_123 (by decide) v h
def cl_124 : CNF.NClause := [(63,false),(4,true),(9,true),(14,false),(19,true),(24,true),(25,true)]
theorem inp_124 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_124 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_124 (by decide) v h
def cl_127 : CNF.NClause := [(63,false),(4,false),(9,true),(14,true),(19,true),(24,true),(25,true)]
theorem inp_127 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_127 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_127 (by decide) v h
def cl_128 : CNF.NClause := [(63,false),(4,true),(9,true),(14,true),(19,true),(24,true),(25,true)]
theorem inp_128 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_128 := by
  exact input_gate (activationGate5 SatVar.a (.i 1) 1) (activationA_mem 1) cl_128 (by decide) v h
def cl_129 : CNF.NClause := [(64,true),(2,false),(7,false),(12,false),(17,false),(22,false),(25,false)]
theorem inp_129 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_129 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_129 (by decide) v h
def cl_130 : CNF.NClause := [(64,true),(2,true),(7,false),(12,false),(17,false),(22,false),(25,false)]
theorem inp_130 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_130 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_130 (by decide) v h
def cl_131 : CNF.NClause := [(64,true),(2,false),(7,true),(12,false),(17,false),(22,false),(25,false)]
theorem inp_131 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_131 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_131 (by decide) v h
def cl_132 : CNF.NClause := [(64,true),(2,true),(7,true),(12,false),(17,false),(22,false),(25,false)]
theorem inp_132 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_132 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_132 (by decide) v h
def cl_133 : CNF.NClause := [(64,true),(2,false),(7,false),(12,true),(17,false),(22,false),(25,false)]
theorem inp_133 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_133 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_133 (by decide) v h
def cl_134 : CNF.NClause := [(64,true),(2,true),(7,false),(12,true),(17,false),(22,false),(25,false)]
theorem inp_134 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_134 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_134 (by decide) v h
def cl_135 : CNF.NClause := [(64,true),(2,false),(7,true),(12,true),(17,false),(22,false),(25,false)]
theorem inp_135 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_135 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_135 (by decide) v h
def cl_136 : CNF.NClause := [(64,true),(2,true),(7,true),(12,true),(17,false),(22,false),(25,false)]
theorem inp_136 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_136 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_136 (by decide) v h
def cl_137 : CNF.NClause := [(64,true),(2,false),(7,false),(12,false),(17,true),(22,false),(25,false)]
theorem inp_137 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_137 := by
  exact input_gate (activationGate5 SatVar.a (.i 2) 2) (activationA_mem 2) cl_137 (by decide) v h
end Percolation.Replay
