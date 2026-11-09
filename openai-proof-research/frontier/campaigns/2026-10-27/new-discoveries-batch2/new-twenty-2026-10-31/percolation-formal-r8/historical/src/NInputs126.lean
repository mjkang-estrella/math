import NInputs125
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_7115 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,true),(80,false),(84,false),(91,true)]
theorem inp_7115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7115 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7115 (by decide) v hb
def cl_7116 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,true),(80,false),(84,false),(91,true)]
theorem inp_7116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7116 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7116 (by decide) v hb
def cl_7117 : CNF.NClause := [(55,false),(24,false),(63,false),(67,true),(76,true),(80,false),(84,false),(91,true)]
theorem inp_7117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7117 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7117 (by decide) v hb
def cl_7118 : CNF.NClause := [(55,false),(24,true),(63,false),(67,true),(76,true),(80,false),(84,false),(91,true)]
theorem inp_7118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7118 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7118 (by decide) v hb
def cl_7119 : CNF.NClause := [(55,false),(24,false),(63,true),(67,true),(76,true),(80,false),(84,false),(91,true)]
theorem inp_7119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7119 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7119 (by decide) v hb
def cl_7120 : CNF.NClause := [(55,false),(24,true),(63,true),(67,true),(76,true),(80,false),(84,false),(91,true)]
theorem inp_7120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7120 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7120 (by decide) v hb
def cl_7121 : CNF.NClause := [(55,false),(24,false),(63,false),(67,false),(76,false),(80,true),(84,false),(91,true)]
theorem inp_7121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7121 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7121 (by decide) v hb
def cl_7122 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(76,false),(80,true),(84,false),(91,true)]
theorem inp_7122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7122 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7122 (by decide) v hb
def cl_7123 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,false),(80,true),(84,false),(91,true)]
theorem inp_7123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7123 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7123 (by decide) v hb
def cl_7124 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,false),(80,true),(84,false),(91,true)]
theorem inp_7124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7124 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7124 (by decide) v hb
def cl_7125 : CNF.NClause := [(55,false),(24,false),(63,false),(67,true),(76,false),(80,true),(84,false),(91,true)]
theorem inp_7125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7125 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7125 (by decide) v hb
def cl_7126 : CNF.NClause := [(55,false),(24,true),(63,false),(67,true),(76,false),(80,true),(84,false),(91,true)]
theorem inp_7126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7126 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7126 (by decide) v hb
def cl_7127 : CNF.NClause := [(55,false),(24,false),(63,true),(67,true),(76,false),(80,true),(84,false),(91,true)]
theorem inp_7127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7127 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7127 (by decide) v hb
def cl_7128 : CNF.NClause := [(55,false),(24,true),(63,true),(67,true),(76,false),(80,true),(84,false),(91,true)]
theorem inp_7128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7128 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7128 (by decide) v hb
def cl_7129 : CNF.NClause := [(55,false),(24,false),(63,false),(67,false),(76,true),(80,true),(84,false),(91,true)]
theorem inp_7129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7129 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7129 (by decide) v hb
def cl_7130 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(76,true),(80,true),(84,false),(91,true)]
theorem inp_7130 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7130 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7130 (by decide) v hb
def cl_7131 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,true),(80,true),(84,false),(91,true)]
theorem inp_7131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7131 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7131 (by decide) v hb
def cl_7132 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,true),(80,true),(84,false),(91,true)]
theorem inp_7132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7132 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7132 (by decide) v hb
def cl_7133 : CNF.NClause := [(55,false),(24,false),(63,false),(67,true),(76,true),(80,true),(84,false),(91,true)]
theorem inp_7133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7133 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7133 (by decide) v hb
def cl_7134 : CNF.NClause := [(55,false),(24,true),(63,false),(67,true),(76,true),(80,true),(84,false),(91,true)]
theorem inp_7134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7134 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7134 (by decide) v hb
def cl_7135 : CNF.NClause := [(55,false),(24,false),(63,true),(67,true),(76,true),(80,true),(84,false),(91,true)]
theorem inp_7135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7135 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7135 (by decide) v hb
def cl_7136 : CNF.NClause := [(55,false),(24,true),(63,true),(67,true),(76,true),(80,true),(84,false),(91,true)]
theorem inp_7136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7136 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7136 (by decide) v hb
def cl_7137 : CNF.NClause := [(55,false),(24,false),(63,false),(67,false),(76,false),(80,false),(84,true),(91,true)]
theorem inp_7137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7137 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7137 (by decide) v hb
def cl_7138 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(76,false),(80,false),(84,true),(91,true)]
theorem inp_7138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7138 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7138 (by decide) v hb
def cl_7139 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,false),(80,false),(84,true),(91,true)]
theorem inp_7139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7139 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7139 (by decide) v hb
def cl_7140 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,false),(80,false),(84,true),(91,true)]
theorem inp_7140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7140 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7140 (by decide) v hb
def cl_7141 : CNF.NClause := [(55,false),(24,false),(63,false),(67,true),(76,false),(80,false),(84,true),(91,true)]
theorem inp_7141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7141 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7141 (by decide) v hb
def cl_7142 : CNF.NClause := [(55,false),(24,true),(63,false),(67,true),(76,false),(80,false),(84,true),(91,true)]
theorem inp_7142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7142 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7142 (by decide) v hb
def cl_7143 : CNF.NClause := [(55,false),(24,false),(63,true),(67,true),(76,false),(80,false),(84,true),(91,true)]
theorem inp_7143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7143 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7143 (by decide) v hb
def cl_7144 : CNF.NClause := [(55,false),(24,true),(63,true),(67,true),(76,false),(80,false),(84,true),(91,true)]
theorem inp_7144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7144 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7144 (by decide) v hb
def cl_7146 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(76,true),(80,false),(84,true),(91,true)]
theorem inp_7146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7146 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7146 (by decide) v hb
def cl_7147 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,true),(80,false),(84,true),(91,true)]
theorem inp_7147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7147 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7147 (by decide) v hb
def cl_7148 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,true),(80,false),(84,true),(91,true)]
theorem inp_7148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7148 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7148 (by decide) v hb
def cl_7149 : CNF.NClause := [(55,false),(24,false),(63,false),(67,true),(76,true),(80,false),(84,true),(91,true)]
theorem inp_7149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7149 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7149 (by decide) v hb
def cl_7150 : CNF.NClause := [(55,false),(24,true),(63,false),(67,true),(76,true),(80,false),(84,true),(91,true)]
theorem inp_7150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7150 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7150 (by decide) v hb
def cl_7151 : CNF.NClause := [(55,false),(24,false),(63,true),(67,true),(76,true),(80,false),(84,true),(91,true)]
theorem inp_7151 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7151 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7151 (by decide) v hb
def cl_7152 : CNF.NClause := [(55,false),(24,true),(63,true),(67,true),(76,true),(80,false),(84,true),(91,true)]
theorem inp_7152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7152 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7152 (by decide) v hb
def cl_7153 : CNF.NClause := [(55,false),(24,false),(63,false),(67,false),(76,false),(80,true),(84,true),(91,true)]
theorem inp_7153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7153 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7153 (by decide) v hb
def cl_7154 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(76,false),(80,true),(84,true),(91,true)]
theorem inp_7154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7154 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7154 (by decide) v hb
def cl_7155 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,false),(80,true),(84,true),(91,true)]
theorem inp_7155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7155 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7155 (by decide) v hb
def cl_7156 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,false),(80,true),(84,true),(91,true)]
theorem inp_7156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7156 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7156 (by decide) v hb
def cl_7158 : CNF.NClause := [(55,false),(24,true),(63,false),(67,true),(76,false),(80,true),(84,true),(91,true)]
theorem inp_7158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7158 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7158 (by decide) v hb
def cl_7160 : CNF.NClause := [(55,false),(24,true),(63,true),(67,true),(76,false),(80,true),(84,true),(91,true)]
theorem inp_7160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7160 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7160 (by decide) v hb
def cl_7161 : CNF.NClause := [(55,false),(24,false),(63,false),(67,false),(76,true),(80,true),(84,true),(91,true)]
theorem inp_7161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7161 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7161 (by decide) v hb
def cl_7162 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(76,true),(80,true),(84,true),(91,true)]
theorem inp_7162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7162 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7162 (by decide) v hb
def cl_7163 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,true),(80,true),(84,true),(91,true)]
theorem inp_7163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7163 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7163 (by decide) v hb
def cl_7164 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,true),(80,true),(84,true),(91,true)]
theorem inp_7164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7164 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7164 (by decide) v hb
def cl_7165 : CNF.NClause := [(55,false),(24,false),(63,false),(67,true),(76,true),(80,true),(84,true),(91,true)]
theorem inp_7165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7165 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7165 (by decide) v hb
def cl_7166 : CNF.NClause := [(55,false),(24,true),(63,false),(67,true),(76,true),(80,true),(84,true),(91,true)]
theorem inp_7166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7166 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7166 (by decide) v hb
def cl_7168 : CNF.NClause := [(55,false),(24,true),(63,true),(67,true),(76,true),(80,true),(84,true),(91,true)]
theorem inp_7168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7168 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7168 (by decide) v hb
end Percolation.NReplay
