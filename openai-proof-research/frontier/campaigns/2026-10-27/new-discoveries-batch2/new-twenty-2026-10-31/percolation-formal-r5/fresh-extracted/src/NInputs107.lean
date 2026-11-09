import NInputs106
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_6125 : CNF.NClause := [(47,false),(16,false),(66,false),(68,true),(75,true),(77,false),(84,true),(89,true)]
theorem inp_6125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6125 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6125 (by decide) v hb
def cl_6126 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true),(75,true),(77,false),(84,true),(89,true)]
theorem inp_6126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6126 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6126 (by decide) v hb
def cl_6127 : CNF.NClause := [(47,false),(16,false),(66,true),(68,true),(75,true),(77,false),(84,true),(89,true)]
theorem inp_6127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6127 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6127 (by decide) v hb
def cl_6128 : CNF.NClause := [(47,false),(16,true),(66,true),(68,true),(75,true),(77,false),(84,true),(89,true)]
theorem inp_6128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6128 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6128 (by decide) v hb
def cl_6129 : CNF.NClause := [(47,false),(16,false),(66,false),(68,false),(75,false),(77,true),(84,true),(89,true)]
theorem inp_6129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6129 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6129 (by decide) v hb
def cl_6130 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,false),(77,true),(84,true),(89,true)]
theorem inp_6130 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6130 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6130 (by decide) v hb
def cl_6131 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(75,false),(77,true),(84,true),(89,true)]
theorem inp_6131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6131 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6131 (by decide) v hb
def cl_6132 : CNF.NClause := [(47,false),(16,true),(66,true),(68,false),(75,false),(77,true),(84,true),(89,true)]
theorem inp_6132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6132 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6132 (by decide) v hb
def cl_6133 : CNF.NClause := [(47,false),(16,false),(66,false),(68,true),(75,false),(77,true),(84,true),(89,true)]
theorem inp_6133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6133 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6133 (by decide) v hb
def cl_6134 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true),(75,false),(77,true),(84,true),(89,true)]
theorem inp_6134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6134 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6134 (by decide) v hb
def cl_6136 : CNF.NClause := [(47,false),(16,true),(66,true),(68,true),(75,false),(77,true),(84,true),(89,true)]
theorem inp_6136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6136 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6136 (by decide) v hb
def cl_6137 : CNF.NClause := [(47,false),(16,false),(66,false),(68,false),(75,true),(77,true),(84,true),(89,true)]
theorem inp_6137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6137 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6137 (by decide) v hb
def cl_6138 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,true),(77,true),(84,true),(89,true)]
theorem inp_6138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6138 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6138 v hb
def cl_6139 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(75,true),(77,true),(84,true),(89,true)]
theorem inp_6139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6139 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6139 (by decide) v hb
def cl_6140 : CNF.NClause := [(47,false),(16,true),(66,true),(68,false),(75,true),(77,true),(84,true),(89,true)]
theorem inp_6140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6140 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6140 (by decide) v hb
def cl_6141 : CNF.NClause := [(47,false),(16,false),(66,false),(68,true),(75,true),(77,true),(84,true),(89,true)]
theorem inp_6141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6141 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6141 (by decide) v hb
def cl_6142 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true),(75,true),(77,true),(84,true),(89,true)]
theorem inp_6142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6142 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6142 (by decide) v hb
def cl_6143 : CNF.NClause := [(47,false),(16,false),(66,true),(68,true),(75,true),(77,true),(84,true),(89,true)]
theorem inp_6143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6143 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6143 v hb
def cl_6144 : CNF.NClause := [(47,false),(16,true),(66,true),(68,true),(75,true),(77,true),(84,true),(89,true)]
theorem inp_6144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6144 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6144 v hb
def cl_6145 : CNF.NClause := [(48,true),(17,false),(64,false),(70,false),(76,false),(77,false),(83,false),(88,false)]
theorem inp_6145 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6145 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6145 (by decide) v hb
def cl_6146 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,false),(77,false),(83,false),(88,false)]
theorem inp_6146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6146 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6146 v hb
def cl_6147 : CNF.NClause := [(48,false),(17,false),(64,true),(70,false),(76,false),(77,false),(83,false),(88,false)]
theorem inp_6147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6147 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6147 (by decide) v hb
def cl_6148 : CNF.NClause := [(48,false),(17,true),(64,true),(70,false),(76,false),(77,false),(83,false),(88,false)]
theorem inp_6148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6148 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6148 (by decide) v hb
def cl_6149 : CNF.NClause := [(48,false),(17,false),(64,false),(70,true),(76,false),(77,false),(83,false),(88,false)]
theorem inp_6149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6149 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6149 (by decide) v hb
def cl_6150 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,false),(77,false),(83,false),(88,false)]
theorem inp_6150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6150 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6150 v hb
def cl_6151 : CNF.NClause := [(48,false),(17,false),(64,true),(70,true),(76,false),(77,false),(83,false),(88,false)]
theorem inp_6151 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6151 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6151 (by decide) v hb
def cl_6152 : CNF.NClause := [(48,false),(17,true),(64,true),(70,true),(76,false),(77,false),(83,false),(88,false)]
theorem inp_6152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6152 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6152 (by decide) v hb
def cl_6153 : CNF.NClause := [(48,false),(17,false),(64,false),(70,false),(76,true),(77,false),(83,false),(88,false)]
theorem inp_6153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6153 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6153 v hb
def cl_6154 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,true),(77,false),(83,false),(88,false)]
theorem inp_6154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6154 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6154 v hb
def cl_6155 : CNF.NClause := [(48,false),(17,false),(64,true),(70,false),(76,true),(77,false),(83,false),(88,false)]
theorem inp_6155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6155 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6155 (by decide) v hb
def cl_6156 : CNF.NClause := [(48,false),(17,true),(64,true),(70,false),(76,true),(77,false),(83,false),(88,false)]
theorem inp_6156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6156 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6156 (by decide) v hb
def cl_6157 : CNF.NClause := [(48,false),(17,false),(64,false),(70,true),(76,true),(77,false),(83,false),(88,false)]
theorem inp_6157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6157 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6157 (by decide) v hb
def cl_6158 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,true),(77,false),(83,false),(88,false)]
theorem inp_6158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6158 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6158 (by decide) v hb
def cl_6159 : CNF.NClause := [(48,false),(17,false),(64,true),(70,true),(76,true),(77,false),(83,false),(88,false)]
theorem inp_6159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6159 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6159 (by decide) v hb
def cl_6160 : CNF.NClause := [(48,false),(17,true),(64,true),(70,true),(76,true),(77,false),(83,false),(88,false)]
theorem inp_6160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6160 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6160 (by decide) v hb
def cl_6161 : CNF.NClause := [(48,false),(17,false),(64,false),(70,false),(76,false),(77,true),(83,false),(88,false)]
theorem inp_6161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6161 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6161 (by decide) v hb
def cl_6162 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,false),(77,true),(83,false),(88,false)]
theorem inp_6162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6162 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6162 (by decide) v hb
def cl_6163 : CNF.NClause := [(48,false),(17,false),(64,true),(70,false),(76,false),(77,true),(83,false),(88,false)]
theorem inp_6163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6163 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6163 (by decide) v hb
def cl_6164 : CNF.NClause := [(48,false),(17,true),(64,true),(70,false),(76,false),(77,true),(83,false),(88,false)]
theorem inp_6164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6164 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6164 (by decide) v hb
def cl_6165 : CNF.NClause := [(48,false),(17,false),(64,false),(70,true),(76,false),(77,true),(83,false),(88,false)]
theorem inp_6165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6165 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6165 (by decide) v hb
def cl_6166 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,false),(77,true),(83,false),(88,false)]
theorem inp_6166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6166 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6166 (by decide) v hb
def cl_6167 : CNF.NClause := [(48,false),(17,false),(64,true),(70,true),(76,false),(77,true),(83,false),(88,false)]
theorem inp_6167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6167 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6167 (by decide) v hb
def cl_6168 : CNF.NClause := [(48,false),(17,true),(64,true),(70,true),(76,false),(77,true),(83,false),(88,false)]
theorem inp_6168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6168 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6168 (by decide) v hb
def cl_6169 : CNF.NClause := [(48,false),(17,false),(64,false),(70,false),(76,true),(77,true),(83,false),(88,false)]
theorem inp_6169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6169 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6169 (by decide) v hb
def cl_6170 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,true),(77,true),(83,false),(88,false)]
theorem inp_6170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6170 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6170 (by decide) v hb
def cl_6171 : CNF.NClause := [(48,false),(17,false),(64,true),(70,false),(76,true),(77,true),(83,false),(88,false)]
theorem inp_6171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6171 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6171 (by decide) v hb
def cl_6172 : CNF.NClause := [(48,false),(17,true),(64,true),(70,false),(76,true),(77,true),(83,false),(88,false)]
theorem inp_6172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6172 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6172 (by decide) v hb
def cl_6173 : CNF.NClause := [(48,false),(17,false),(64,false),(70,true),(76,true),(77,true),(83,false),(88,false)]
theorem inp_6173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6173 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6173 (by decide) v hb
def cl_6174 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,true),(77,true),(83,false),(88,false)]
theorem inp_6174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6174 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6174 (by decide) v hb
def cl_6175 : CNF.NClause := [(48,false),(17,false),(64,true),(70,true),(76,true),(77,true),(83,false),(88,false)]
theorem inp_6175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6175 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6175 (by decide) v hb
end Percolation.NReplay
