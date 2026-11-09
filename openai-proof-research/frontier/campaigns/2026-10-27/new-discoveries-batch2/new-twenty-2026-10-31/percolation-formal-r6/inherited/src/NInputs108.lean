import NInputs107
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_6176 : CNF.NClause := [(48,false),(17,true),(64,true),(70,true),(76,true),(77,true),(83,false),(88,false)]
theorem inp_6176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6176 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6176 (by decide) v hb
def cl_6177 : CNF.NClause := [(48,false),(17,false),(64,false),(70,false),(76,false),(77,false),(83,true),(88,false)]
theorem inp_6177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6177 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6177 (by decide) v hb
def cl_6178 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,false),(77,false),(83,true),(88,false)]
theorem inp_6178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6178 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6178 v hb
def cl_6179 : CNF.NClause := [(48,false),(17,false),(64,true),(70,false),(76,false),(77,false),(83,true),(88,false)]
theorem inp_6179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6179 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6179 (by decide) v hb
def cl_6180 : CNF.NClause := [(48,false),(17,true),(64,true),(70,false),(76,false),(77,false),(83,true),(88,false)]
theorem inp_6180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6180 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6180 (by decide) v hb
def cl_6181 : CNF.NClause := [(48,false),(17,false),(64,false),(70,true),(76,false),(77,false),(83,true),(88,false)]
theorem inp_6181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6181 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6181 (by decide) v hb
def cl_6182 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,false),(77,false),(83,true),(88,false)]
theorem inp_6182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6182 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6182 (by decide) v hb
def cl_6183 : CNF.NClause := [(48,false),(17,false),(64,true),(70,true),(76,false),(77,false),(83,true),(88,false)]
theorem inp_6183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6183 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6183 (by decide) v hb
def cl_6184 : CNF.NClause := [(48,false),(17,true),(64,true),(70,true),(76,false),(77,false),(83,true),(88,false)]
theorem inp_6184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6184 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6184 (by decide) v hb
def cl_6185 : CNF.NClause := [(48,false),(17,false),(64,false),(70,false),(76,true),(77,false),(83,true),(88,false)]
theorem inp_6185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6185 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6185 (by decide) v hb
def cl_6186 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,true),(77,false),(83,true),(88,false)]
theorem inp_6186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6186 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6186 v hb
def cl_6187 : CNF.NClause := [(48,false),(17,false),(64,true),(70,false),(76,true),(77,false),(83,true),(88,false)]
theorem inp_6187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6187 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6187 (by decide) v hb
def cl_6188 : CNF.NClause := [(48,false),(17,true),(64,true),(70,false),(76,true),(77,false),(83,true),(88,false)]
theorem inp_6188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6188 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6188 (by decide) v hb
def cl_6189 : CNF.NClause := [(48,false),(17,false),(64,false),(70,true),(76,true),(77,false),(83,true),(88,false)]
theorem inp_6189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6189 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6189 (by decide) v hb
def cl_6190 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,true),(77,false),(83,true),(88,false)]
theorem inp_6190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6190 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6190 (by decide) v hb
def cl_6191 : CNF.NClause := [(48,false),(17,false),(64,true),(70,true),(76,true),(77,false),(83,true),(88,false)]
theorem inp_6191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6191 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6191 (by decide) v hb
def cl_6192 : CNF.NClause := [(48,false),(17,true),(64,true),(70,true),(76,true),(77,false),(83,true),(88,false)]
theorem inp_6192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6192 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6192 (by decide) v hb
def cl_6193 : CNF.NClause := [(48,false),(17,false),(64,false),(70,false),(76,false),(77,true),(83,true),(88,false)]
theorem inp_6193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6193 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6193 (by decide) v hb
def cl_6194 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,false),(77,true),(83,true),(88,false)]
theorem inp_6194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6194 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6194 (by decide) v hb
def cl_6195 : CNF.NClause := [(48,false),(17,false),(64,true),(70,false),(76,false),(77,true),(83,true),(88,false)]
theorem inp_6195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6195 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6195 (by decide) v hb
def cl_6196 : CNF.NClause := [(48,false),(17,true),(64,true),(70,false),(76,false),(77,true),(83,true),(88,false)]
theorem inp_6196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6196 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6196 (by decide) v hb
def cl_6197 : CNF.NClause := [(48,false),(17,false),(64,false),(70,true),(76,false),(77,true),(83,true),(88,false)]
theorem inp_6197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6197 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6197 (by decide) v hb
def cl_6198 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,false),(77,true),(83,true),(88,false)]
theorem inp_6198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6198 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6198 (by decide) v hb
def cl_6199 : CNF.NClause := [(48,false),(17,false),(64,true),(70,true),(76,false),(77,true),(83,true),(88,false)]
theorem inp_6199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6199 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6199 (by decide) v hb
def cl_6200 : CNF.NClause := [(48,false),(17,true),(64,true),(70,true),(76,false),(77,true),(83,true),(88,false)]
theorem inp_6200 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6200 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6200 (by decide) v hb
def cl_6201 : CNF.NClause := [(48,false),(17,false),(64,false),(70,false),(76,true),(77,true),(83,true),(88,false)]
theorem inp_6201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6201 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6201 (by decide) v hb
def cl_6202 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,true),(77,true),(83,true),(88,false)]
theorem inp_6202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6202 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6202 (by decide) v hb
def cl_6203 : CNF.NClause := [(48,false),(17,false),(64,true),(70,false),(76,true),(77,true),(83,true),(88,false)]
theorem inp_6203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6203 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6203 (by decide) v hb
def cl_6204 : CNF.NClause := [(48,false),(17,true),(64,true),(70,false),(76,true),(77,true),(83,true),(88,false)]
theorem inp_6204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6204 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6204 (by decide) v hb
def cl_6205 : CNF.NClause := [(48,false),(17,false),(64,false),(70,true),(76,true),(77,true),(83,true),(88,false)]
theorem inp_6205 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6205 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6205 (by decide) v hb
def cl_6206 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,true),(77,true),(83,true),(88,false)]
theorem inp_6206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6206 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6206 (by decide) v hb
def cl_6207 : CNF.NClause := [(48,false),(17,false),(64,true),(70,true),(76,true),(77,true),(83,true),(88,false)]
theorem inp_6207 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6207 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6207 (by decide) v hb
def cl_6208 : CNF.NClause := [(48,false),(17,true),(64,true),(70,true),(76,true),(77,true),(83,true),(88,false)]
theorem inp_6208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6208 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6208 (by decide) v hb
def cl_6209 : CNF.NClause := [(48,false),(17,false),(64,false),(70,false),(76,false),(77,false),(83,false),(88,true)]
theorem inp_6209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6209 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6209 (by decide) v hb
def cl_6210 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,false),(77,false),(83,false),(88,true)]
theorem inp_6210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6210 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6210 v hb
def cl_6211 : CNF.NClause := [(48,false),(17,false),(64,true),(70,false),(76,false),(77,false),(83,false),(88,true)]
theorem inp_6211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6211 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6211 (by decide) v hb
def cl_6212 : CNF.NClause := [(48,false),(17,true),(64,true),(70,false),(76,false),(77,false),(83,false),(88,true)]
theorem inp_6212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6212 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6212 (by decide) v hb
def cl_6213 : CNF.NClause := [(48,false),(17,false),(64,false),(70,true),(76,false),(77,false),(83,false),(88,true)]
theorem inp_6213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6213 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6213 (by decide) v hb
def cl_6214 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,false),(77,false),(83,false),(88,true)]
theorem inp_6214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6214 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6214 v hb
def cl_6215 : CNF.NClause := [(48,false),(17,false),(64,true),(70,true),(76,false),(77,false),(83,false),(88,true)]
theorem inp_6215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6215 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6215 (by decide) v hb
def cl_6216 : CNF.NClause := [(48,false),(17,true),(64,true),(70,true),(76,false),(77,false),(83,false),(88,true)]
theorem inp_6216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6216 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6216 (by decide) v hb
def cl_6217 : CNF.NClause := [(48,false),(17,false),(64,false),(70,false),(76,true),(77,false),(83,false),(88,true)]
theorem inp_6217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6217 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6217 (by decide) v hb
def cl_6218 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,true),(77,false),(83,false),(88,true)]
theorem inp_6218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6218 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6218 (by decide) v hb
def cl_6219 : CNF.NClause := [(48,false),(17,false),(64,true),(70,false),(76,true),(77,false),(83,false),(88,true)]
theorem inp_6219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6219 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6219 (by decide) v hb
def cl_6220 : CNF.NClause := [(48,false),(17,true),(64,true),(70,false),(76,true),(77,false),(83,false),(88,true)]
theorem inp_6220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6220 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6220 (by decide) v hb
def cl_6221 : CNF.NClause := [(48,false),(17,false),(64,false),(70,true),(76,true),(77,false),(83,false),(88,true)]
theorem inp_6221 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6221 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6221 (by decide) v hb
def cl_6222 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,true),(77,false),(83,false),(88,true)]
theorem inp_6222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6222 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6222 (by decide) v hb
def cl_6224 : CNF.NClause := [(48,false),(17,true),(64,true),(70,true),(76,true),(77,false),(83,false),(88,true)]
theorem inp_6224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6224 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6224 (by decide) v hb
def cl_6225 : CNF.NClause := [(48,false),(17,false),(64,false),(70,false),(76,false),(77,true),(83,false),(88,true)]
theorem inp_6225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6225 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6225 (by decide) v hb
def cl_6226 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,false),(77,true),(83,false),(88,true)]
theorem inp_6226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6226 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6226 (by decide) v hb
end Percolation.NReplay
