import NInputs108
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_6227 : CNF.NClause := [(48,false),(17,false),(64,true),(70,false),(76,false),(77,true),(83,false),(88,true)]
theorem inp_6227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6227 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6227 (by decide) v hb
def cl_6228 : CNF.NClause := [(48,false),(17,true),(64,true),(70,false),(76,false),(77,true),(83,false),(88,true)]
theorem inp_6228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6228 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6228 (by decide) v hb
def cl_6229 : CNF.NClause := [(48,false),(17,false),(64,false),(70,true),(76,false),(77,true),(83,false),(88,true)]
theorem inp_6229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6229 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6229 (by decide) v hb
def cl_6230 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,false),(77,true),(83,false),(88,true)]
theorem inp_6230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6230 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6230 (by decide) v hb
def cl_6231 : CNF.NClause := [(48,false),(17,false),(64,true),(70,true),(76,false),(77,true),(83,false),(88,true)]
theorem inp_6231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6231 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6231 (by decide) v hb
def cl_6232 : CNF.NClause := [(48,false),(17,true),(64,true),(70,true),(76,false),(77,true),(83,false),(88,true)]
theorem inp_6232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6232 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6232 (by decide) v hb
def cl_6233 : CNF.NClause := [(48,false),(17,false),(64,false),(70,false),(76,true),(77,true),(83,false),(88,true)]
theorem inp_6233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6233 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6233 (by decide) v hb
def cl_6234 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,true),(77,true),(83,false),(88,true)]
theorem inp_6234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6234 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6234 (by decide) v hb
def cl_6235 : CNF.NClause := [(48,false),(17,false),(64,true),(70,false),(76,true),(77,true),(83,false),(88,true)]
theorem inp_6235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6235 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6235 (by decide) v hb
def cl_6236 : CNF.NClause := [(48,false),(17,true),(64,true),(70,false),(76,true),(77,true),(83,false),(88,true)]
theorem inp_6236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6236 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6236 (by decide) v hb
def cl_6237 : CNF.NClause := [(48,false),(17,false),(64,false),(70,true),(76,true),(77,true),(83,false),(88,true)]
theorem inp_6237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6237 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6237 (by decide) v hb
def cl_6238 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,true),(77,true),(83,false),(88,true)]
theorem inp_6238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6238 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6238 (by decide) v hb
def cl_6239 : CNF.NClause := [(48,false),(17,false),(64,true),(70,true),(76,true),(77,true),(83,false),(88,true)]
theorem inp_6239 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6239 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6239 (by decide) v hb
def cl_6240 : CNF.NClause := [(48,false),(17,true),(64,true),(70,true),(76,true),(77,true),(83,false),(88,true)]
theorem inp_6240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6240 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6240 (by decide) v hb
def cl_6241 : CNF.NClause := [(48,false),(17,false),(64,false),(70,false),(76,false),(77,false),(83,true),(88,true)]
theorem inp_6241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6241 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6241 (by decide) v hb
def cl_6242 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,false),(77,false),(83,true),(88,true)]
theorem inp_6242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6242 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6242 (by decide) v hb
def cl_6243 : CNF.NClause := [(48,false),(17,false),(64,true),(70,false),(76,false),(77,false),(83,true),(88,true)]
theorem inp_6243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6243 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6243 (by decide) v hb
def cl_6244 : CNF.NClause := [(48,false),(17,true),(64,true),(70,false),(76,false),(77,false),(83,true),(88,true)]
theorem inp_6244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6244 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6244 (by decide) v hb
def cl_6245 : CNF.NClause := [(48,false),(17,false),(64,false),(70,true),(76,false),(77,false),(83,true),(88,true)]
theorem inp_6245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6245 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6245 (by decide) v hb
def cl_6246 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,false),(77,false),(83,true),(88,true)]
theorem inp_6246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6246 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6246 (by decide) v hb
def cl_6247 : CNF.NClause := [(48,false),(17,false),(64,true),(70,true),(76,false),(77,false),(83,true),(88,true)]
theorem inp_6247 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6247 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6247 (by decide) v hb
def cl_6248 : CNF.NClause := [(48,false),(17,true),(64,true),(70,true),(76,false),(77,false),(83,true),(88,true)]
theorem inp_6248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6248 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6248 (by decide) v hb
def cl_6249 : CNF.NClause := [(48,false),(17,false),(64,false),(70,false),(76,true),(77,false),(83,true),(88,true)]
theorem inp_6249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6249 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6249 (by decide) v hb
def cl_6250 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,true),(77,false),(83,true),(88,true)]
theorem inp_6250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6250 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6250 (by decide) v hb
def cl_6252 : CNF.NClause := [(48,false),(17,true),(64,true),(70,false),(76,true),(77,false),(83,true),(88,true)]
theorem inp_6252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6252 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6252 (by decide) v hb
def cl_6253 : CNF.NClause := [(48,false),(17,false),(64,false),(70,true),(76,true),(77,false),(83,true),(88,true)]
theorem inp_6253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6253 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6253 (by decide) v hb
def cl_6254 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,true),(77,false),(83,true),(88,true)]
theorem inp_6254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6254 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6254 (by decide) v hb
def cl_6256 : CNF.NClause := [(48,false),(17,true),(64,true),(70,true),(76,true),(77,false),(83,true),(88,true)]
theorem inp_6256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6256 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6256 (by decide) v hb
def cl_6258 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,false),(77,true),(83,true),(88,true)]
theorem inp_6258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6258 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6258 (by decide) v hb
def cl_6259 : CNF.NClause := [(48,false),(17,false),(64,true),(70,false),(76,false),(77,true),(83,true),(88,true)]
theorem inp_6259 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6259 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6259 (by decide) v hb
def cl_6260 : CNF.NClause := [(48,false),(17,true),(64,true),(70,false),(76,false),(77,true),(83,true),(88,true)]
theorem inp_6260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6260 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6260 (by decide) v hb
def cl_6261 : CNF.NClause := [(48,false),(17,false),(64,false),(70,true),(76,false),(77,true),(83,true),(88,true)]
theorem inp_6261 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6261 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6261 (by decide) v hb
def cl_6262 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,false),(77,true),(83,true),(88,true)]
theorem inp_6262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6262 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6262 (by decide) v hb
def cl_6263 : CNF.NClause := [(48,false),(17,false),(64,true),(70,true),(76,false),(77,true),(83,true),(88,true)]
theorem inp_6263 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6263 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6263 (by decide) v hb
def cl_6264 : CNF.NClause := [(48,false),(17,true),(64,true),(70,true),(76,false),(77,true),(83,true),(88,true)]
theorem inp_6264 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6264 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6264 (by decide) v hb
def cl_6266 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,true),(77,true),(83,true),(88,true)]
theorem inp_6266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6266 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6266 (by decide) v hb
def cl_6268 : CNF.NClause := [(48,false),(17,true),(64,true),(70,false),(76,true),(77,true),(83,true),(88,true)]
theorem inp_6268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6268 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6268 (by decide) v hb
def cl_6269 : CNF.NClause := [(48,false),(17,false),(64,false),(70,true),(76,true),(77,true),(83,true),(88,true)]
theorem inp_6269 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6269 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6269 (by decide) v hb
def cl_6270 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,true),(77,true),(83,true),(88,true)]
theorem inp_6270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6270 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6270 (by decide) v hb
def cl_6272 : CNF.NClause := [(48,false),(17,true),(64,true),(70,true),(76,true),(77,true),(83,true),(88,true)]
theorem inp_6272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6272 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) cl_6272 (by decide) v hb
def cl_6273 : CNF.NClause := [(49,true),(18,false),(65,false),(69,false),(73,false),(77,false),(86,false),(91,false)]
theorem inp_6273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6273 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6273 (by decide) v hb
def cl_6274 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,false),(77,false),(86,false),(91,false)]
theorem inp_6274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6274 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6274 v hb
def cl_6275 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(73,false),(77,false),(86,false),(91,false)]
theorem inp_6275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6275 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6275 (by decide) v hb
def cl_6276 : CNF.NClause := [(49,false),(18,true),(65,true),(69,false),(73,false),(77,false),(86,false),(91,false)]
theorem inp_6276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6276 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6276 (by decide) v hb
def cl_6277 : CNF.NClause := [(49,false),(18,false),(65,false),(69,true),(73,false),(77,false),(86,false),(91,false)]
theorem inp_6277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6277 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6277 v hb
def cl_6278 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,false),(77,false),(86,false),(91,false)]
theorem inp_6278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6278 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6278 v hb
def cl_6279 : CNF.NClause := [(49,false),(18,false),(65,true),(69,true),(73,false),(77,false),(86,false),(91,false)]
theorem inp_6279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6279 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6279 (by decide) v hb
def cl_6280 : CNF.NClause := [(49,false),(18,true),(65,true),(69,true),(73,false),(77,false),(86,false),(91,false)]
theorem inp_6280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6280 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6280 (by decide) v hb
def cl_6281 : CNF.NClause := [(49,false),(18,false),(65,false),(69,false),(73,true),(77,false),(86,false),(91,false)]
theorem inp_6281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6281 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6281 v hb
def cl_6282 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,true),(77,false),(86,false),(91,false)]
theorem inp_6282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6282 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) cl_6282 (by decide) v hb
end Percolation.NReplay
