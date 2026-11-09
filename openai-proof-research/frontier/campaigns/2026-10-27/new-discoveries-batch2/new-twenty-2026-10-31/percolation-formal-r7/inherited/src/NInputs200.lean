import NInputs199
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_13203 : CNF.NClause := [(993,true),(998,true),(1003,false),(1008,true),(1013,true),(1017,true)]
theorem inp_13203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13203 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 4) (closed_mem 28 4) cl_13203 (by decide) v hb
def cl_13204 : CNF.NClause := [(993,true),(998,false),(1003,true),(1008,true),(1013,true),(1017,true)]
theorem inp_13204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13204 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 4) (closed_mem 28 4) cl_13204 (by decide) v hb
def cl_13207 : CNF.NClause := [(1012,true),(1013,true),(1014,true),(1015,true),(1016,false),(1022,true)]
theorem inp_13207 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13207 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 5) (closed_mem 28 5) cl_13207 (by decide) v hb
def cl_13208 : CNF.NClause := [(1012,true),(1013,true),(1014,true),(1015,false),(1016,true),(1022,true)]
theorem inp_13208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13208 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 5) (closed_mem 28 5) cl_13208 (by decide) v hb
def cl_13209 : CNF.NClause := [(1012,true),(1013,true),(1014,false),(1015,true),(1016,true),(1022,true)]
theorem inp_13209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13209 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 5) (closed_mem 28 5) cl_13209 (by decide) v hb
def cl_13211 : CNF.NClause := [(1012,false),(1013,true),(1014,true),(1015,true),(1016,true),(1022,true)]
theorem inp_13211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13211 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 5) (closed_mem 28 5) cl_13211 (by decide) v hb
def cl_13213 : CNF.NClause := [(996,true),(1000,true),(1004,true),(1008,true),(1012,false),(1021,true)]
theorem inp_13213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13213 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 6) (closed_mem 28 6) cl_13213 (by decide) v hb
def cl_13214 : CNF.NClause := [(996,true),(1000,true),(1004,true),(1008,false),(1012,true),(1021,true)]
theorem inp_13214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13214 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 6) (closed_mem 28 6) cl_13214 (by decide) v hb
def cl_13215 : CNF.NClause := [(996,true),(1000,true),(1004,false),(1008,true),(1012,true),(1021,true)]
theorem inp_13215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13215 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 6) (closed_mem 28 6) cl_13215 (by decide) v hb
def cl_13217 : CNF.NClause := [(996,false),(1000,true),(1004,true),(1008,true),(1012,true),(1021,true)]
theorem inp_13217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13217 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 6) (closed_mem 28 6) cl_13217 (by decide) v hb
def cl_13218 : CNF.NClause := [(994,true),(1001,true),(1003,true),(1010,true),(1012,true),(1019,false)]
theorem inp_13218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13218 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 7) (closed_mem 28 7) cl_13218 (by decide) v hb
def cl_13222 : CNF.NClause := [(994,true),(1001,false),(1003,true),(1010,true),(1012,true),(1019,true)]
theorem inp_13222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13222 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 7) (closed_mem 28 7) cl_13222 (by decide) v hb
def cl_13224 : CNF.NClause := [(995,true),(998,true),(1006,true),(1009,true),(1012,true),(1020,false)]
theorem inp_13224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13224 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13224 v hb
def cl_13230 : CNF.NClause := [(993,true),(999,true),(1005,true),(1011,true),(1012,true),(1018,false)]
theorem inp_13230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13230 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 9) (closed_mem 28 9) cl_13230 (by decide) v hb
def cl_13231 : CNF.NClause := [(993,true),(999,true),(1005,true),(1011,true),(1012,false),(1018,true)]
theorem inp_13231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13231 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 9) (closed_mem 28 9) cl_13231 (by decide) v hb
def cl_13234 : CNF.NClause := [(993,true),(999,false),(1005,true),(1011,true),(1012,true),(1018,true)]
theorem inp_13234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13234 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 9) (closed_mem 28 9) cl_13234 (by decide) v hb
def cl_13235 : CNF.NClause := [(993,false),(999,true),(1005,true),(1011,true),(1012,true),(1018,true)]
theorem inp_13235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13235 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 9) (closed_mem 28 9) cl_13235 (by decide) v hb
def cl_13237 : CNF.NClause := [(1002,true),(1003,true),(1004,true),(1005,true),(1006,false),(1022,true)]
theorem inp_13237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13237 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 10) (closed_mem 28 10) cl_13237 (by decide) v hb
def cl_13238 : CNF.NClause := [(1002,true),(1003,true),(1004,true),(1005,false),(1006,true),(1022,true)]
theorem inp_13238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13238 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 10) (closed_mem 28 10) cl_13238 (by decide) v hb
def cl_13239 : CNF.NClause := [(1002,true),(1003,true),(1004,false),(1005,true),(1006,true),(1022,true)]
theorem inp_13239 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13239 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 10) (closed_mem 28 10) cl_13239 (by decide) v hb
def cl_13240 : CNF.NClause := [(1002,true),(1003,false),(1004,true),(1005,true),(1006,true),(1022,true)]
theorem inp_13240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13240 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 10) (closed_mem 28 10) cl_13240 (by decide) v hb
def cl_13242 : CNF.NClause := [(996,true),(999,true),(1002,true),(1010,true),(1013,true),(1020,false)]
theorem inp_13242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13242 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13242 v hb
def cl_13248 : CNF.NClause := [(994,true),(998,true),(1002,true),(1011,true),(1015,true),(1021,false)]
theorem inp_13248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13248 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 12) (closed_mem 28 12) cl_13248 (by decide) v hb
def cl_13249 : CNF.NClause := [(994,true),(998,true),(1002,true),(1011,true),(1015,false),(1021,true)]
theorem inp_13249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13249 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 12) (closed_mem 28 12) cl_13249 (by decide) v hb
def cl_13252 : CNF.NClause := [(994,true),(998,false),(1002,true),(1011,true),(1015,true),(1021,true)]
theorem inp_13252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13252 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 12) (closed_mem 28 12) cl_13252 (by decide) v hb
def cl_13255 : CNF.NClause := [(995,true),(1001,true),(1002,true),(1008,true),(1014,false),(1018,true)]
theorem inp_13255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13255 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 13) (closed_mem 28 13) cl_13255 (by decide) v hb
def cl_13257 : CNF.NClause := [(995,true),(1001,true),(1002,false),(1008,true),(1014,true),(1018,true)]
theorem inp_13257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13257 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 13) (closed_mem 28 13) cl_13257 (by decide) v hb
def cl_13259 : CNF.NClause := [(995,false),(1001,true),(1002,true),(1008,true),(1014,true),(1018,true)]
theorem inp_13259 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13259 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 13) (closed_mem 28 13) cl_13259 (by decide) v hb
def cl_13260 : CNF.NClause := [(993,true),(1000,true),(1002,true),(1009,true),(1016,true),(1019,false)]
theorem inp_13260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13260 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 14) (closed_mem 28 14) cl_13260 (by decide) v hb
def cl_13264 : CNF.NClause := [(993,true),(1000,false),(1002,true),(1009,true),(1016,true),(1019,true)]
theorem inp_13264 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13264 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 14) (closed_mem 28 14) cl_13264 (by decide) v hb
def cl_13267 : CNF.NClause := [(1007,true),(1008,true),(1009,true),(1010,true),(1011,false),(1022,true)]
theorem inp_13267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13267 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 15) (closed_mem 28 15) cl_13267 (by decide) v hb
def cl_13268 : CNF.NClause := [(1007,true),(1008,true),(1009,true),(1010,false),(1011,true),(1022,true)]
theorem inp_13268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13268 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13268 v hb
def cl_13269 : CNF.NClause := [(1007,true),(1008,true),(1009,false),(1010,true),(1011,true),(1022,true)]
theorem inp_13269 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13269 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 15) (closed_mem 28 15) cl_13269 (by decide) v hb
def cl_13270 : CNF.NClause := [(1007,true),(1008,false),(1009,true),(1010,true),(1011,true),(1022,true)]
theorem inp_13270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13270 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 15) (closed_mem 28 15) cl_13270 (by decide) v hb
def cl_13271 : CNF.NClause := [(1007,false),(1008,true),(1009,true),(1010,true),(1011,true),(1022,true)]
theorem inp_13271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13271 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 15) (closed_mem 28 15) cl_13271 (by decide) v hb
def cl_13272 : CNF.NClause := [(996,true),(998,true),(1005,true),(1007,true),(1014,true),(1019,false)]
theorem inp_13272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13272 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 16) (closed_mem 28 16) cl_13272 (by decide) v hb
def cl_13277 : CNF.NClause := [(996,false),(998,true),(1005,true),(1007,true),(1014,true),(1019,true)]
theorem inp_13277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13277 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13277 v hb
def cl_13278 : CNF.NClause := [(994,true),(1000,true),(1006,true),(1007,true),(1013,true),(1018,false)]
theorem inp_13278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13278 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 17) (closed_mem 28 17) cl_13278 (by decide) v hb
def cl_13280 : CNF.NClause := [(994,true),(1000,true),(1006,true),(1007,false),(1013,true),(1018,true)]
theorem inp_13280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13280 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 17) (closed_mem 28 17) cl_13280 (by decide) v hb
def cl_13281 : CNF.NClause := [(994,true),(1000,true),(1006,false),(1007,true),(1013,true),(1018,true)]
theorem inp_13281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13281 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13281 v hb
def cl_13282 : CNF.NClause := [(994,true),(1000,false),(1006,true),(1007,true),(1013,true),(1018,true)]
theorem inp_13282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13282 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 17) (closed_mem 28 17) cl_13282 (by decide) v hb
def cl_13284 : CNF.NClause := [(995,true),(999,true),(1003,true),(1007,true),(1016,true),(1021,false)]
theorem inp_13284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13284 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 18) (closed_mem 28 18) cl_13284 (by decide) v hb
def cl_13286 : CNF.NClause := [(995,true),(999,true),(1003,true),(1007,false),(1016,true),(1021,true)]
theorem inp_13286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13286 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 18) (closed_mem 28 18) cl_13286 (by decide) v hb
def cl_13287 : CNF.NClause := [(995,true),(999,true),(1003,false),(1007,true),(1016,true),(1021,true)]
theorem inp_13287 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13287 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 18) (closed_mem 28 18) cl_13287 (by decide) v hb
def cl_13288 : CNF.NClause := [(995,true),(999,false),(1003,true),(1007,true),(1016,true),(1021,true)]
theorem inp_13288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13288 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 18) (closed_mem 28 18) cl_13288 (by decide) v hb
def cl_13289 : CNF.NClause := [(995,false),(999,true),(1003,true),(1007,true),(1016,true),(1021,true)]
theorem inp_13289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13289 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 18) (closed_mem 28 18) cl_13289 (by decide) v hb
def cl_13290 : CNF.NClause := [(993,true),(1001,true),(1004,true),(1007,true),(1015,true),(1020,false)]
theorem inp_13290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13290 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 19) (closed_mem 28 19) cl_13290 (by decide) v hb
def cl_13297 : CNF.NClause := [(997,true),(998,true),(999,true),(1000,true),(1001,false),(1022,true)]
theorem inp_13297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13297 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 20) (closed_mem 28 20) cl_13297 (by decide) v hb
def cl_13298 : CNF.NClause := [(997,true),(998,true),(999,true),(1000,false),(1001,true),(1022,true)]
theorem inp_13298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13298 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 20) (closed_mem 28 20) cl_13298 (by decide) v hb
def cl_13299 : CNF.NClause := [(997,true),(998,true),(999,false),(1000,true),(1001,true),(1022,true)]
theorem inp_13299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13299 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 20) (closed_mem 28 20) cl_13299 (by decide) v hb
end Percolation.NReplay
