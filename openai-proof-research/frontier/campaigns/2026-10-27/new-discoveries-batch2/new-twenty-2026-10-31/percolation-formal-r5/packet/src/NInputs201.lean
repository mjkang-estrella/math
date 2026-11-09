import NInputs200
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_13300 : CNF.NClause := [(997,true),(998,false),(999,true),(1000,true),(1001,true),(1022,true)]
theorem inp_13300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13300 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 20) (closed_mem 28 20) cl_13300 (by decide) v hb
def cl_13301 : CNF.NClause := [(997,false),(998,true),(999,true),(1000,true),(1001,true),(1022,true)]
theorem inp_13301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13301 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 20) (closed_mem 28 20) cl_13301 (by decide) v hb
def cl_13302 : CNF.NClause := [(996,true),(997,true),(1003,true),(1009,true),(1015,true),(1018,false)]
theorem inp_13302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13302 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 21) (closed_mem 28 21) cl_13302 (by decide) v hb
def cl_13303 : CNF.NClause := [(996,true),(997,true),(1003,true),(1009,true),(1015,false),(1018,true)]
theorem inp_13303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13303 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 21) (closed_mem 28 21) cl_13303 (by decide) v hb
def cl_13308 : CNF.NClause := [(994,true),(997,true),(1005,true),(1008,true),(1016,true),(1020,false)]
theorem inp_13308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13308 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 22) (closed_mem 28 22) cl_13308 (by decide) v hb
def cl_13314 : CNF.NClause := [(995,true),(997,true),(1004,true),(1011,true),(1013,true),(1019,false)]
theorem inp_13314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13314 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 23) (closed_mem 28 23) cl_13314 (by decide) v hb
def cl_13315 : CNF.NClause := [(995,true),(997,true),(1004,true),(1011,true),(1013,false),(1019,true)]
theorem inp_13315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13315 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 23) (closed_mem 28 23) cl_13315 (by decide) v hb
def cl_13317 : CNF.NClause := [(995,true),(997,true),(1004,false),(1011,true),(1013,true),(1019,true)]
theorem inp_13317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13317 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13317 v hb
def cl_13320 : CNF.NClause := [(993,true),(997,true),(1006,true),(1010,true),(1014,true),(1021,false)]
theorem inp_13320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13320 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 24) (closed_mem 28 24) cl_13320 (by decide) v hb
def cl_13322 : CNF.NClause := [(993,true),(997,true),(1006,true),(1010,false),(1014,true),(1021,true)]
theorem inp_13322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13322 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 24) (closed_mem 28 24) cl_13322 (by decide) v hb
def cl_13323 : CNF.NClause := [(993,true),(997,true),(1006,false),(1010,true),(1014,true),(1021,true)]
theorem inp_13323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13323 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 24) (closed_mem 28 24) cl_13323 (by decide) v hb
def cl_13324 : CNF.NClause := [(993,true),(997,false),(1006,true),(1010,true),(1014,true),(1021,true)]
theorem inp_13324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13324 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 24) (closed_mem 28 24) cl_13324 (by decide) v hb
def cl_13325 : CNF.NClause := [(993,false),(997,true),(1006,true),(1010,true),(1014,true),(1021,true)]
theorem inp_13325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13325 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 24) (closed_mem 28 24) cl_13325 (by decide) v hb
def cl_13327 : CNF.NClause := [(992,true),(993,true),(994,true),(995,true),(996,false),(1022,true)]
theorem inp_13327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13327 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 25) (closed_mem 28 25) cl_13327 (by decide) v hb
def cl_13328 : CNF.NClause := [(992,true),(993,true),(994,true),(995,false),(996,true),(1022,true)]
theorem inp_13328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13328 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 25) (closed_mem 28 25) cl_13328 (by decide) v hb
def cl_13329 : CNF.NClause := [(992,true),(993,true),(994,false),(995,true),(996,true),(1022,true)]
theorem inp_13329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13329 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 25) (closed_mem 28 25) cl_13329 (by decide) v hb
def cl_13330 : CNF.NClause := [(992,true),(993,false),(994,true),(995,true),(996,true),(1022,true)]
theorem inp_13330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13330 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 25) (closed_mem 28 25) cl_13330 (by decide) v hb
def cl_13332 : CNF.NClause := [(992,true),(1001,true),(1005,true),(1009,true),(1013,true),(1021,false)]
theorem inp_13332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13332 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 26) (closed_mem 28 26) cl_13332 (by decide) v hb
def cl_13333 : CNF.NClause := [(992,true),(1001,true),(1005,true),(1009,true),(1013,false),(1021,true)]
theorem inp_13333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13333 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 26) (closed_mem 28 26) cl_13333 (by decide) v hb
def cl_13334 : CNF.NClause := [(992,true),(1001,true),(1005,true),(1009,false),(1013,true),(1021,true)]
theorem inp_13334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13334 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 26) (closed_mem 28 26) cl_13334 (by decide) v hb
def cl_13335 : CNF.NClause := [(992,true),(1001,true),(1005,false),(1009,true),(1013,true),(1021,true)]
theorem inp_13335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13335 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 26) (closed_mem 28 26) cl_13335 (by decide) v hb
def cl_13336 : CNF.NClause := [(992,true),(1001,false),(1005,true),(1009,true),(1013,true),(1021,true)]
theorem inp_13336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13336 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 26) (closed_mem 28 26) cl_13336 (by decide) v hb
def cl_13338 : CNF.NClause := [(992,true),(999,true),(1006,true),(1008,true),(1015,true),(1019,false)]
theorem inp_13338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13338 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 27) (closed_mem 28 27) cl_13338 (by decide) v hb
def cl_13339 : CNF.NClause := [(992,true),(999,true),(1006,true),(1008,true),(1015,false),(1019,true)]
theorem inp_13339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13339 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13339 v hb
def cl_13340 : CNF.NClause := [(992,true),(999,true),(1006,true),(1008,false),(1015,true),(1019,true)]
theorem inp_13340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13340 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 27) (closed_mem 28 27) cl_13340 (by decide) v hb
def cl_13341 : CNF.NClause := [(992,true),(999,true),(1006,false),(1008,true),(1015,true),(1019,true)]
theorem inp_13341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13341 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 27) (closed_mem 28 27) cl_13341 (by decide) v hb
def cl_13344 : CNF.NClause := [(992,true),(1000,true),(1003,true),(1011,true),(1014,true),(1020,false)]
theorem inp_13344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13344 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 28) (closed_mem 28 28) cl_13344 (by decide) v hb
def cl_13350 : CNF.NClause := [(992,true),(998,true),(1004,true),(1010,true),(1016,true),(1018,false)]
theorem inp_13350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13350 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 29) (closed_mem 28 29) cl_13350 (by decide) v hb
def cl_13351 : CNF.NClause := [(992,true),(998,true),(1004,true),(1010,true),(1016,false),(1018,true)]
theorem inp_13351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13351 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 29) (closed_mem 28 29) cl_13351 (by decide) v hb
def cl_13352 : CNF.NClause := [(992,true),(998,true),(1004,true),(1010,false),(1016,true),(1018,true)]
theorem inp_13352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13352 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 29) (closed_mem 28 29) cl_13352 (by decide) v hb
def cl_13353 : CNF.NClause := [(992,true),(998,true),(1004,false),(1010,true),(1016,true),(1018,true)]
theorem inp_13353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13353 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 29) (closed_mem 28 29) cl_13353 (by decide) v hb
def cl_13354 : CNF.NClause := [(992,true),(998,false),(1004,true),(1010,true),(1016,true),(1018,true)]
theorem inp_13354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13354 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 29) (closed_mem 28 29) cl_13354 (by decide) v hb
def cl_13357 : CNF.NClause := [(992,true),(997,true),(1002,true),(1007,true),(1012,false),(1017,true)]
theorem inp_13357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13357 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13357 v hb
def cl_13358 : CNF.NClause := [(992,true),(997,true),(1002,true),(1007,false),(1012,true),(1017,true)]
theorem inp_13358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13358 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 30) (closed_mem 28 30) cl_13358 (by decide) v hb
def cl_13359 : CNF.NClause := [(992,true),(997,true),(1002,false),(1007,true),(1012,true),(1017,true)]
theorem inp_13359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13359 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 30) (closed_mem 28 30) cl_13359 (by decide) v hb
def cl_13360 : CNF.NClause := [(992,true),(997,false),(1002,true),(1007,true),(1012,true),(1017,true)]
theorem inp_13360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13360 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 30) (closed_mem 28 30) cl_13360 (by decide) v hb
def cl_13363 : CNF.NClause := [(1048,true),(1049,true),(1050,true),(1051,true),(1052,false),(1053,true)]
theorem inp_13363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13363 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 0) (closed_mem 29 0) cl_13363 (by decide) v hb
def cl_13369 : CNF.NClause := [(1027,true),(1032,true),(1037,true),(1042,true),(1047,false),(1048,true)]
theorem inp_13369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13369 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 1) (closed_mem 29 1) cl_13369 (by decide) v hb
def cl_13371 : CNF.NClause := [(1027,true),(1032,true),(1037,false),(1042,true),(1047,true),(1048,true)]
theorem inp_13371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13371 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 1) (closed_mem 29 1) cl_13371 (by decide) v hb
def cl_13372 : CNF.NClause := [(1027,true),(1032,false),(1037,true),(1042,true),(1047,true),(1048,true)]
theorem inp_13372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13372 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 1) (closed_mem 29 1) cl_13372 (by decide) v hb
def cl_13373 : CNF.NClause := [(1027,false),(1032,true),(1037,true),(1042,true),(1047,true),(1048,true)]
theorem inp_13373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13373 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 1) (closed_mem 29 1) cl_13373 (by decide) v hb
def cl_13376 : CNF.NClause := [(1025,true),(1030,true),(1035,true),(1040,false),(1045,true),(1048,true)]
theorem inp_13376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13376 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 2) (closed_mem 29 2) cl_13376 (by decide) v hb
def cl_13377 : CNF.NClause := [(1025,true),(1030,true),(1035,false),(1040,true),(1045,true),(1048,true)]
theorem inp_13377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13377 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 2) (closed_mem 29 2) cl_13377 (by decide) v hb
def cl_13378 : CNF.NClause := [(1025,true),(1030,false),(1035,true),(1040,true),(1045,true),(1048,true)]
theorem inp_13378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13378 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 2) (closed_mem 29 2) cl_13378 (by decide) v hb
def cl_13379 : CNF.NClause := [(1025,false),(1030,true),(1035,true),(1040,true),(1045,true),(1048,true)]
theorem inp_13379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13379 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 2) (closed_mem 29 2) cl_13379 (by decide) v hb
def cl_13381 : CNF.NClause := [(1026,true),(1031,true),(1036,true),(1041,true),(1046,false),(1048,true)]
theorem inp_13381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13381 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 3) (closed_mem 29 3) cl_13381 (by decide) v hb
def cl_13383 : CNF.NClause := [(1026,true),(1031,true),(1036,false),(1041,true),(1046,true),(1048,true)]
theorem inp_13383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13383 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 3) (closed_mem 29 3) cl_13383 (by decide) v hb
def cl_13384 : CNF.NClause := [(1026,true),(1031,false),(1036,true),(1041,true),(1046,true),(1048,true)]
theorem inp_13384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13384 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 3) (closed_mem 29 3) cl_13384 (by decide) v hb
def cl_13387 : CNF.NClause := [(1024,true),(1029,true),(1034,true),(1039,true),(1044,false),(1048,true)]
theorem inp_13387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13387 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 4) (closed_mem 29 4) cl_13387 (by decide) v hb
def cl_13388 : CNF.NClause := [(1024,true),(1029,true),(1034,true),(1039,false),(1044,true),(1048,true)]
theorem inp_13388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13388 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 4) (closed_mem 29 4) cl_13388 (by decide) v hb
end Percolation.NReplay
