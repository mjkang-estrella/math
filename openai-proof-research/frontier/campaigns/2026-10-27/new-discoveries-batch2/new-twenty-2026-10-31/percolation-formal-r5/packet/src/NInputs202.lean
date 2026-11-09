import NInputs201
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_13389 : CNF.NClause := [(1024,true),(1029,true),(1034,false),(1039,true),(1044,true),(1048,true)]
theorem inp_13389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13389 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 4) (closed_mem 29 4) cl_13389 (by decide) v hb
def cl_13390 : CNF.NClause := [(1024,true),(1029,false),(1034,true),(1039,true),(1044,true),(1048,true)]
theorem inp_13390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13390 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 4) (closed_mem 29 4) cl_13390 (by decide) v hb
def cl_13391 : CNF.NClause := [(1024,false),(1029,true),(1034,true),(1039,true),(1044,true),(1048,true)]
theorem inp_13391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13391 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 4) (closed_mem 29 4) cl_13391 (by decide) v hb
def cl_13393 : CNF.NClause := [(1043,true),(1044,true),(1045,true),(1046,true),(1047,false),(1053,true)]
theorem inp_13393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13393 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 5) (closed_mem 29 5) cl_13393 (by decide) v hb
def cl_13394 : CNF.NClause := [(1043,true),(1044,true),(1045,true),(1046,false),(1047,true),(1053,true)]
theorem inp_13394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13394 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 5) (closed_mem 29 5) cl_13394 (by decide) v hb
def cl_13395 : CNF.NClause := [(1043,true),(1044,true),(1045,false),(1046,true),(1047,true),(1053,true)]
theorem inp_13395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13395 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 5) (closed_mem 29 5) cl_13395 (by decide) v hb
def cl_13397 : CNF.NClause := [(1043,false),(1044,true),(1045,true),(1046,true),(1047,true),(1053,true)]
theorem inp_13397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13397 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 5) (closed_mem 29 5) cl_13397 (by decide) v hb
def cl_13398 : CNF.NClause := [(1027,true),(1031,true),(1035,true),(1039,true),(1043,true),(1052,false)]
theorem inp_13398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13398 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 6) (closed_mem 29 6) cl_13398 (by decide) v hb
def cl_13404 : CNF.NClause := [(1025,true),(1032,true),(1034,true),(1041,true),(1043,true),(1050,false)]
theorem inp_13404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13404 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 7) (closed_mem 29 7) cl_13404 (by decide) v hb
def cl_13405 : CNF.NClause := [(1025,true),(1032,true),(1034,true),(1041,true),(1043,false),(1050,true)]
theorem inp_13405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13405 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 7) (closed_mem 29 7) cl_13405 (by decide) v hb
def cl_13409 : CNF.NClause := [(1025,false),(1032,true),(1034,true),(1041,true),(1043,true),(1050,true)]
theorem inp_13409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13409 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 7) (closed_mem 29 7) cl_13409 (by decide) v hb
def cl_13410 : CNF.NClause := [(1026,true),(1029,true),(1037,true),(1040,true),(1043,true),(1051,false)]
theorem inp_13410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13410 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 8) (closed_mem 29 8) cl_13410 (by decide) v hb
def cl_13411 : CNF.NClause := [(1026,true),(1029,true),(1037,true),(1040,true),(1043,false),(1051,true)]
theorem inp_13411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13411 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 8) (closed_mem 29 8) cl_13411 (by decide) v hb
def cl_13412 : CNF.NClause := [(1026,true),(1029,true),(1037,true),(1040,false),(1043,true),(1051,true)]
theorem inp_13412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13412 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 8) (closed_mem 29 8) cl_13412 (by decide) v hb
def cl_13417 : CNF.NClause := [(1024,true),(1030,true),(1036,true),(1042,true),(1043,false),(1049,true)]
theorem inp_13417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13417 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 9) (closed_mem 29 9) cl_13417 (by decide) v hb
def cl_13421 : CNF.NClause := [(1024,false),(1030,true),(1036,true),(1042,true),(1043,true),(1049,true)]
theorem inp_13421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13421 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 9) (closed_mem 29 9) cl_13421 (by decide) v hb
def cl_13423 : CNF.NClause := [(1033,true),(1034,true),(1035,true),(1036,true),(1037,false),(1053,true)]
theorem inp_13423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13423 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 10) (closed_mem 29 10) cl_13423 (by decide) v hb
def cl_13424 : CNF.NClause := [(1033,true),(1034,true),(1035,true),(1036,false),(1037,true),(1053,true)]
theorem inp_13424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13424 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 10) (closed_mem 29 10) cl_13424 (by decide) v hb
def cl_13425 : CNF.NClause := [(1033,true),(1034,true),(1035,false),(1036,true),(1037,true),(1053,true)]
theorem inp_13425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13425 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 10) (closed_mem 29 10) cl_13425 (by decide) v hb
def cl_13426 : CNF.NClause := [(1033,true),(1034,false),(1035,true),(1036,true),(1037,true),(1053,true)]
theorem inp_13426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13426 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 10) (closed_mem 29 10) cl_13426 (by decide) v hb
def cl_13429 : CNF.NClause := [(1027,true),(1030,true),(1033,true),(1041,true),(1044,false),(1051,true)]
theorem inp_13429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13429 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 11) (closed_mem 29 11) cl_13429 (by decide) v hb
def cl_13430 : CNF.NClause := [(1027,true),(1030,true),(1033,true),(1041,false),(1044,true),(1051,true)]
theorem inp_13430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13430 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 11) (closed_mem 29 11) cl_13430 (by decide) v hb
def cl_13431 : CNF.NClause := [(1027,true),(1030,true),(1033,false),(1041,true),(1044,true),(1051,true)]
theorem inp_13431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13431 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 11) (closed_mem 29 11) cl_13431 (by decide) v hb
def cl_13433 : CNF.NClause := [(1027,false),(1030,true),(1033,true),(1041,true),(1044,true),(1051,true)]
theorem inp_13433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13433 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 11) (closed_mem 29 11) cl_13433 (by decide) v hb
def cl_13434 : CNF.NClause := [(1025,true),(1029,true),(1033,true),(1042,true),(1046,true),(1052,false)]
theorem inp_13434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13434 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 12) (closed_mem 29 12) cl_13434 (by decide) v hb
def cl_13440 : CNF.NClause := [(1026,true),(1032,true),(1033,true),(1039,true),(1045,true),(1049,false)]
theorem inp_13440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13440 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 13) (closed_mem 29 13) cl_13440 (by decide) v hb
def cl_13441 : CNF.NClause := [(1026,true),(1032,true),(1033,true),(1039,true),(1045,false),(1049,true)]
theorem inp_13441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13441 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 13) (closed_mem 29 13) cl_13441 (by decide) v hb
def cl_13443 : CNF.NClause := [(1026,true),(1032,true),(1033,false),(1039,true),(1045,true),(1049,true)]
theorem inp_13443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13443 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 13) (closed_mem 29 13) cl_13443 (by decide) v hb
def cl_13445 : CNF.NClause := [(1026,false),(1032,true),(1033,true),(1039,true),(1045,true),(1049,true)]
theorem inp_13445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13445 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 13) (closed_mem 29 13) cl_13445 (by decide) v hb
def cl_13446 : CNF.NClause := [(1024,true),(1031,true),(1033,true),(1040,true),(1047,true),(1050,false)]
theorem inp_13446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13446 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 14) (closed_mem 29 14) cl_13446 (by decide) v hb
def cl_13447 : CNF.NClause := [(1024,true),(1031,true),(1033,true),(1040,true),(1047,false),(1050,true)]
theorem inp_13447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13447 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 14) (closed_mem 29 14) cl_13447 (by decide) v hb
def cl_13453 : CNF.NClause := [(1038,true),(1039,true),(1040,true),(1041,true),(1042,false),(1053,true)]
theorem inp_13453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13453 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 15) (closed_mem 29 15) cl_13453 (by decide) v hb
def cl_13454 : CNF.NClause := [(1038,true),(1039,true),(1040,true),(1041,false),(1042,true),(1053,true)]
theorem inp_13454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13454 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 15) (closed_mem 29 15) cl_13454 (by decide) v hb
def cl_13455 : CNF.NClause := [(1038,true),(1039,true),(1040,false),(1041,true),(1042,true),(1053,true)]
theorem inp_13455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13455 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 15) (closed_mem 29 15) cl_13455 (by decide) v hb
def cl_13456 : CNF.NClause := [(1038,true),(1039,false),(1040,true),(1041,true),(1042,true),(1053,true)]
theorem inp_13456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13456 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 15) (closed_mem 29 15) cl_13456 (by decide) v hb
def cl_13457 : CNF.NClause := [(1038,false),(1039,true),(1040,true),(1041,true),(1042,true),(1053,true)]
theorem inp_13457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13457 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 15) (closed_mem 29 15) cl_13457 (by decide) v hb
def cl_13458 : CNF.NClause := [(1027,true),(1029,true),(1036,true),(1038,true),(1045,true),(1050,false)]
theorem inp_13458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13458 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 16) (closed_mem 29 16) cl_13458 (by decide) v hb
def cl_13463 : CNF.NClause := [(1027,false),(1029,true),(1036,true),(1038,true),(1045,true),(1050,true)]
theorem inp_13463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13463 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 16) (closed_mem 29 16) cl_13463 (by decide) v hb
def cl_13466 : CNF.NClause := [(1025,true),(1031,true),(1037,true),(1038,false),(1044,true),(1049,true)]
theorem inp_13466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13466 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 17) (closed_mem 29 17) cl_13466 (by decide) v hb
def cl_13469 : CNF.NClause := [(1025,false),(1031,true),(1037,true),(1038,true),(1044,true),(1049,true)]
theorem inp_13469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13469 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 17) (closed_mem 29 17) cl_13469 (by decide) v hb
def cl_13470 : CNF.NClause := [(1026,true),(1030,true),(1034,true),(1038,true),(1047,true),(1052,false)]
theorem inp_13470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13470 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 18) (closed_mem 29 18) cl_13470 (by decide) v hb
def cl_13476 : CNF.NClause := [(1024,true),(1032,true),(1035,true),(1038,true),(1046,true),(1051,false)]
theorem inp_13476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13476 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 19) (closed_mem 29 19) cl_13476 (by decide) v hb
def cl_13477 : CNF.NClause := [(1024,true),(1032,true),(1035,true),(1038,true),(1046,false),(1051,true)]
theorem inp_13477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13477 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 19) (closed_mem 29 19) cl_13477 (by decide) v hb
def cl_13480 : CNF.NClause := [(1024,true),(1032,false),(1035,true),(1038,true),(1046,true),(1051,true)]
theorem inp_13480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13480 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 19) (closed_mem 29 19) cl_13480 (by decide) v hb
def cl_13483 : CNF.NClause := [(1028,true),(1029,true),(1030,true),(1031,true),(1032,false),(1053,true)]
theorem inp_13483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13483 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 20) (closed_mem 29 20) cl_13483 (by decide) v hb
def cl_13484 : CNF.NClause := [(1028,true),(1029,true),(1030,true),(1031,false),(1032,true),(1053,true)]
theorem inp_13484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13484 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 20) (closed_mem 29 20) cl_13484 (by decide) v hb
def cl_13485 : CNF.NClause := [(1028,true),(1029,true),(1030,false),(1031,true),(1032,true),(1053,true)]
theorem inp_13485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13485 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 20) (closed_mem 29 20) cl_13485 (by decide) v hb
def cl_13486 : CNF.NClause := [(1028,true),(1029,false),(1030,true),(1031,true),(1032,true),(1053,true)]
theorem inp_13486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13486 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 20) (closed_mem 29 20) cl_13486 (by decide) v hb
def cl_13487 : CNF.NClause := [(1028,false),(1029,true),(1030,true),(1031,true),(1032,true),(1053,true)]
theorem inp_13487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13487 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 20) (closed_mem 29 20) cl_13487 (by decide) v hb
def cl_13488 : CNF.NClause := [(1027,true),(1028,true),(1034,true),(1040,true),(1046,true),(1049,false)]
theorem inp_13488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13488 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 21) (closed_mem 29 21) cl_13488 (by decide) v hb
end Percolation.NReplay
