import NInputs202
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_13489 : CNF.NClause := [(1027,true),(1028,true),(1034,true),(1040,true),(1046,false),(1049,true)]
theorem inp_13489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13489 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 21) (closed_mem 29 21) cl_13489 (by decide) v hb
def cl_13492 : CNF.NClause := [(1027,true),(1028,false),(1034,true),(1040,true),(1046,true),(1049,true)]
theorem inp_13492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13492 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 21) (closed_mem 29 21) cl_13492 (by decide) v hb
def cl_13493 : CNF.NClause := [(1027,false),(1028,true),(1034,true),(1040,true),(1046,true),(1049,true)]
theorem inp_13493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13493 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 21) (closed_mem 29 21) cl_13493 (by decide) v hb
def cl_13494 : CNF.NClause := [(1025,true),(1028,true),(1036,true),(1039,true),(1047,true),(1051,false)]
theorem inp_13494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13494 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 22) (closed_mem 29 22) cl_13494 (by decide) v hb
def cl_13496 : CNF.NClause := [(1025,true),(1028,true),(1036,true),(1039,false),(1047,true),(1051,true)]
theorem inp_13496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13496 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 22) (closed_mem 29 22) cl_13496 (by decide) v hb
def cl_13497 : CNF.NClause := [(1025,true),(1028,true),(1036,false),(1039,true),(1047,true),(1051,true)]
theorem inp_13497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13497 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 22) (closed_mem 29 22) cl_13497 (by decide) v hb
def cl_13498 : CNF.NClause := [(1025,true),(1028,false),(1036,true),(1039,true),(1047,true),(1051,true)]
theorem inp_13498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13498 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 22) (closed_mem 29 22) cl_13498 (by decide) v hb
def cl_13499 : CNF.NClause := [(1025,false),(1028,true),(1036,true),(1039,true),(1047,true),(1051,true)]
theorem inp_13499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13499 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 22) (closed_mem 29 22) cl_13499 (by decide) v hb
def cl_13500 : CNF.NClause := [(1026,true),(1028,true),(1035,true),(1042,true),(1044,true),(1050,false)]
theorem inp_13500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13500 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 23) (closed_mem 29 23) cl_13500 (by decide) v hb
def cl_13502 : CNF.NClause := [(1026,true),(1028,true),(1035,true),(1042,false),(1044,true),(1050,true)]
theorem inp_13502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13502 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 23) (closed_mem 29 23) cl_13502 (by decide) v hb
def cl_13504 : CNF.NClause := [(1026,true),(1028,false),(1035,true),(1042,true),(1044,true),(1050,true)]
theorem inp_13504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13504 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 23) (closed_mem 29 23) cl_13504 (by decide) v hb
def cl_13505 : CNF.NClause := [(1026,false),(1028,true),(1035,true),(1042,true),(1044,true),(1050,true)]
theorem inp_13505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13505 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 23) (closed_mem 29 23) cl_13505 (by decide) v hb
def cl_13506 : CNF.NClause := [(1024,true),(1028,true),(1037,true),(1041,true),(1045,true),(1052,false)]
theorem inp_13506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13506 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 24) (closed_mem 29 24) cl_13506 (by decide) v hb
def cl_13513 : CNF.NClause := [(1023,true),(1024,true),(1025,true),(1026,true),(1027,false),(1053,true)]
theorem inp_13513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13513 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 25) (closed_mem 29 25) cl_13513 (by decide) v hb
def cl_13514 : CNF.NClause := [(1023,true),(1024,true),(1025,true),(1026,false),(1027,true),(1053,true)]
theorem inp_13514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13514 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 25) (closed_mem 29 25) cl_13514 (by decide) v hb
def cl_13515 : CNF.NClause := [(1023,true),(1024,true),(1025,false),(1026,true),(1027,true),(1053,true)]
theorem inp_13515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13515 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 25) (closed_mem 29 25) cl_13515 (by decide) v hb
def cl_13516 : CNF.NClause := [(1023,true),(1024,false),(1025,true),(1026,true),(1027,true),(1053,true)]
theorem inp_13516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13516 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 25) (closed_mem 29 25) cl_13516 (by decide) v hb
def cl_13518 : CNF.NClause := [(1023,true),(1032,true),(1036,true),(1040,true),(1044,true),(1052,false)]
theorem inp_13518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13518 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 26) (closed_mem 29 26) cl_13518 (by decide) v hb
def cl_13524 : CNF.NClause := [(1023,true),(1030,true),(1037,true),(1039,true),(1046,true),(1050,false)]
theorem inp_13524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13524 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 27) (closed_mem 29 27) cl_13524 (by decide) v hb
def cl_13526 : CNF.NClause := [(1023,true),(1030,true),(1037,true),(1039,false),(1046,true),(1050,true)]
theorem inp_13526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13526 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 27) (closed_mem 29 27) cl_13526 (by decide) v hb
def cl_13527 : CNF.NClause := [(1023,true),(1030,true),(1037,false),(1039,true),(1046,true),(1050,true)]
theorem inp_13527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13527 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 27) (closed_mem 29 27) cl_13527 (by decide) v hb
def cl_13530 : CNF.NClause := [(1023,true),(1031,true),(1034,true),(1042,true),(1045,true),(1051,false)]
theorem inp_13530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13530 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 28) (closed_mem 29 28) cl_13530 (by decide) v hb
def cl_13531 : CNF.NClause := [(1023,true),(1031,true),(1034,true),(1042,true),(1045,false),(1051,true)]
theorem inp_13531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13531 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 28) (closed_mem 29 28) cl_13531 (by decide) v hb
def cl_13532 : CNF.NClause := [(1023,true),(1031,true),(1034,true),(1042,false),(1045,true),(1051,true)]
theorem inp_13532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13532 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 28) (closed_mem 29 28) cl_13532 (by decide) v hb
def cl_13533 : CNF.NClause := [(1023,true),(1031,true),(1034,false),(1042,true),(1045,true),(1051,true)]
theorem inp_13533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13533 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 28) (closed_mem 29 28) cl_13533 (by decide) v hb
def cl_13534 : CNF.NClause := [(1023,true),(1031,false),(1034,true),(1042,true),(1045,true),(1051,true)]
theorem inp_13534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13534 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 28) (closed_mem 29 28) cl_13534 (by decide) v hb
def cl_13536 : CNF.NClause := [(1023,true),(1029,true),(1035,true),(1041,true),(1047,true),(1049,false)]
theorem inp_13536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13536 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 29) (closed_mem 29 29) cl_13536 (by decide) v hb
def cl_13538 : CNF.NClause := [(1023,true),(1029,true),(1035,true),(1041,false),(1047,true),(1049,true)]
theorem inp_13538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13538 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 29) (closed_mem 29 29) cl_13538 (by decide) v hb
def cl_13539 : CNF.NClause := [(1023,true),(1029,true),(1035,false),(1041,true),(1047,true),(1049,true)]
theorem inp_13539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13539 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 29) (closed_mem 29 29) cl_13539 (by decide) v hb
def cl_13540 : CNF.NClause := [(1023,true),(1029,false),(1035,true),(1041,true),(1047,true),(1049,true)]
theorem inp_13540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13540 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 29) (closed_mem 29 29) cl_13540 (by decide) v hb
def cl_13543 : CNF.NClause := [(1023,true),(1028,true),(1033,true),(1038,true),(1043,false),(1048,true)]
theorem inp_13543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13543 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 30) (closed_mem 29 30) cl_13543 (by decide) v hb
def cl_13544 : CNF.NClause := [(1023,true),(1028,true),(1033,true),(1038,false),(1043,true),(1048,true)]
theorem inp_13544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13544 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 30) (closed_mem 29 30) cl_13544 (by decide) v hb
def cl_13545 : CNF.NClause := [(1023,true),(1028,true),(1033,false),(1038,true),(1043,true),(1048,true)]
theorem inp_13545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13545 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 30) (closed_mem 29 30) cl_13545 (by decide) v hb
def cl_13546 : CNF.NClause := [(1023,true),(1028,false),(1033,true),(1038,true),(1043,true),(1048,true)]
theorem inp_13546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13546 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 29 30) (closed_mem 29 30) cl_13546 (by decide) v hb
def cl_13548 : CNF.NClause := [(1079,true),(1080,true),(1081,true),(1082,true),(1083,true),(1084,false)]
theorem inp_13548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13548 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13548 v hb
def cl_13555 : CNF.NClause := [(1058,true),(1063,true),(1068,true),(1073,true),(1078,false),(1079,true)]
theorem inp_13555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13555 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 1) (closed_mem 30 1) cl_13555 (by decide) v hb
def cl_13556 : CNF.NClause := [(1058,true),(1063,true),(1068,true),(1073,false),(1078,true),(1079,true)]
theorem inp_13556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13556 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 1) (closed_mem 30 1) cl_13556 (by decide) v hb
def cl_13557 : CNF.NClause := [(1058,true),(1063,true),(1068,false),(1073,true),(1078,true),(1079,true)]
theorem inp_13557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13557 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 1) (closed_mem 30 1) cl_13557 (by decide) v hb
def cl_13558 : CNF.NClause := [(1058,true),(1063,false),(1068,true),(1073,true),(1078,true),(1079,true)]
theorem inp_13558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13558 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 1) (closed_mem 30 1) cl_13558 (by decide) v hb
def cl_13559 : CNF.NClause := [(1058,false),(1063,true),(1068,true),(1073,true),(1078,true),(1079,true)]
theorem inp_13559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13559 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13559 v hb
def cl_13561 : CNF.NClause := [(1056,true),(1061,true),(1066,true),(1071,true),(1076,false),(1079,true)]
theorem inp_13561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13561 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 2) (closed_mem 30 2) cl_13561 (by decide) v hb
def cl_13562 : CNF.NClause := [(1056,true),(1061,true),(1066,true),(1071,false),(1076,true),(1079,true)]
theorem inp_13562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13562 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 2) (closed_mem 30 2) cl_13562 (by decide) v hb
def cl_13563 : CNF.NClause := [(1056,true),(1061,true),(1066,false),(1071,true),(1076,true),(1079,true)]
theorem inp_13563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13563 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 2) (closed_mem 30 2) cl_13563 (by decide) v hb
def cl_13564 : CNF.NClause := [(1056,true),(1061,false),(1066,true),(1071,true),(1076,true),(1079,true)]
theorem inp_13564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13564 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 2) (closed_mem 30 2) cl_13564 (by decide) v hb
def cl_13565 : CNF.NClause := [(1056,false),(1061,true),(1066,true),(1071,true),(1076,true),(1079,true)]
theorem inp_13565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13565 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 2) (closed_mem 30 2) cl_13565 (by decide) v hb
def cl_13567 : CNF.NClause := [(1057,true),(1062,true),(1067,true),(1072,true),(1077,false),(1079,true)]
theorem inp_13567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13567 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13567 v hb
def cl_13568 : CNF.NClause := [(1057,true),(1062,true),(1067,true),(1072,false),(1077,true),(1079,true)]
theorem inp_13568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13568 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 3) (closed_mem 30 3) cl_13568 (by decide) v hb
def cl_13569 : CNF.NClause := [(1057,true),(1062,true),(1067,false),(1072,true),(1077,true),(1079,true)]
theorem inp_13569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13569 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 3) (closed_mem 30 3) cl_13569 (by decide) v hb
def cl_13570 : CNF.NClause := [(1057,true),(1062,false),(1067,true),(1072,true),(1077,true),(1079,true)]
theorem inp_13570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13570 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 3) (closed_mem 30 3) cl_13570 (by decide) v hb
def cl_13571 : CNF.NClause := [(1057,false),(1062,true),(1067,true),(1072,true),(1077,true),(1079,true)]
theorem inp_13571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13571 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 3) (closed_mem 30 3) cl_13571 (by decide) v hb
end Percolation.NReplay
