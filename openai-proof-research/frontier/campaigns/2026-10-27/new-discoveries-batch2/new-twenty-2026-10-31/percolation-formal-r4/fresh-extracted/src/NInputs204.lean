import NInputs203
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_13573 : CNF.NClause := [(1055,true),(1060,true),(1065,true),(1070,true),(1075,false),(1079,true)]
theorem inp_13573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13573 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 4) (closed_mem 30 4) cl_13573 (by decide) v hb
def cl_13574 : CNF.NClause := [(1055,true),(1060,true),(1065,true),(1070,false),(1075,true),(1079,true)]
theorem inp_13574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13574 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 4) (closed_mem 30 4) cl_13574 (by decide) v hb
def cl_13575 : CNF.NClause := [(1055,true),(1060,true),(1065,false),(1070,true),(1075,true),(1079,true)]
theorem inp_13575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13575 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 4) (closed_mem 30 4) cl_13575 (by decide) v hb
def cl_13576 : CNF.NClause := [(1055,true),(1060,false),(1065,true),(1070,true),(1075,true),(1079,true)]
theorem inp_13576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13576 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 4) (closed_mem 30 4) cl_13576 (by decide) v hb
def cl_13577 : CNF.NClause := [(1055,false),(1060,true),(1065,true),(1070,true),(1075,true),(1079,true)]
theorem inp_13577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13577 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 4) (closed_mem 30 4) cl_13577 (by decide) v hb
def cl_13578 : CNF.NClause := [(1074,true),(1075,true),(1076,true),(1077,true),(1078,true),(1084,false)]
theorem inp_13578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13578 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13578 v hb
def cl_13584 : CNF.NClause := [(1058,true),(1062,true),(1066,true),(1070,true),(1074,true),(1083,false)]
theorem inp_13584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13584 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 6) (closed_mem 30 6) cl_13584 (by decide) v hb
def cl_13585 : CNF.NClause := [(1058,true),(1062,true),(1066,true),(1070,true),(1074,false),(1083,true)]
theorem inp_13585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13585 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 6) (closed_mem 30 6) cl_13585 (by decide) v hb
def cl_13586 : CNF.NClause := [(1058,true),(1062,true),(1066,true),(1070,false),(1074,true),(1083,true)]
theorem inp_13586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13586 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 6) (closed_mem 30 6) cl_13586 (by decide) v hb
def cl_13587 : CNF.NClause := [(1058,true),(1062,true),(1066,false),(1070,true),(1074,true),(1083,true)]
theorem inp_13587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13587 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 6) (closed_mem 30 6) cl_13587 (by decide) v hb
def cl_13588 : CNF.NClause := [(1058,true),(1062,false),(1066,true),(1070,true),(1074,true),(1083,true)]
theorem inp_13588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13588 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 6) (closed_mem 30 6) cl_13588 (by decide) v hb
def cl_13589 : CNF.NClause := [(1058,false),(1062,true),(1066,true),(1070,true),(1074,true),(1083,true)]
theorem inp_13589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13589 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 6) (closed_mem 30 6) cl_13589 (by decide) v hb
def cl_13590 : CNF.NClause := [(1056,true),(1063,true),(1065,true),(1072,true),(1074,true),(1081,false)]
theorem inp_13590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13590 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 7) (closed_mem 30 7) cl_13590 (by decide) v hb
def cl_13591 : CNF.NClause := [(1056,true),(1063,true),(1065,true),(1072,true),(1074,false),(1081,true)]
theorem inp_13591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13591 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 7) (closed_mem 30 7) cl_13591 (by decide) v hb
def cl_13592 : CNF.NClause := [(1056,true),(1063,true),(1065,true),(1072,false),(1074,true),(1081,true)]
theorem inp_13592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13592 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 7) (closed_mem 30 7) cl_13592 (by decide) v hb
def cl_13593 : CNF.NClause := [(1056,true),(1063,true),(1065,false),(1072,true),(1074,true),(1081,true)]
theorem inp_13593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13593 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 7) (closed_mem 30 7) cl_13593 (by decide) v hb
def cl_13594 : CNF.NClause := [(1056,true),(1063,false),(1065,true),(1072,true),(1074,true),(1081,true)]
theorem inp_13594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13594 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 7) (closed_mem 30 7) cl_13594 (by decide) v hb
def cl_13595 : CNF.NClause := [(1056,false),(1063,true),(1065,true),(1072,true),(1074,true),(1081,true)]
theorem inp_13595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13595 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 7) (closed_mem 30 7) cl_13595 (by decide) v hb
def cl_13596 : CNF.NClause := [(1057,true),(1060,true),(1068,true),(1071,true),(1074,true),(1082,false)]
theorem inp_13596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13596 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 8) (closed_mem 30 8) cl_13596 (by decide) v hb
def cl_13597 : CNF.NClause := [(1057,true),(1060,true),(1068,true),(1071,true),(1074,false),(1082,true)]
theorem inp_13597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13597 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 8) (closed_mem 30 8) cl_13597 (by decide) v hb
def cl_13598 : CNF.NClause := [(1057,true),(1060,true),(1068,true),(1071,false),(1074,true),(1082,true)]
theorem inp_13598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13598 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 8) (closed_mem 30 8) cl_13598 (by decide) v hb
def cl_13599 : CNF.NClause := [(1057,true),(1060,true),(1068,false),(1071,true),(1074,true),(1082,true)]
theorem inp_13599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13599 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 8) (closed_mem 30 8) cl_13599 (by decide) v hb
def cl_13600 : CNF.NClause := [(1057,true),(1060,false),(1068,true),(1071,true),(1074,true),(1082,true)]
theorem inp_13600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13600 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 8) (closed_mem 30 8) cl_13600 (by decide) v hb
def cl_13601 : CNF.NClause := [(1057,false),(1060,true),(1068,true),(1071,true),(1074,true),(1082,true)]
theorem inp_13601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13601 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13601 v hb
def cl_13602 : CNF.NClause := [(1055,true),(1061,true),(1067,true),(1073,true),(1074,true),(1080,false)]
theorem inp_13602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13602 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 9) (closed_mem 30 9) cl_13602 (by decide) v hb
def cl_13603 : CNF.NClause := [(1055,true),(1061,true),(1067,true),(1073,true),(1074,false),(1080,true)]
theorem inp_13603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13603 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13603 v hb
def cl_13604 : CNF.NClause := [(1055,true),(1061,true),(1067,true),(1073,false),(1074,true),(1080,true)]
theorem inp_13604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13604 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 9) (closed_mem 30 9) cl_13604 (by decide) v hb
def cl_13605 : CNF.NClause := [(1055,true),(1061,true),(1067,false),(1073,true),(1074,true),(1080,true)]
theorem inp_13605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13605 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 9) (closed_mem 30 9) cl_13605 (by decide) v hb
def cl_13606 : CNF.NClause := [(1055,true),(1061,false),(1067,true),(1073,true),(1074,true),(1080,true)]
theorem inp_13606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13606 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13606 v hb
def cl_13607 : CNF.NClause := [(1055,false),(1061,true),(1067,true),(1073,true),(1074,true),(1080,true)]
theorem inp_13607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13607 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 9) (closed_mem 30 9) cl_13607 (by decide) v hb
def cl_13608 : CNF.NClause := [(1064,true),(1065,true),(1066,true),(1067,true),(1068,true),(1084,false)]
theorem inp_13608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13608 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 10) (closed_mem 30 10) cl_13608 (by decide) v hb
def cl_13614 : CNF.NClause := [(1058,true),(1061,true),(1064,true),(1072,true),(1075,true),(1082,false)]
theorem inp_13614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13614 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 11) (closed_mem 30 11) cl_13614 (by decide) v hb
def cl_13615 : CNF.NClause := [(1058,true),(1061,true),(1064,true),(1072,true),(1075,false),(1082,true)]
theorem inp_13615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13615 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 11) (closed_mem 30 11) cl_13615 (by decide) v hb
def cl_13616 : CNF.NClause := [(1058,true),(1061,true),(1064,true),(1072,false),(1075,true),(1082,true)]
theorem inp_13616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13616 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13616 v hb
def cl_13617 : CNF.NClause := [(1058,true),(1061,true),(1064,false),(1072,true),(1075,true),(1082,true)]
theorem inp_13617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13617 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 11) (closed_mem 30 11) cl_13617 (by decide) v hb
def cl_13618 : CNF.NClause := [(1058,true),(1061,false),(1064,true),(1072,true),(1075,true),(1082,true)]
theorem inp_13618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13618 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 11) (closed_mem 30 11) cl_13618 (by decide) v hb
def cl_13619 : CNF.NClause := [(1058,false),(1061,true),(1064,true),(1072,true),(1075,true),(1082,true)]
theorem inp_13619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13619 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 11) (closed_mem 30 11) cl_13619 (by decide) v hb
def cl_13620 : CNF.NClause := [(1056,true),(1060,true),(1064,true),(1073,true),(1077,true),(1083,false)]
theorem inp_13620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13620 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 12) (closed_mem 30 12) cl_13620 (by decide) v hb
def cl_13621 : CNF.NClause := [(1056,true),(1060,true),(1064,true),(1073,true),(1077,false),(1083,true)]
theorem inp_13621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13621 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 12) (closed_mem 30 12) cl_13621 (by decide) v hb
def cl_13622 : CNF.NClause := [(1056,true),(1060,true),(1064,true),(1073,false),(1077,true),(1083,true)]
theorem inp_13622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13622 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 12) (closed_mem 30 12) cl_13622 (by decide) v hb
def cl_13623 : CNF.NClause := [(1056,true),(1060,true),(1064,false),(1073,true),(1077,true),(1083,true)]
theorem inp_13623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13623 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 12) (closed_mem 30 12) cl_13623 (by decide) v hb
def cl_13624 : CNF.NClause := [(1056,true),(1060,false),(1064,true),(1073,true),(1077,true),(1083,true)]
theorem inp_13624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13624 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 12) (closed_mem 30 12) cl_13624 (by decide) v hb
def cl_13625 : CNF.NClause := [(1056,false),(1060,true),(1064,true),(1073,true),(1077,true),(1083,true)]
theorem inp_13625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13625 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13625 v hb
def cl_13626 : CNF.NClause := [(1057,true),(1063,true),(1064,true),(1070,true),(1076,true),(1080,false)]
theorem inp_13626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13626 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 13) (closed_mem 30 13) cl_13626 (by decide) v hb
def cl_13627 : CNF.NClause := [(1057,true),(1063,true),(1064,true),(1070,true),(1076,false),(1080,true)]
theorem inp_13627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13627 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 13) (closed_mem 30 13) cl_13627 (by decide) v hb
def cl_13628 : CNF.NClause := [(1057,true),(1063,true),(1064,true),(1070,false),(1076,true),(1080,true)]
theorem inp_13628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13628 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 13) (closed_mem 30 13) cl_13628 (by decide) v hb
def cl_13629 : CNF.NClause := [(1057,true),(1063,true),(1064,false),(1070,true),(1076,true),(1080,true)]
theorem inp_13629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13629 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 13) (closed_mem 30 13) cl_13629 (by decide) v hb
def cl_13630 : CNF.NClause := [(1057,true),(1063,false),(1064,true),(1070,true),(1076,true),(1080,true)]
theorem inp_13630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13630 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 13) (closed_mem 30 13) cl_13630 (by decide) v hb
def cl_13631 : CNF.NClause := [(1057,false),(1063,true),(1064,true),(1070,true),(1076,true),(1080,true)]
theorem inp_13631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13631 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 13) (closed_mem 30 13) cl_13631 (by decide) v hb
def cl_13632 : CNF.NClause := [(1055,true),(1062,true),(1064,true),(1071,true),(1078,true),(1081,false)]
theorem inp_13632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13632 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 14) (closed_mem 30 14) cl_13632 (by decide) v hb
end Percolation.NReplay
