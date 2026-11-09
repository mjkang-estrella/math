import NInputs205
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_13693 : CNF.NClause := [(1055,true),(1059,true),(1068,true),(1072,true),(1076,false),(1083,true)]
theorem inp_13693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13693 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13693 v hb
def cl_13694 : CNF.NClause := [(1055,true),(1059,true),(1068,true),(1072,false),(1076,true),(1083,true)]
theorem inp_13694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13694 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 24) (closed_mem 30 24) cl_13694 (by decide) v hb
def cl_13695 : CNF.NClause := [(1055,true),(1059,true),(1068,false),(1072,true),(1076,true),(1083,true)]
theorem inp_13695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13695 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 24) (closed_mem 30 24) cl_13695 (by decide) v hb
def cl_13696 : CNF.NClause := [(1055,true),(1059,false),(1068,true),(1072,true),(1076,true),(1083,true)]
theorem inp_13696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13696 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 24) (closed_mem 30 24) cl_13696 (by decide) v hb
def cl_13697 : CNF.NClause := [(1055,false),(1059,true),(1068,true),(1072,true),(1076,true),(1083,true)]
theorem inp_13697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13697 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 24) (closed_mem 30 24) cl_13697 (by decide) v hb
def cl_13698 : CNF.NClause := [(1054,true),(1055,true),(1056,true),(1057,true),(1058,true),(1084,false)]
theorem inp_13698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13698 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13698 v hb
def cl_13704 : CNF.NClause := [(1054,true),(1063,true),(1067,true),(1071,true),(1075,true),(1083,false)]
theorem inp_13704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13704 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 26) (closed_mem 30 26) cl_13704 (by decide) v hb
def cl_13705 : CNF.NClause := [(1054,true),(1063,true),(1067,true),(1071,true),(1075,false),(1083,true)]
theorem inp_13705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13705 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 26) (closed_mem 30 26) cl_13705 (by decide) v hb
def cl_13706 : CNF.NClause := [(1054,true),(1063,true),(1067,true),(1071,false),(1075,true),(1083,true)]
theorem inp_13706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13706 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 26) (closed_mem 30 26) cl_13706 (by decide) v hb
def cl_13707 : CNF.NClause := [(1054,true),(1063,true),(1067,false),(1071,true),(1075,true),(1083,true)]
theorem inp_13707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13707 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 26) (closed_mem 30 26) cl_13707 (by decide) v hb
def cl_13708 : CNF.NClause := [(1054,true),(1063,false),(1067,true),(1071,true),(1075,true),(1083,true)]
theorem inp_13708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13708 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 26) (closed_mem 30 26) cl_13708 (by decide) v hb
def cl_13710 : CNF.NClause := [(1054,true),(1061,true),(1068,true),(1070,true),(1077,true),(1081,false)]
theorem inp_13710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13710 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 27) (closed_mem 30 27) cl_13710 (by decide) v hb
def cl_13711 : CNF.NClause := [(1054,true),(1061,true),(1068,true),(1070,true),(1077,false),(1081,true)]
theorem inp_13711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13711 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 27) (closed_mem 30 27) cl_13711 (by decide) v hb
def cl_13712 : CNF.NClause := [(1054,true),(1061,true),(1068,true),(1070,false),(1077,true),(1081,true)]
theorem inp_13712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13712 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 27) (closed_mem 30 27) cl_13712 (by decide) v hb
def cl_13713 : CNF.NClause := [(1054,true),(1061,true),(1068,false),(1070,true),(1077,true),(1081,true)]
theorem inp_13713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13713 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 27) (closed_mem 30 27) cl_13713 (by decide) v hb
def cl_13714 : CNF.NClause := [(1054,true),(1061,false),(1068,true),(1070,true),(1077,true),(1081,true)]
theorem inp_13714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13714 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 27) (closed_mem 30 27) cl_13714 (by decide) v hb
def cl_13716 : CNF.NClause := [(1054,true),(1062,true),(1065,true),(1073,true),(1076,true),(1082,false)]
theorem inp_13716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13716 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 28) (closed_mem 30 28) cl_13716 (by decide) v hb
def cl_13717 : CNF.NClause := [(1054,true),(1062,true),(1065,true),(1073,true),(1076,false),(1082,true)]
theorem inp_13717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13717 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 28) (closed_mem 30 28) cl_13717 (by decide) v hb
def cl_13718 : CNF.NClause := [(1054,true),(1062,true),(1065,true),(1073,false),(1076,true),(1082,true)]
theorem inp_13718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13718 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 28) (closed_mem 30 28) cl_13718 (by decide) v hb
def cl_13719 : CNF.NClause := [(1054,true),(1062,true),(1065,false),(1073,true),(1076,true),(1082,true)]
theorem inp_13719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13719 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 28) (closed_mem 30 28) cl_13719 (by decide) v hb
def cl_13720 : CNF.NClause := [(1054,true),(1062,false),(1065,true),(1073,true),(1076,true),(1082,true)]
theorem inp_13720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13720 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 28) (closed_mem 30 28) cl_13720 (by decide) v hb
def cl_13722 : CNF.NClause := [(1054,true),(1060,true),(1066,true),(1072,true),(1078,true),(1080,false)]
theorem inp_13722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13722 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13722 v hb
def cl_13723 : CNF.NClause := [(1054,true),(1060,true),(1066,true),(1072,true),(1078,false),(1080,true)]
theorem inp_13723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13723 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 29) (closed_mem 30 29) cl_13723 (by decide) v hb
def cl_13724 : CNF.NClause := [(1054,true),(1060,true),(1066,true),(1072,false),(1078,true),(1080,true)]
theorem inp_13724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13724 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 29) (closed_mem 30 29) cl_13724 (by decide) v hb
def cl_13725 : CNF.NClause := [(1054,true),(1060,true),(1066,false),(1072,true),(1078,true),(1080,true)]
theorem inp_13725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13725 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 29) (closed_mem 30 29) cl_13725 (by decide) v hb
def cl_13726 : CNF.NClause := [(1054,true),(1060,false),(1066,true),(1072,true),(1078,true),(1080,true)]
theorem inp_13726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13726 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 29) (closed_mem 30 29) cl_13726 (by decide) v hb
def cl_13729 : CNF.NClause := [(1054,true),(1059,true),(1064,true),(1069,true),(1074,false),(1079,true)]
theorem inp_13729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13729 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13729 v hb
def cl_13730 : CNF.NClause := [(1054,true),(1059,true),(1064,true),(1069,false),(1074,true),(1079,true)]
theorem inp_13730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13730 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 30) (closed_mem 30 30) cl_13730 (by decide) v hb
def cl_13731 : CNF.NClause := [(1054,true),(1059,true),(1064,false),(1069,true),(1074,true),(1079,true)]
theorem inp_13731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13731 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 30) (closed_mem 30 30) cl_13731 (by decide) v hb
def cl_13732 : CNF.NClause := [(1054,true),(1059,false),(1064,true),(1069,true),(1074,true),(1079,true)]
theorem inp_13732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13732 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 30) (closed_mem 30 30) cl_13732 (by decide) v hb
def cl_13735 : CNF.NClause := [(0,true),(124,true)]
theorem inp_13735 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13735 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13735 = (omitClause5 0) := by decide
  rw [he]
  exact input_omit 0 v hb
def cl_13736 : CNF.NClause := [(1,true),(156,true)]
theorem inp_13736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13736 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13736 = (omitClause5 1) := by decide
  rw [he]
  exact input_omit 1 v hb
def cl_13737 : CNF.NClause := [(2,true),(188,true)]
theorem inp_13737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13737 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13737 = (omitClause5 2) := by decide
  rw [he]
  exact input_omit 2 v hb
def cl_13738 : CNF.NClause := [(3,true),(220,true)]
theorem inp_13738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13738 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13738 = (omitClause5 3) := by decide
  rw [he]
  exact input_omit 3 v hb
def cl_13739 : CNF.NClause := [(4,true),(252,true)]
theorem inp_13739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13739 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13739 = (omitClause5 4) := by decide
  rw [he]
  exact input_omit 4 v hb
def cl_13740 : CNF.NClause := [(5,true),(284,true)]
theorem inp_13740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13740 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13740 v hb
def cl_13741 : CNF.NClause := [(6,true),(316,true)]
theorem inp_13741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13741 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13741 = (omitClause5 6) := by decide
  rw [he]
  exact input_omit 6 v hb
def cl_13742 : CNF.NClause := [(7,true),(348,true)]
theorem inp_13742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13742 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13742 v hb
def cl_13743 : CNF.NClause := [(8,true),(380,true)]
theorem inp_13743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13743 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13743 v hb
def cl_13744 : CNF.NClause := [(9,true),(412,true)]
theorem inp_13744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13744 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13744 v hb
def cl_13745 : CNF.NClause := [(10,true),(444,true)]
theorem inp_13745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13745 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13745 v hb
def cl_13746 : CNF.NClause := [(11,true),(476,true)]
theorem inp_13746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13746 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13746 v hb
def cl_13747 : CNF.NClause := [(12,true),(508,true)]
theorem inp_13747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13747 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13747 = (omitClause5 12) := by decide
  rw [he]
  exact input_omit 12 v hb
def cl_13748 : CNF.NClause := [(13,true),(540,true)]
theorem inp_13748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13748 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13748 = (omitClause5 13) := by decide
  rw [he]
  exact input_omit 13 v hb
def cl_13749 : CNF.NClause := [(14,true),(572,true)]
theorem inp_13749 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13749 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13749 = (omitClause5 14) := by decide
  rw [he]
  exact input_omit 14 v hb
def cl_13750 : CNF.NClause := [(15,true),(604,true)]
theorem inp_13750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13750 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13750 = (omitClause5 15) := by decide
  rw [he]
  exact input_omit 15 v hb
def cl_13751 : CNF.NClause := [(16,true),(636,true)]
theorem inp_13751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13751 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13751 = (omitClause5 16) := by decide
  rw [he]
  exact input_omit 16 v hb
def cl_13752 : CNF.NClause := [(17,true),(668,true)]
theorem inp_13752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13752 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13752 = (omitClause5 17) := by decide
  rw [he]
  exact input_omit 17 v hb
def cl_13753 : CNF.NClause := [(18,true),(700,true)]
theorem inp_13753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13753 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13753 = (omitClause5 18) := by decide
  rw [he]
  exact input_omit 18 v hb
def cl_13754 : CNF.NClause := [(19,true),(732,true)]
theorem inp_13754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13754 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13754 v hb
end Percolation.NReplay
