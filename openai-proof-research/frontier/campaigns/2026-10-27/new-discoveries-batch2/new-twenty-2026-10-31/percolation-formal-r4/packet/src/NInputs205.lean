import NInputs204
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_13633 : CNF.NClause := [(1055,true),(1062,true),(1064,true),(1071,true),(1078,false),(1081,true)]
theorem inp_13633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13633 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13633 v hb
def cl_13634 : CNF.NClause := [(1055,true),(1062,true),(1064,true),(1071,false),(1078,true),(1081,true)]
theorem inp_13634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13634 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 14) (closed_mem 30 14) cl_13634 (by decide) v hb
def cl_13635 : CNF.NClause := [(1055,true),(1062,true),(1064,false),(1071,true),(1078,true),(1081,true)]
theorem inp_13635 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13635 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 14) (closed_mem 30 14) cl_13635 (by decide) v hb
def cl_13636 : CNF.NClause := [(1055,true),(1062,false),(1064,true),(1071,true),(1078,true),(1081,true)]
theorem inp_13636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13636 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13636 v hb
def cl_13637 : CNF.NClause := [(1055,false),(1062,true),(1064,true),(1071,true),(1078,true),(1081,true)]
theorem inp_13637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13637 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 14) (closed_mem 30 14) cl_13637 (by decide) v hb
def cl_13638 : CNF.NClause := [(1069,true),(1070,true),(1071,true),(1072,true),(1073,true),(1084,false)]
theorem inp_13638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13638 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 15) (closed_mem 30 15) cl_13638 (by decide) v hb
def cl_13644 : CNF.NClause := [(1058,true),(1060,true),(1067,true),(1069,true),(1076,true),(1081,false)]
theorem inp_13644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13644 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 16) (closed_mem 30 16) cl_13644 (by decide) v hb
def cl_13645 : CNF.NClause := [(1058,true),(1060,true),(1067,true),(1069,true),(1076,false),(1081,true)]
theorem inp_13645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13645 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 16) (closed_mem 30 16) cl_13645 (by decide) v hb
def cl_13646 : CNF.NClause := [(1058,true),(1060,true),(1067,true),(1069,false),(1076,true),(1081,true)]
theorem inp_13646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13646 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13646 v hb
def cl_13647 : CNF.NClause := [(1058,true),(1060,true),(1067,false),(1069,true),(1076,true),(1081,true)]
theorem inp_13647 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13647 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 16) (closed_mem 30 16) cl_13647 (by decide) v hb
def cl_13648 : CNF.NClause := [(1058,true),(1060,false),(1067,true),(1069,true),(1076,true),(1081,true)]
theorem inp_13648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13648 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 16) (closed_mem 30 16) cl_13648 (by decide) v hb
def cl_13649 : CNF.NClause := [(1058,false),(1060,true),(1067,true),(1069,true),(1076,true),(1081,true)]
theorem inp_13649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13649 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 16) (closed_mem 30 16) cl_13649 (by decide) v hb
def cl_13650 : CNF.NClause := [(1056,true),(1062,true),(1068,true),(1069,true),(1075,true),(1080,false)]
theorem inp_13650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13650 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 17) (closed_mem 30 17) cl_13650 (by decide) v hb
def cl_13651 : CNF.NClause := [(1056,true),(1062,true),(1068,true),(1069,true),(1075,false),(1080,true)]
theorem inp_13651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13651 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 17) (closed_mem 30 17) cl_13651 (by decide) v hb
def cl_13652 : CNF.NClause := [(1056,true),(1062,true),(1068,true),(1069,false),(1075,true),(1080,true)]
theorem inp_13652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13652 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 17) (closed_mem 30 17) cl_13652 (by decide) v hb
def cl_13653 : CNF.NClause := [(1056,true),(1062,true),(1068,false),(1069,true),(1075,true),(1080,true)]
theorem inp_13653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13653 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 17) (closed_mem 30 17) cl_13653 (by decide) v hb
def cl_13654 : CNF.NClause := [(1056,true),(1062,false),(1068,true),(1069,true),(1075,true),(1080,true)]
theorem inp_13654 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13654 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 17) (closed_mem 30 17) cl_13654 (by decide) v hb
def cl_13655 : CNF.NClause := [(1056,false),(1062,true),(1068,true),(1069,true),(1075,true),(1080,true)]
theorem inp_13655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13655 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 17) (closed_mem 30 17) cl_13655 (by decide) v hb
def cl_13656 : CNF.NClause := [(1057,true),(1061,true),(1065,true),(1069,true),(1078,true),(1083,false)]
theorem inp_13656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13656 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 18) (closed_mem 30 18) cl_13656 (by decide) v hb
def cl_13657 : CNF.NClause := [(1057,true),(1061,true),(1065,true),(1069,true),(1078,false),(1083,true)]
theorem inp_13657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13657 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 18) (closed_mem 30 18) cl_13657 (by decide) v hb
def cl_13658 : CNF.NClause := [(1057,true),(1061,true),(1065,true),(1069,false),(1078,true),(1083,true)]
theorem inp_13658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13658 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 18) (closed_mem 30 18) cl_13658 (by decide) v hb
def cl_13659 : CNF.NClause := [(1057,true),(1061,true),(1065,false),(1069,true),(1078,true),(1083,true)]
theorem inp_13659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13659 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 18) (closed_mem 30 18) cl_13659 (by decide) v hb
def cl_13660 : CNF.NClause := [(1057,true),(1061,false),(1065,true),(1069,true),(1078,true),(1083,true)]
theorem inp_13660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13660 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 18) (closed_mem 30 18) cl_13660 (by decide) v hb
def cl_13661 : CNF.NClause := [(1057,false),(1061,true),(1065,true),(1069,true),(1078,true),(1083,true)]
theorem inp_13661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13661 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 18) (closed_mem 30 18) cl_13661 (by decide) v hb
def cl_13662 : CNF.NClause := [(1055,true),(1063,true),(1066,true),(1069,true),(1077,true),(1082,false)]
theorem inp_13662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13662 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 19) (closed_mem 30 19) cl_13662 (by decide) v hb
def cl_13663 : CNF.NClause := [(1055,true),(1063,true),(1066,true),(1069,true),(1077,false),(1082,true)]
theorem inp_13663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13663 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 19) (closed_mem 30 19) cl_13663 (by decide) v hb
def cl_13664 : CNF.NClause := [(1055,true),(1063,true),(1066,true),(1069,false),(1077,true),(1082,true)]
theorem inp_13664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13664 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 19) (closed_mem 30 19) cl_13664 (by decide) v hb
def cl_13665 : CNF.NClause := [(1055,true),(1063,true),(1066,false),(1069,true),(1077,true),(1082,true)]
theorem inp_13665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13665 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 19) (closed_mem 30 19) cl_13665 (by decide) v hb
def cl_13666 : CNF.NClause := [(1055,true),(1063,false),(1066,true),(1069,true),(1077,true),(1082,true)]
theorem inp_13666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13666 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 19) (closed_mem 30 19) cl_13666 (by decide) v hb
def cl_13667 : CNF.NClause := [(1055,false),(1063,true),(1066,true),(1069,true),(1077,true),(1082,true)]
theorem inp_13667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13667 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 19) (closed_mem 30 19) cl_13667 (by decide) v hb
def cl_13668 : CNF.NClause := [(1059,true),(1060,true),(1061,true),(1062,true),(1063,true),(1084,false)]
theorem inp_13668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13668 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13668 v hb
def cl_13674 : CNF.NClause := [(1058,true),(1059,true),(1065,true),(1071,true),(1077,true),(1080,false)]
theorem inp_13674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13674 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 21) (closed_mem 30 21) cl_13674 (by decide) v hb
def cl_13675 : CNF.NClause := [(1058,true),(1059,true),(1065,true),(1071,true),(1077,false),(1080,true)]
theorem inp_13675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13675 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13675 v hb
def cl_13676 : CNF.NClause := [(1058,true),(1059,true),(1065,true),(1071,false),(1077,true),(1080,true)]
theorem inp_13676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13676 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13676 v hb
def cl_13677 : CNF.NClause := [(1058,true),(1059,true),(1065,false),(1071,true),(1077,true),(1080,true)]
theorem inp_13677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13677 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13677 v hb
def cl_13678 : CNF.NClause := [(1058,true),(1059,false),(1065,true),(1071,true),(1077,true),(1080,true)]
theorem inp_13678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13678 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 21) (closed_mem 30 21) cl_13678 (by decide) v hb
def cl_13679 : CNF.NClause := [(1058,false),(1059,true),(1065,true),(1071,true),(1077,true),(1080,true)]
theorem inp_13679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13679 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 21) (closed_mem 30 21) cl_13679 (by decide) v hb
def cl_13680 : CNF.NClause := [(1056,true),(1059,true),(1067,true),(1070,true),(1078,true),(1082,false)]
theorem inp_13680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13680 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 22) (closed_mem 30 22) cl_13680 (by decide) v hb
def cl_13681 : CNF.NClause := [(1056,true),(1059,true),(1067,true),(1070,true),(1078,false),(1082,true)]
theorem inp_13681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13681 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 22) (closed_mem 30 22) cl_13681 (by decide) v hb
def cl_13682 : CNF.NClause := [(1056,true),(1059,true),(1067,true),(1070,false),(1078,true),(1082,true)]
theorem inp_13682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13682 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 22) (closed_mem 30 22) cl_13682 (by decide) v hb
def cl_13683 : CNF.NClause := [(1056,true),(1059,true),(1067,false),(1070,true),(1078,true),(1082,true)]
theorem inp_13683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13683 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 22) (closed_mem 30 22) cl_13683 (by decide) v hb
def cl_13684 : CNF.NClause := [(1056,true),(1059,false),(1067,true),(1070,true),(1078,true),(1082,true)]
theorem inp_13684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13684 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 22) (closed_mem 30 22) cl_13684 (by decide) v hb
def cl_13685 : CNF.NClause := [(1056,false),(1059,true),(1067,true),(1070,true),(1078,true),(1082,true)]
theorem inp_13685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13685 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 22) (closed_mem 30 22) cl_13685 (by decide) v hb
def cl_13686 : CNF.NClause := [(1057,true),(1059,true),(1066,true),(1073,true),(1075,true),(1081,false)]
theorem inp_13686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13686 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 23) (closed_mem 30 23) cl_13686 (by decide) v hb
def cl_13687 : CNF.NClause := [(1057,true),(1059,true),(1066,true),(1073,true),(1075,false),(1081,true)]
theorem inp_13687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13687 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 23) (closed_mem 30 23) cl_13687 (by decide) v hb
def cl_13688 : CNF.NClause := [(1057,true),(1059,true),(1066,true),(1073,false),(1075,true),(1081,true)]
theorem inp_13688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13688 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 23) (closed_mem 30 23) cl_13688 (by decide) v hb
def cl_13689 : CNF.NClause := [(1057,true),(1059,true),(1066,false),(1073,true),(1075,true),(1081,true)]
theorem inp_13689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13689 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 23) (closed_mem 30 23) cl_13689 (by decide) v hb
def cl_13690 : CNF.NClause := [(1057,true),(1059,false),(1066,true),(1073,true),(1075,true),(1081,true)]
theorem inp_13690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13690 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 23) (closed_mem 30 23) cl_13690 (by decide) v hb
def cl_13691 : CNF.NClause := [(1057,false),(1059,true),(1066,true),(1073,true),(1075,true),(1081,true)]
theorem inp_13691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13691 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 30 23) (closed_mem 30 23) cl_13691 (by decide) v hb
def cl_13692 : CNF.NClause := [(1055,true),(1059,true),(1068,true),(1072,true),(1076,true),(1083,false)]
theorem inp_13692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13692 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13692 v hb
end Percolation.NReplay
