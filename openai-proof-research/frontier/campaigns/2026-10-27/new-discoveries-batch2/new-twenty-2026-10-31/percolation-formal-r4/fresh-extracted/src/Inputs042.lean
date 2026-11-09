import Inputs041
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_11609 : CNF.NClause := [(715,false),(721,true),(727,true),(728,true),(734,true),(739,true)]
theorem inp_11609 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11609 := by
  exact input_gate (closedGate5 19 17) (closed_mem 19 17) cl_11609 (by decide) v h
def cl_11625 : CNF.NClause := [(718,true),(719,true),(720,false),(721,true),(722,true),(743,true)]
theorem inp_11625 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11625 := by
  exact input_gate (closedGate5 19 20) (closed_mem 19 20) cl_11625 (by decide) v h
def cl_11626 : CNF.NClause := [(718,true),(719,false),(720,true),(721,true),(722,true),(743,true)]
theorem inp_11626 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11626 := by
  exact input_gate (closedGate5 19 20) (closed_mem 19 20) cl_11626 (by decide) v h
def cl_11631 : CNF.NClause := [(717,true),(718,true),(724,false),(730,true),(736,true),(739,true)]
theorem inp_11631 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11631 := by
  exact input_gate (closedGate5 19 21) (closed_mem 19 21) cl_11631 (by decide) v h
def cl_11642 : CNF.NClause := [(716,true),(718,true),(725,true),(732,false),(734,true),(740,true)]
theorem inp_11642 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11642 := by
  exact input_gate (closedGate5 19 23) (closed_mem 19 23) cl_11642 (by decide) v h
def cl_11656 : CNF.NClause := [(713,true),(714,false),(715,true),(716,true),(717,true),(743,true)]
theorem inp_11656 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11656 := by
  exact input_gate (closedGate5 19 25) (closed_mem 19 25) cl_11656 (by decide) v h
def cl_11662 : CNF.NClause := [(713,true),(722,false),(726,true),(730,true),(734,true),(742,true)]
theorem inp_11662 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11662 := by
  exact input_gate (closedGate5 19 26) (closed_mem 19 26) cl_11662 (by decide) v h
def cl_11669 : CNF.NClause := [(713,false),(720,true),(727,true),(729,true),(736,true),(740,true)]
theorem inp_11669 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11669 := by
  exact input_gate (closedGate5 19 27) (closed_mem 19 27) cl_11669 (by decide) v h
def cl_11899 : CNF.NClause := [(776,true),(781,true),(786,true),(791,true),(796,false),(800,true)]
theorem inp_11899 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11899 := by
  exact input_gate (closedGate5 21 4) (closed_mem 21 4) cl_11899 (by decide) v h
def cl_11962 : CNF.NClause := [(776,true),(783,false),(785,true),(792,true),(799,true),(802,true)]
theorem inp_11962 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11962 := by
  exact input_gate (closedGate5 21 14) (closed_mem 21 14) cl_11962 (by decide) v h
def cl_12009 : CNF.NClause := [(777,true),(780,true),(788,false),(791,true),(799,true),(803,true)]
theorem inp_12009 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12009 := by
  exact input_gate (closedGate5 21 22) (closed_mem 21 22) cl_12009 (by decide) v h
def cl_12046 : CNF.NClause := [(775,true),(783,false),(786,true),(794,true),(797,true),(803,true)]
theorem inp_12046 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12046 := by
  exact input_gate (closedGate5 21 28) (closed_mem 21 28) cl_12046 (by decide) v h
def cl_12093 : CNF.NClause := [(826,true),(827,true),(828,false),(829,true),(830,true),(836,true)]
theorem inp_12093 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12093 := by
  exact input_gate (closedGate5 22 5) (closed_mem 22 5) cl_12093 (by decide) v h
def cl_12133 : CNF.NClause := [(808,true),(812,true),(816,true),(825,true),(829,false),(835,true)]
theorem inp_12133 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12133 := by
  exact input_gate (closedGate5 22 12) (closed_mem 22 12) cl_12133 (by decide) v h
def cl_13038 : CNF.NClause := [(964,true),(967,true),(975,true),(978,true),(981,true),(989,false)]
theorem inp_13038 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13038 := by
  exact input_gate (closedGate5 27 8) (closed_mem 27 8) cl_13038 (by decide) v h
def cl_13061 : CNF.NClause := [(965,false),(968,true),(971,true),(979,true),(982,true),(989,true)]
theorem inp_13061 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13061 := by
  exact input_gate (closedGate5 27 11) (closed_mem 27 11) cl_13061 (by decide) v h
def cl_13085 : CNF.NClause := [(976,false),(977,true),(978,true),(979,true),(980,true),(991,true)]
theorem inp_13085 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13085 := by
  exact input_gate (closedGate5 27 15) (closed_mem 27 15) cl_13085 (by decide) v h
def cl_13086 : CNF.NClause := [(965,true),(967,true),(974,true),(976,true),(983,true),(988,false)]
theorem inp_13086 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13086 := by
  exact input_gate (closedGate5 27 16) (closed_mem 27 16) cl_13086 (by decide) v h
def cl_13094 : CNF.NClause := [(963,true),(969,true),(975,true),(976,false),(982,true),(987,true)]
theorem inp_13094 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13094 := by
  exact input_gate (closedGate5 27 17) (closed_mem 27 17) cl_13094 (by decide) v h
def cl_13193 : CNF.NClause := [(994,false),(999,true),(1004,true),(1009,true),(1014,true),(1017,true)]
theorem inp_13193 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13193 := by
  exact input_gate (closedGate5 28 2) (closed_mem 28 2) cl_13193 (by decide) v h
def cl_13197 : CNF.NClause := [(995,true),(1000,true),(1005,false),(1010,true),(1015,true),(1017,true)]
theorem inp_13197 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13197 := by
  exact input_gate (closedGate5 28 3) (closed_mem 28 3) cl_13197 (by decide) v h
def cl_13224 : CNF.NClause := [(995,true),(998,true),(1006,true),(1009,true),(1012,true),(1020,false)]
theorem inp_13224 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13224 := by
  exact input_gate (closedGate5 28 8) (closed_mem 28 8) cl_13224 (by decide) v h
def cl_13242 : CNF.NClause := [(996,true),(999,true),(1002,true),(1010,true),(1013,true),(1020,false)]
theorem inp_13242 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13242 := by
  exact input_gate (closedGate5 28 11) (closed_mem 28 11) cl_13242 (by decide) v h
def cl_13268 : CNF.NClause := [(1007,true),(1008,true),(1009,true),(1010,false),(1011,true),(1022,true)]
theorem inp_13268 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13268 := by
  exact input_gate (closedGate5 28 15) (closed_mem 28 15) cl_13268 (by decide) v h
def cl_13277 : CNF.NClause := [(996,false),(998,true),(1005,true),(1007,true),(1014,true),(1019,true)]
theorem inp_13277 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13277 := by
  exact input_gate (closedGate5 28 16) (closed_mem 28 16) cl_13277 (by decide) v h
def cl_13281 : CNF.NClause := [(994,true),(1000,true),(1006,false),(1007,true),(1013,true),(1018,true)]
theorem inp_13281 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13281 := by
  exact input_gate (closedGate5 28 17) (closed_mem 28 17) cl_13281 (by decide) v h
def cl_13317 : CNF.NClause := [(995,true),(997,true),(1004,false),(1011,true),(1013,true),(1019,true)]
theorem inp_13317 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13317 := by
  exact input_gate (closedGate5 28 23) (closed_mem 28 23) cl_13317 (by decide) v h
def cl_13339 : CNF.NClause := [(992,true),(999,true),(1006,true),(1008,true),(1015,false),(1019,true)]
theorem inp_13339 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13339 := by
  exact input_gate (closedGate5 28 27) (closed_mem 28 27) cl_13339 (by decide) v h
def cl_13356 : CNF.NClause := [(992,true),(997,true),(1002,true),(1007,true),(1012,true),(1017,false)]
theorem inp_13356 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13356 := by
  exact input_gate (closedGate5 28 30) (closed_mem 28 30) cl_13356 (by decide) v h
def cl_13357 : CNF.NClause := [(992,true),(997,true),(1002,true),(1007,true),(1012,false),(1017,true)]
theorem inp_13357 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13357 := by
  exact input_gate (closedGate5 28 30) (closed_mem 28 30) cl_13357 (by decide) v h
def cl_13548 : CNF.NClause := [(1079,true),(1080,true),(1081,true),(1082,true),(1083,true),(1084,false)]
theorem inp_13548 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13548 := by
  exact input_gate (closedGate5 30 0) (closed_mem 30 0) cl_13548 (by decide) v h
def cl_13554 : CNF.NClause := [(1058,true),(1063,true),(1068,true),(1073,true),(1078,true),(1079,false)]
theorem inp_13554 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13554 := by
  exact input_gate (closedGate5 30 1) (closed_mem 30 1) cl_13554 (by decide) v h
def cl_13559 : CNF.NClause := [(1058,false),(1063,true),(1068,true),(1073,true),(1078,true),(1079,true)]
theorem inp_13559 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13559 := by
  exact input_gate (closedGate5 30 1) (closed_mem 30 1) cl_13559 (by decide) v h
def cl_13567 : CNF.NClause := [(1057,true),(1062,true),(1067,true),(1072,true),(1077,false),(1079,true)]
theorem inp_13567 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13567 := by
  exact input_gate (closedGate5 30 3) (closed_mem 30 3) cl_13567 (by decide) v h
def cl_13578 : CNF.NClause := [(1074,true),(1075,true),(1076,true),(1077,true),(1078,true),(1084,false)]
theorem inp_13578 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13578 := by
  exact input_gate (closedGate5 30 5) (closed_mem 30 5) cl_13578 (by decide) v h
def cl_13601 : CNF.NClause := [(1057,false),(1060,true),(1068,true),(1071,true),(1074,true),(1082,true)]
theorem inp_13601 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13601 := by
  exact input_gate (closedGate5 30 8) (closed_mem 30 8) cl_13601 (by decide) v h
def cl_13603 : CNF.NClause := [(1055,true),(1061,true),(1067,true),(1073,true),(1074,false),(1080,true)]
theorem inp_13603 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13603 := by
  exact input_gate (closedGate5 30 9) (closed_mem 30 9) cl_13603 (by decide) v h
def cl_13606 : CNF.NClause := [(1055,true),(1061,false),(1067,true),(1073,true),(1074,true),(1080,true)]
theorem inp_13606 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13606 := by
  exact input_gate (closedGate5 30 9) (closed_mem 30 9) cl_13606 (by decide) v h
def cl_13616 : CNF.NClause := [(1058,true),(1061,true),(1064,true),(1072,false),(1075,true),(1082,true)]
theorem inp_13616 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13616 := by
  exact input_gate (closedGate5 30 11) (closed_mem 30 11) cl_13616 (by decide) v h
def cl_13625 : CNF.NClause := [(1056,false),(1060,true),(1064,true),(1073,true),(1077,true),(1083,true)]
theorem inp_13625 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13625 := by
  exact input_gate (closedGate5 30 12) (closed_mem 30 12) cl_13625 (by decide) v h
def cl_13633 : CNF.NClause := [(1055,true),(1062,true),(1064,true),(1071,true),(1078,false),(1081,true)]
theorem inp_13633 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13633 := by
  exact input_gate (closedGate5 30 14) (closed_mem 30 14) cl_13633 (by decide) v h
def cl_13636 : CNF.NClause := [(1055,true),(1062,false),(1064,true),(1071,true),(1078,true),(1081,true)]
theorem inp_13636 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13636 := by
  exact input_gate (closedGate5 30 14) (closed_mem 30 14) cl_13636 (by decide) v h
def cl_13646 : CNF.NClause := [(1058,true),(1060,true),(1067,true),(1069,false),(1076,true),(1081,true)]
theorem inp_13646 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13646 := by
  exact input_gate (closedGate5 30 16) (closed_mem 30 16) cl_13646 (by decide) v h
def cl_13668 : CNF.NClause := [(1059,true),(1060,true),(1061,true),(1062,true),(1063,true),(1084,false)]
theorem inp_13668 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13668 := by
  exact input_gate (closedGate5 30 20) (closed_mem 30 20) cl_13668 (by decide) v h
def cl_13675 : CNF.NClause := [(1058,true),(1059,true),(1065,true),(1071,true),(1077,false),(1080,true)]
theorem inp_13675 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13675 := by
  exact input_gate (closedGate5 30 21) (closed_mem 30 21) cl_13675 (by decide) v h
def cl_13676 : CNF.NClause := [(1058,true),(1059,true),(1065,true),(1071,false),(1077,true),(1080,true)]
theorem inp_13676 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13676 := by
  exact input_gate (closedGate5 30 21) (closed_mem 30 21) cl_13676 (by decide) v h
def cl_13677 : CNF.NClause := [(1058,true),(1059,true),(1065,false),(1071,true),(1077,true),(1080,true)]
theorem inp_13677 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13677 := by
  exact input_gate (closedGate5 30 21) (closed_mem 30 21) cl_13677 (by decide) v h
def cl_13692 : CNF.NClause := [(1055,true),(1059,true),(1068,true),(1072,true),(1076,true),(1083,false)]
theorem inp_13692 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13692 := by
  exact input_gate (closedGate5 30 24) (closed_mem 30 24) cl_13692 (by decide) v h
def cl_13693 : CNF.NClause := [(1055,true),(1059,true),(1068,true),(1072,true),(1076,false),(1083,true)]
theorem inp_13693 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13693 := by
  exact input_gate (closedGate5 30 24) (closed_mem 30 24) cl_13693 (by decide) v h
def cl_13698 : CNF.NClause := [(1054,true),(1055,true),(1056,true),(1057,true),(1058,true),(1084,false)]
theorem inp_13698 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13698 := by
  exact input_gate (closedGate5 30 25) (closed_mem 30 25) cl_13698 (by decide) v h
end Percolation.Replay
