import NInputs185
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_11954 : CNF.NClause := [(778,true),(784,true),(785,true),(791,false),(797,true),(801,true)]
theorem inp_11954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11954 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 13) (closed_mem 21 13) cl_11954 (by decide) v hb
def cl_11955 : CNF.NClause := [(778,true),(784,true),(785,false),(791,true),(797,true),(801,true)]
theorem inp_11955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11955 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 13) (closed_mem 21 13) cl_11955 (by decide) v hb
def cl_11957 : CNF.NClause := [(778,false),(784,true),(785,true),(791,true),(797,true),(801,true)]
theorem inp_11957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11957 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 13) (closed_mem 21 13) cl_11957 (by decide) v hb
def cl_11963 : CNF.NClause := [(776,false),(783,true),(785,true),(792,true),(799,true),(802,true)]
theorem inp_11963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11963 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 14) (closed_mem 21 14) cl_11963 (by decide) v hb
def cl_11965 : CNF.NClause := [(790,true),(791,true),(792,true),(793,true),(794,false),(805,true)]
theorem inp_11965 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11965 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 15) (closed_mem 21 15) cl_11965 (by decide) v hb
def cl_11966 : CNF.NClause := [(790,true),(791,true),(792,true),(793,false),(794,true),(805,true)]
theorem inp_11966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11966 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 15) (closed_mem 21 15) cl_11966 (by decide) v hb
def cl_11967 : CNF.NClause := [(790,true),(791,true),(792,false),(793,true),(794,true),(805,true)]
theorem inp_11967 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11967 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 15) (closed_mem 21 15) cl_11967 (by decide) v hb
def cl_11968 : CNF.NClause := [(790,true),(791,false),(792,true),(793,true),(794,true),(805,true)]
theorem inp_11968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11968 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 15) (closed_mem 21 15) cl_11968 (by decide) v hb
def cl_11969 : CNF.NClause := [(790,false),(791,true),(792,true),(793,true),(794,true),(805,true)]
theorem inp_11969 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11969 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 15) (closed_mem 21 15) cl_11969 (by decide) v hb
def cl_11972 : CNF.NClause := [(779,true),(781,true),(788,true),(790,false),(797,true),(802,true)]
theorem inp_11972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11972 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 16) (closed_mem 21 16) cl_11972 (by decide) v hb
def cl_11973 : CNF.NClause := [(779,true),(781,true),(788,false),(790,true),(797,true),(802,true)]
theorem inp_11973 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11973 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 16) (closed_mem 21 16) cl_11973 (by decide) v hb
def cl_11975 : CNF.NClause := [(779,false),(781,true),(788,true),(790,true),(797,true),(802,true)]
theorem inp_11975 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11975 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 16) (closed_mem 21 16) cl_11975 (by decide) v hb
def cl_11977 : CNF.NClause := [(777,true),(783,true),(789,true),(790,true),(796,false),(801,true)]
theorem inp_11977 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11977 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 17) (closed_mem 21 17) cl_11977 (by decide) v hb
def cl_11983 : CNF.NClause := [(778,true),(782,true),(786,true),(790,true),(799,false),(804,true)]
theorem inp_11983 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11983 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 18) (closed_mem 21 18) cl_11983 (by decide) v hb
def cl_11985 : CNF.NClause := [(778,true),(782,true),(786,false),(790,true),(799,true),(804,true)]
theorem inp_11985 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11985 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 18) (closed_mem 21 18) cl_11985 (by decide) v hb
def cl_11986 : CNF.NClause := [(778,true),(782,false),(786,true),(790,true),(799,true),(804,true)]
theorem inp_11986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11986 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 18) (closed_mem 21 18) cl_11986 (by decide) v hb
def cl_11987 : CNF.NClause := [(778,false),(782,true),(786,true),(790,true),(799,true),(804,true)]
theorem inp_11987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11987 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 18) (closed_mem 21 18) cl_11987 (by decide) v hb
def cl_11989 : CNF.NClause := [(776,true),(784,true),(787,true),(790,true),(798,false),(803,true)]
theorem inp_11989 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11989 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 19) (closed_mem 21 19) cl_11989 (by decide) v hb
def cl_11991 : CNF.NClause := [(776,true),(784,true),(787,false),(790,true),(798,true),(803,true)]
theorem inp_11991 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11991 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 19) (closed_mem 21 19) cl_11991 (by decide) v hb
def cl_11992 : CNF.NClause := [(776,true),(784,false),(787,true),(790,true),(798,true),(803,true)]
theorem inp_11992 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11992 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 19) (closed_mem 21 19) cl_11992 (by decide) v hb
def cl_11993 : CNF.NClause := [(776,false),(784,true),(787,true),(790,true),(798,true),(803,true)]
theorem inp_11993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11993 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 19) (closed_mem 21 19) cl_11993 (by decide) v hb
def cl_11995 : CNF.NClause := [(780,true),(781,true),(782,true),(783,true),(784,false),(805,true)]
theorem inp_11995 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11995 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 20) (closed_mem 21 20) cl_11995 (by decide) v hb
def cl_11996 : CNF.NClause := [(780,true),(781,true),(782,true),(783,false),(784,true),(805,true)]
theorem inp_11996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11996 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 20) (closed_mem 21 20) cl_11996 (by decide) v hb
def cl_11997 : CNF.NClause := [(780,true),(781,true),(782,false),(783,true),(784,true),(805,true)]
theorem inp_11997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11997 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 20) (closed_mem 21 20) cl_11997 (by decide) v hb
def cl_11998 : CNF.NClause := [(780,true),(781,false),(782,true),(783,true),(784,true),(805,true)]
theorem inp_11998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11998 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 20) (closed_mem 21 20) cl_11998 (by decide) v hb
def cl_11999 : CNF.NClause := [(780,false),(781,true),(782,true),(783,true),(784,true),(805,true)]
theorem inp_11999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11999 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 20) (closed_mem 21 20) cl_11999 (by decide) v hb
def cl_12001 : CNF.NClause := [(779,true),(780,true),(786,true),(792,true),(798,false),(801,true)]
theorem inp_12001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12001 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 21) (closed_mem 21 21) cl_12001 (by decide) v hb
def cl_12003 : CNF.NClause := [(779,true),(780,true),(786,false),(792,true),(798,true),(801,true)]
theorem inp_12003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12003 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 21) (closed_mem 21 21) cl_12003 (by decide) v hb
def cl_12004 : CNF.NClause := [(779,true),(780,false),(786,true),(792,true),(798,true),(801,true)]
theorem inp_12004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12004 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 21) (closed_mem 21 21) cl_12004 (by decide) v hb
def cl_12006 : CNF.NClause := [(777,true),(780,true),(788,true),(791,true),(799,true),(803,false)]
theorem inp_12006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12006 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 22) (closed_mem 21 22) cl_12006 (by decide) v hb
def cl_12007 : CNF.NClause := [(777,true),(780,true),(788,true),(791,true),(799,false),(803,true)]
theorem inp_12007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12007 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 22) (closed_mem 21 22) cl_12007 (by decide) v hb
def cl_12008 : CNF.NClause := [(777,true),(780,true),(788,true),(791,false),(799,true),(803,true)]
theorem inp_12008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12008 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 22) (closed_mem 21 22) cl_12008 (by decide) v hb
def cl_12009 : CNF.NClause := [(777,true),(780,true),(788,false),(791,true),(799,true),(803,true)]
theorem inp_12009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12009 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_12009 v hb
def cl_12010 : CNF.NClause := [(777,true),(780,false),(788,true),(791,true),(799,true),(803,true)]
theorem inp_12010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12010 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 22) (closed_mem 21 22) cl_12010 (by decide) v hb
def cl_12013 : CNF.NClause := [(778,true),(780,true),(787,true),(794,true),(796,false),(802,true)]
theorem inp_12013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12013 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 23) (closed_mem 21 23) cl_12013 (by decide) v hb
def cl_12018 : CNF.NClause := [(776,true),(780,true),(789,true),(793,true),(797,true),(804,false)]
theorem inp_12018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12018 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 24) (closed_mem 21 24) cl_12018 (by decide) v hb
def cl_12019 : CNF.NClause := [(776,true),(780,true),(789,true),(793,true),(797,false),(804,true)]
theorem inp_12019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12019 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 24) (closed_mem 21 24) cl_12019 (by decide) v hb
def cl_12020 : CNF.NClause := [(776,true),(780,true),(789,true),(793,false),(797,true),(804,true)]
theorem inp_12020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12020 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 24) (closed_mem 21 24) cl_12020 (by decide) v hb
def cl_12022 : CNF.NClause := [(776,true),(780,false),(789,true),(793,true),(797,true),(804,true)]
theorem inp_12022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12022 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 24) (closed_mem 21 24) cl_12022 (by decide) v hb
def cl_12023 : CNF.NClause := [(776,false),(780,true),(789,true),(793,true),(797,true),(804,true)]
theorem inp_12023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12023 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 24) (closed_mem 21 24) cl_12023 (by decide) v hb
def cl_12025 : CNF.NClause := [(775,true),(776,true),(777,true),(778,true),(779,false),(805,true)]
theorem inp_12025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12025 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 25) (closed_mem 21 25) cl_12025 (by decide) v hb
def cl_12026 : CNF.NClause := [(775,true),(776,true),(777,true),(778,false),(779,true),(805,true)]
theorem inp_12026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12026 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 25) (closed_mem 21 25) cl_12026 (by decide) v hb
def cl_12027 : CNF.NClause := [(775,true),(776,true),(777,false),(778,true),(779,true),(805,true)]
theorem inp_12027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12027 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 25) (closed_mem 21 25) cl_12027 (by decide) v hb
def cl_12028 : CNF.NClause := [(775,true),(776,false),(777,true),(778,true),(779,true),(805,true)]
theorem inp_12028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12028 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 25) (closed_mem 21 25) cl_12028 (by decide) v hb
def cl_12031 : CNF.NClause := [(775,true),(784,true),(788,true),(792,true),(796,false),(804,true)]
theorem inp_12031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12031 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 26) (closed_mem 21 26) cl_12031 (by decide) v hb
def cl_12036 : CNF.NClause := [(775,true),(782,true),(789,true),(791,true),(798,true),(802,false)]
theorem inp_12036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12036 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 27) (closed_mem 21 27) cl_12036 (by decide) v hb
def cl_12037 : CNF.NClause := [(775,true),(782,true),(789,true),(791,true),(798,false),(802,true)]
theorem inp_12037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12037 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 27) (closed_mem 21 27) cl_12037 (by decide) v hb
def cl_12038 : CNF.NClause := [(775,true),(782,true),(789,true),(791,false),(798,true),(802,true)]
theorem inp_12038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12038 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 27) (closed_mem 21 27) cl_12038 (by decide) v hb
def cl_12039 : CNF.NClause := [(775,true),(782,true),(789,false),(791,true),(798,true),(802,true)]
theorem inp_12039 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12039 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 27) (closed_mem 21 27) cl_12039 (by decide) v hb
def cl_12040 : CNF.NClause := [(775,true),(782,false),(789,true),(791,true),(798,true),(802,true)]
theorem inp_12040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12040 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 27) (closed_mem 21 27) cl_12040 (by decide) v hb
end Percolation.NReplay
