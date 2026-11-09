import NInputs103
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_5974 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(79,false),(80,true),(81,false),(92,true)]
theorem inp_5974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5974 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5974 (by decide) v hb
def cl_5975 : CNF.NClause := [(46,false),(15,false),(77,true),(78,true),(79,false),(80,true),(81,false),(92,true)]
theorem inp_5975 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5975 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5975 (by decide) v hb
def cl_5976 : CNF.NClause := [(46,false),(15,true),(77,true),(78,true),(79,false),(80,true),(81,false),(92,true)]
theorem inp_5976 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5976 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5976 (by decide) v hb
def cl_5977 : CNF.NClause := [(46,false),(15,false),(77,false),(78,false),(79,true),(80,true),(81,false),(92,true)]
theorem inp_5977 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5977 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5977 (by decide) v hb
def cl_5978 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,true),(80,true),(81,false),(92,true)]
theorem inp_5978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5978 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5978 v hb
def cl_5979 : CNF.NClause := [(46,false),(15,false),(77,true),(78,false),(79,true),(80,true),(81,false),(92,true)]
theorem inp_5979 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5979 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5979 (by decide) v hb
def cl_5980 : CNF.NClause := [(46,false),(15,true),(77,true),(78,false),(79,true),(80,true),(81,false),(92,true)]
theorem inp_5980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5980 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5980 (by decide) v hb
def cl_5981 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(79,true),(80,true),(81,false),(92,true)]
theorem inp_5981 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5981 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5981 (by decide) v hb
def cl_5982 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(79,true),(80,true),(81,false),(92,true)]
theorem inp_5982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5982 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5982 (by decide) v hb
def cl_5983 : CNF.NClause := [(46,false),(15,false),(77,true),(78,true),(79,true),(80,true),(81,false),(92,true)]
theorem inp_5983 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5983 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5983 (by decide) v hb
def cl_5984 : CNF.NClause := [(46,false),(15,true),(77,true),(78,true),(79,true),(80,true),(81,false),(92,true)]
theorem inp_5984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5984 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5984 (by decide) v hb
def cl_5985 : CNF.NClause := [(46,false),(15,false),(77,false),(78,false),(79,false),(80,false),(81,true),(92,true)]
theorem inp_5985 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5985 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5985 (by decide) v hb
def cl_5986 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,false),(80,false),(81,true),(92,true)]
theorem inp_5986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5986 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5986 (by decide) v hb
def cl_5987 : CNF.NClause := [(46,false),(15,false),(77,true),(78,false),(79,false),(80,false),(81,true),(92,true)]
theorem inp_5987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5987 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5987 (by decide) v hb
def cl_5988 : CNF.NClause := [(46,false),(15,true),(77,true),(78,false),(79,false),(80,false),(81,true),(92,true)]
theorem inp_5988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5988 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5988 (by decide) v hb
def cl_5989 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(79,false),(80,false),(81,true),(92,true)]
theorem inp_5989 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5989 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5989 (by decide) v hb
def cl_5990 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(79,false),(80,false),(81,true),(92,true)]
theorem inp_5990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5990 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5990 (by decide) v hb
def cl_5991 : CNF.NClause := [(46,false),(15,false),(77,true),(78,true),(79,false),(80,false),(81,true),(92,true)]
theorem inp_5991 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5991 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5991 (by decide) v hb
def cl_5992 : CNF.NClause := [(46,false),(15,true),(77,true),(78,true),(79,false),(80,false),(81,true),(92,true)]
theorem inp_5992 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5992 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5992 (by decide) v hb
def cl_5993 : CNF.NClause := [(46,false),(15,false),(77,false),(78,false),(79,true),(80,false),(81,true),(92,true)]
theorem inp_5993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5993 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5993 (by decide) v hb
def cl_5994 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,true),(80,false),(81,true),(92,true)]
theorem inp_5994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5994 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5994 (by decide) v hb
def cl_5995 : CNF.NClause := [(46,false),(15,false),(77,true),(78,false),(79,true),(80,false),(81,true),(92,true)]
theorem inp_5995 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5995 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5995 (by decide) v hb
def cl_5996 : CNF.NClause := [(46,false),(15,true),(77,true),(78,false),(79,true),(80,false),(81,true),(92,true)]
theorem inp_5996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5996 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5996 (by decide) v hb
def cl_5997 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(79,true),(80,false),(81,true),(92,true)]
theorem inp_5997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5997 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5997 (by decide) v hb
def cl_5998 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(79,true),(80,false),(81,true),(92,true)]
theorem inp_5998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5998 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5998 (by decide) v hb
def cl_5999 : CNF.NClause := [(46,false),(15,false),(77,true),(78,true),(79,true),(80,false),(81,true),(92,true)]
theorem inp_5999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5999 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5999 (by decide) v hb
def cl_6000 : CNF.NClause := [(46,false),(15,true),(77,true),(78,true),(79,true),(80,false),(81,true),(92,true)]
theorem inp_6000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6000 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_6000 (by decide) v hb
def cl_6001 : CNF.NClause := [(46,false),(15,false),(77,false),(78,false),(79,false),(80,true),(81,true),(92,true)]
theorem inp_6001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6001 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_6001 (by decide) v hb
def cl_6002 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,false),(80,true),(81,true),(92,true)]
theorem inp_6002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6002 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_6002 (by decide) v hb
def cl_6003 : CNF.NClause := [(46,false),(15,false),(77,true),(78,false),(79,false),(80,true),(81,true),(92,true)]
theorem inp_6003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6003 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_6003 (by decide) v hb
def cl_6004 : CNF.NClause := [(46,false),(15,true),(77,true),(78,false),(79,false),(80,true),(81,true),(92,true)]
theorem inp_6004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6004 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_6004 (by decide) v hb
def cl_6005 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(79,false),(80,true),(81,true),(92,true)]
theorem inp_6005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6005 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_6005 (by decide) v hb
def cl_6006 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(79,false),(80,true),(81,true),(92,true)]
theorem inp_6006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6006 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_6006 (by decide) v hb
def cl_6007 : CNF.NClause := [(46,false),(15,false),(77,true),(78,true),(79,false),(80,true),(81,true),(92,true)]
theorem inp_6007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6007 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_6007 (by decide) v hb
def cl_6008 : CNF.NClause := [(46,false),(15,true),(77,true),(78,true),(79,false),(80,true),(81,true),(92,true)]
theorem inp_6008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6008 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_6008 (by decide) v hb
def cl_6009 : CNF.NClause := [(46,false),(15,false),(77,false),(78,false),(79,true),(80,true),(81,true),(92,true)]
theorem inp_6009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6009 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_6009 (by decide) v hb
def cl_6010 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,true),(80,true),(81,true),(92,true)]
theorem inp_6010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6010 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_6010 (by decide) v hb
def cl_6011 : CNF.NClause := [(46,false),(15,false),(77,true),(78,false),(79,true),(80,true),(81,true),(92,true)]
theorem inp_6011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6011 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_6011 (by decide) v hb
def cl_6012 : CNF.NClause := [(46,false),(15,true),(77,true),(78,false),(79,true),(80,true),(81,true),(92,true)]
theorem inp_6012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6012 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_6012 (by decide) v hb
def cl_6013 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(79,true),(80,true),(81,true),(92,true)]
theorem inp_6013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6013 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_6013 (by decide) v hb
def cl_6014 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(79,true),(80,true),(81,true),(92,true)]
theorem inp_6014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6014 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_6014 (by decide) v hb
def cl_6015 : CNF.NClause := [(46,false),(15,false),(77,true),(78,true),(79,true),(80,true),(81,true),(92,true)]
theorem inp_6015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6015 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6015 v hb
def cl_6016 : CNF.NClause := [(46,false),(15,true),(77,true),(78,true),(79,true),(80,true),(81,true),(92,true)]
theorem inp_6016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6016 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6016 v hb
def cl_6017 : CNF.NClause := [(47,true),(16,false),(66,false),(68,false),(75,false),(77,false),(84,false),(89,false)]
theorem inp_6017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6017 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6017 (by decide) v hb
def cl_6018 : CNF.NClause := [(47,false),(16,true),(66,false),(68,false),(75,false),(77,false),(84,false),(89,false)]
theorem inp_6018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6018 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6018 (by decide) v hb
def cl_6019 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(75,false),(77,false),(84,false),(89,false)]
theorem inp_6019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6019 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6019 (by decide) v hb
def cl_6020 : CNF.NClause := [(47,false),(16,true),(66,true),(68,false),(75,false),(77,false),(84,false),(89,false)]
theorem inp_6020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6020 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6020 (by decide) v hb
def cl_6021 : CNF.NClause := [(47,false),(16,false),(66,false),(68,true),(75,false),(77,false),(84,false),(89,false)]
theorem inp_6021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6021 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6021 (by decide) v hb
def cl_6022 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true),(75,false),(77,false),(84,false),(89,false)]
theorem inp_6022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6022 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6022 (by decide) v hb
def cl_6023 : CNF.NClause := [(47,false),(16,false),(66,true),(68,true),(75,false),(77,false),(84,false),(89,false)]
theorem inp_6023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6023 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 16) (spread_mem 16) cl_6023 (by decide) v hb
end Percolation.NReplay
