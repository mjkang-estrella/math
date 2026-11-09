import NInputs139
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_7970 : CNF.NClause := [(149,true),(150,true),(151,true),(152,false),(153,true),(154,true)]
theorem inp_7970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7970 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 0) (closed_mem 0 0) cl_7970 (by decide) v hb
def cl_7971 : CNF.NClause := [(149,true),(150,true),(151,false),(152,true),(153,true),(154,true)]
theorem inp_7971 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7971 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 0) (closed_mem 0 0) cl_7971 (by decide) v hb
def cl_7972 : CNF.NClause := [(149,true),(150,false),(151,true),(152,true),(153,true),(154,true)]
theorem inp_7972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7972 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 0) (closed_mem 0 0) cl_7972 (by decide) v hb
def cl_7975 : CNF.NClause := [(128,true),(133,true),(138,true),(143,true),(148,false),(149,true)]
theorem inp_7975 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7975 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 1) (closed_mem 0 1) cl_7975 (by decide) v hb
def cl_7976 : CNF.NClause := [(128,true),(133,true),(138,true),(143,false),(148,true),(149,true)]
theorem inp_7976 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7976 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 1) (closed_mem 0 1) cl_7976 (by decide) v hb
def cl_7977 : CNF.NClause := [(128,true),(133,true),(138,false),(143,true),(148,true),(149,true)]
theorem inp_7977 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7977 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 1) (closed_mem 0 1) cl_7977 (by decide) v hb
def cl_7978 : CNF.NClause := [(128,true),(133,false),(138,true),(143,true),(148,true),(149,true)]
theorem inp_7978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7978 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 1) (closed_mem 0 1) cl_7978 (by decide) v hb
def cl_7979 : CNF.NClause := [(128,false),(133,true),(138,true),(143,true),(148,true),(149,true)]
theorem inp_7979 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7979 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 1) (closed_mem 0 1) cl_7979 (by decide) v hb
def cl_7981 : CNF.NClause := [(126,true),(131,true),(136,true),(141,true),(146,false),(149,true)]
theorem inp_7981 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7981 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 2) (closed_mem 0 2) cl_7981 (by decide) v hb
def cl_7982 : CNF.NClause := [(126,true),(131,true),(136,true),(141,false),(146,true),(149,true)]
theorem inp_7982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7982 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 2) (closed_mem 0 2) cl_7982 (by decide) v hb
def cl_7983 : CNF.NClause := [(126,true),(131,true),(136,false),(141,true),(146,true),(149,true)]
theorem inp_7983 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7983 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 2) (closed_mem 0 2) cl_7983 (by decide) v hb
def cl_7984 : CNF.NClause := [(126,true),(131,false),(136,true),(141,true),(146,true),(149,true)]
theorem inp_7984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7984 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 2) (closed_mem 0 2) cl_7984 (by decide) v hb
def cl_7985 : CNF.NClause := [(126,false),(131,true),(136,true),(141,true),(146,true),(149,true)]
theorem inp_7985 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7985 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 2) (closed_mem 0 2) cl_7985 (by decide) v hb
def cl_7987 : CNF.NClause := [(127,true),(132,true),(137,true),(142,true),(147,false),(149,true)]
theorem inp_7987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7987 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 3) (closed_mem 0 3) cl_7987 (by decide) v hb
def cl_7988 : CNF.NClause := [(127,true),(132,true),(137,true),(142,false),(147,true),(149,true)]
theorem inp_7988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7988 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 3) (closed_mem 0 3) cl_7988 (by decide) v hb
def cl_7989 : CNF.NClause := [(127,true),(132,true),(137,false),(142,true),(147,true),(149,true)]
theorem inp_7989 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7989 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 3) (closed_mem 0 3) cl_7989 (by decide) v hb
def cl_7990 : CNF.NClause := [(127,true),(132,false),(137,true),(142,true),(147,true),(149,true)]
theorem inp_7990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7990 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 3) (closed_mem 0 3) cl_7990 (by decide) v hb
def cl_7991 : CNF.NClause := [(127,false),(132,true),(137,true),(142,true),(147,true),(149,true)]
theorem inp_7991 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7991 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 3) (closed_mem 0 3) cl_7991 (by decide) v hb
def cl_7993 : CNF.NClause := [(125,true),(130,true),(135,true),(140,true),(145,false),(149,true)]
theorem inp_7993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7993 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 4) (closed_mem 0 4) cl_7993 (by decide) v hb
def cl_7994 : CNF.NClause := [(125,true),(130,true),(135,true),(140,false),(145,true),(149,true)]
theorem inp_7994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7994 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 4) (closed_mem 0 4) cl_7994 (by decide) v hb
def cl_7995 : CNF.NClause := [(125,true),(130,true),(135,false),(140,true),(145,true),(149,true)]
theorem inp_7995 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7995 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 4) (closed_mem 0 4) cl_7995 (by decide) v hb
def cl_7996 : CNF.NClause := [(125,true),(130,false),(135,true),(140,true),(145,true),(149,true)]
theorem inp_7996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7996 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 4) (closed_mem 0 4) cl_7996 (by decide) v hb
def cl_7997 : CNF.NClause := [(125,false),(130,true),(135,true),(140,true),(145,true),(149,true)]
theorem inp_7997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7997 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 4) (closed_mem 0 4) cl_7997 (by decide) v hb
def cl_7999 : CNF.NClause := [(144,true),(145,true),(146,true),(147,true),(148,false),(154,true)]
theorem inp_7999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7999 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 5) (closed_mem 0 5) cl_7999 (by decide) v hb
def cl_8000 : CNF.NClause := [(144,true),(145,true),(146,true),(147,false),(148,true),(154,true)]
theorem inp_8000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8000 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 5) (closed_mem 0 5) cl_8000 (by decide) v hb
def cl_8001 : CNF.NClause := [(144,true),(145,true),(146,false),(147,true),(148,true),(154,true)]
theorem inp_8001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8001 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 5) (closed_mem 0 5) cl_8001 (by decide) v hb
def cl_8002 : CNF.NClause := [(144,true),(145,false),(146,true),(147,true),(148,true),(154,true)]
theorem inp_8002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8002 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 5) (closed_mem 0 5) cl_8002 (by decide) v hb
def cl_8003 : CNF.NClause := [(144,false),(145,true),(146,true),(147,true),(148,true),(154,true)]
theorem inp_8003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8003 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 5) (closed_mem 0 5) cl_8003 (by decide) v hb
def cl_8004 : CNF.NClause := [(128,true),(132,true),(136,true),(140,true),(144,true),(153,false)]
theorem inp_8004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8004 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 6) (closed_mem 0 6) cl_8004 (by decide) v hb
def cl_8005 : CNF.NClause := [(128,true),(132,true),(136,true),(140,true),(144,false),(153,true)]
theorem inp_8005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8005 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 6) (closed_mem 0 6) cl_8005 (by decide) v hb
def cl_8006 : CNF.NClause := [(128,true),(132,true),(136,true),(140,false),(144,true),(153,true)]
theorem inp_8006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8006 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 6) (closed_mem 0 6) cl_8006 (by decide) v hb
def cl_8007 : CNF.NClause := [(128,true),(132,true),(136,false),(140,true),(144,true),(153,true)]
theorem inp_8007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8007 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 6) (closed_mem 0 6) cl_8007 (by decide) v hb
def cl_8008 : CNF.NClause := [(128,true),(132,false),(136,true),(140,true),(144,true),(153,true)]
theorem inp_8008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8008 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 6) (closed_mem 0 6) cl_8008 (by decide) v hb
def cl_8009 : CNF.NClause := [(128,false),(132,true),(136,true),(140,true),(144,true),(153,true)]
theorem inp_8009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8009 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 6) (closed_mem 0 6) cl_8009 (by decide) v hb
def cl_8010 : CNF.NClause := [(126,true),(133,true),(135,true),(142,true),(144,true),(151,false)]
theorem inp_8010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8010 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 7) (closed_mem 0 7) cl_8010 (by decide) v hb
def cl_8011 : CNF.NClause := [(126,true),(133,true),(135,true),(142,true),(144,false),(151,true)]
theorem inp_8011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8011 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 7) (closed_mem 0 7) cl_8011 (by decide) v hb
def cl_8012 : CNF.NClause := [(126,true),(133,true),(135,true),(142,false),(144,true),(151,true)]
theorem inp_8012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8012 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 7) (closed_mem 0 7) cl_8012 (by decide) v hb
def cl_8013 : CNF.NClause := [(126,true),(133,true),(135,false),(142,true),(144,true),(151,true)]
theorem inp_8013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8013 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 7) (closed_mem 0 7) cl_8013 (by decide) v hb
def cl_8014 : CNF.NClause := [(126,true),(133,false),(135,true),(142,true),(144,true),(151,true)]
theorem inp_8014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8014 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 7) (closed_mem 0 7) cl_8014 (by decide) v hb
def cl_8015 : CNF.NClause := [(126,false),(133,true),(135,true),(142,true),(144,true),(151,true)]
theorem inp_8015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8015 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 7) (closed_mem 0 7) cl_8015 (by decide) v hb
def cl_8016 : CNF.NClause := [(127,true),(130,true),(138,true),(141,true),(144,true),(152,false)]
theorem inp_8016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8016 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 8) (closed_mem 0 8) cl_8016 (by decide) v hb
def cl_8017 : CNF.NClause := [(127,true),(130,true),(138,true),(141,true),(144,false),(152,true)]
theorem inp_8017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8017 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 8) (closed_mem 0 8) cl_8017 (by decide) v hb
def cl_8018 : CNF.NClause := [(127,true),(130,true),(138,true),(141,false),(144,true),(152,true)]
theorem inp_8018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8018 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 8) (closed_mem 0 8) cl_8018 (by decide) v hb
def cl_8019 : CNF.NClause := [(127,true),(130,true),(138,false),(141,true),(144,true),(152,true)]
theorem inp_8019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8019 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 8) (closed_mem 0 8) cl_8019 (by decide) v hb
def cl_8020 : CNF.NClause := [(127,true),(130,false),(138,true),(141,true),(144,true),(152,true)]
theorem inp_8020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8020 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 8) (closed_mem 0 8) cl_8020 (by decide) v hb
def cl_8021 : CNF.NClause := [(127,false),(130,true),(138,true),(141,true),(144,true),(152,true)]
theorem inp_8021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8021 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 8) (closed_mem 0 8) cl_8021 (by decide) v hb
def cl_8022 : CNF.NClause := [(125,true),(131,true),(137,true),(143,true),(144,true),(150,false)]
theorem inp_8022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8022 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 9) (closed_mem 0 9) cl_8022 (by decide) v hb
def cl_8023 : CNF.NClause := [(125,true),(131,true),(137,true),(143,true),(144,false),(150,true)]
theorem inp_8023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8023 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 9) (closed_mem 0 9) cl_8023 (by decide) v hb
def cl_8024 : CNF.NClause := [(125,true),(131,true),(137,true),(143,false),(144,true),(150,true)]
theorem inp_8024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8024 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 9) (closed_mem 0 9) cl_8024 (by decide) v hb
def cl_8025 : CNF.NClause := [(125,true),(131,true),(137,false),(143,true),(144,true),(150,true)]
theorem inp_8025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8025 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 9) (closed_mem 0 9) cl_8025 (by decide) v hb
end Percolation.NReplay
