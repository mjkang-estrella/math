import NInputs084
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_4991 : CNF.NClause := [(38,false),(7,false),(64,true),(71,true),(73,true),(80,true),(82,true),(89,true)]
theorem inp_4991 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4991 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4991 (by decide) v hb
def cl_4992 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,true),(80,true),(82,true),(89,true)]
theorem inp_4992 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4992 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4992 (by decide) v hb
def cl_4993 : CNF.NClause := [(39,true),(8,false),(65,false),(68,false),(76,false),(79,false),(82,false),(90,false)]
theorem inp_4993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4993 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_4993 (by decide) v hb
def cl_4994 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,false),(79,false),(82,false),(90,false)]
theorem inp_4994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4994 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_4994 (by decide) v hb
def cl_4995 : CNF.NClause := [(39,false),(8,false),(65,true),(68,false),(76,false),(79,false),(82,false),(90,false)]
theorem inp_4995 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4995 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_4995 (by decide) v hb
def cl_4996 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,false),(79,false),(82,false),(90,false)]
theorem inp_4996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4996 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_4996 (by decide) v hb
def cl_4997 : CNF.NClause := [(39,false),(8,false),(65,false),(68,true),(76,false),(79,false),(82,false),(90,false)]
theorem inp_4997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4997 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_4997 (by decide) v hb
def cl_4998 : CNF.NClause := [(39,false),(8,true),(65,false),(68,true),(76,false),(79,false),(82,false),(90,false)]
theorem inp_4998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4998 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_4998 (by decide) v hb
def cl_4999 : CNF.NClause := [(39,false),(8,false),(65,true),(68,true),(76,false),(79,false),(82,false),(90,false)]
theorem inp_4999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4999 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_4999 (by decide) v hb
def cl_5000 : CNF.NClause := [(39,false),(8,true),(65,true),(68,true),(76,false),(79,false),(82,false),(90,false)]
theorem inp_5000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5000 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5000 (by decide) v hb
def cl_5001 : CNF.NClause := [(39,false),(8,false),(65,false),(68,false),(76,true),(79,false),(82,false),(90,false)]
theorem inp_5001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5001 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5001 (by decide) v hb
def cl_5002 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,true),(79,false),(82,false),(90,false)]
theorem inp_5002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5002 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5002 (by decide) v hb
def cl_5003 : CNF.NClause := [(39,false),(8,false),(65,true),(68,false),(76,true),(79,false),(82,false),(90,false)]
theorem inp_5003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5003 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5003 (by decide) v hb
def cl_5004 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,true),(79,false),(82,false),(90,false)]
theorem inp_5004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5004 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5004 (by decide) v hb
def cl_5005 : CNF.NClause := [(39,false),(8,false),(65,false),(68,true),(76,true),(79,false),(82,false),(90,false)]
theorem inp_5005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5005 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5005 (by decide) v hb
def cl_5006 : CNF.NClause := [(39,false),(8,true),(65,false),(68,true),(76,true),(79,false),(82,false),(90,false)]
theorem inp_5006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5006 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5006 (by decide) v hb
def cl_5007 : CNF.NClause := [(39,false),(8,false),(65,true),(68,true),(76,true),(79,false),(82,false),(90,false)]
theorem inp_5007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5007 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5007 (by decide) v hb
def cl_5008 : CNF.NClause := [(39,false),(8,true),(65,true),(68,true),(76,true),(79,false),(82,false),(90,false)]
theorem inp_5008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5008 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5008 (by decide) v hb
def cl_5009 : CNF.NClause := [(39,false),(8,false),(65,false),(68,false),(76,false),(79,true),(82,false),(90,false)]
theorem inp_5009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5009 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5009 (by decide) v hb
def cl_5010 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,false),(79,true),(82,false),(90,false)]
theorem inp_5010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5010 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5010 (by decide) v hb
def cl_5011 : CNF.NClause := [(39,false),(8,false),(65,true),(68,false),(76,false),(79,true),(82,false),(90,false)]
theorem inp_5011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5011 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5011 (by decide) v hb
def cl_5012 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,false),(79,true),(82,false),(90,false)]
theorem inp_5012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5012 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5012 (by decide) v hb
def cl_5013 : CNF.NClause := [(39,false),(8,false),(65,false),(68,true),(76,false),(79,true),(82,false),(90,false)]
theorem inp_5013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5013 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5013 (by decide) v hb
def cl_5014 : CNF.NClause := [(39,false),(8,true),(65,false),(68,true),(76,false),(79,true),(82,false),(90,false)]
theorem inp_5014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5014 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5014 (by decide) v hb
def cl_5015 : CNF.NClause := [(39,false),(8,false),(65,true),(68,true),(76,false),(79,true),(82,false),(90,false)]
theorem inp_5015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5015 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5015 (by decide) v hb
def cl_5016 : CNF.NClause := [(39,false),(8,true),(65,true),(68,true),(76,false),(79,true),(82,false),(90,false)]
theorem inp_5016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5016 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5016 (by decide) v hb
def cl_5017 : CNF.NClause := [(39,false),(8,false),(65,false),(68,false),(76,true),(79,true),(82,false),(90,false)]
theorem inp_5017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5017 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5017 (by decide) v hb
def cl_5018 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,true),(79,true),(82,false),(90,false)]
theorem inp_5018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5018 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5018 (by decide) v hb
def cl_5019 : CNF.NClause := [(39,false),(8,false),(65,true),(68,false),(76,true),(79,true),(82,false),(90,false)]
theorem inp_5019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5019 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5019 (by decide) v hb
def cl_5020 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,true),(79,true),(82,false),(90,false)]
theorem inp_5020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5020 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5020 (by decide) v hb
def cl_5021 : CNF.NClause := [(39,false),(8,false),(65,false),(68,true),(76,true),(79,true),(82,false),(90,false)]
theorem inp_5021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5021 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5021 (by decide) v hb
def cl_5022 : CNF.NClause := [(39,false),(8,true),(65,false),(68,true),(76,true),(79,true),(82,false),(90,false)]
theorem inp_5022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5022 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5022 (by decide) v hb
def cl_5023 : CNF.NClause := [(39,false),(8,false),(65,true),(68,true),(76,true),(79,true),(82,false),(90,false)]
theorem inp_5023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5023 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5023 (by decide) v hb
def cl_5024 : CNF.NClause := [(39,false),(8,true),(65,true),(68,true),(76,true),(79,true),(82,false),(90,false)]
theorem inp_5024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5024 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5024 (by decide) v hb
def cl_5025 : CNF.NClause := [(39,false),(8,false),(65,false),(68,false),(76,false),(79,false),(82,true),(90,false)]
theorem inp_5025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5025 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5025 (by decide) v hb
def cl_5026 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,false),(79,false),(82,true),(90,false)]
theorem inp_5026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5026 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5026 v hb
def cl_5027 : CNF.NClause := [(39,false),(8,false),(65,true),(68,false),(76,false),(79,false),(82,true),(90,false)]
theorem inp_5027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5027 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5027 (by decide) v hb
def cl_5028 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,false),(79,false),(82,true),(90,false)]
theorem inp_5028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5028 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5028 v hb
def cl_5029 : CNF.NClause := [(39,false),(8,false),(65,false),(68,true),(76,false),(79,false),(82,true),(90,false)]
theorem inp_5029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5029 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5029 (by decide) v hb
def cl_5030 : CNF.NClause := [(39,false),(8,true),(65,false),(68,true),(76,false),(79,false),(82,true),(90,false)]
theorem inp_5030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5030 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5030 (by decide) v hb
def cl_5031 : CNF.NClause := [(39,false),(8,false),(65,true),(68,true),(76,false),(79,false),(82,true),(90,false)]
theorem inp_5031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5031 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5031 (by decide) v hb
def cl_5032 : CNF.NClause := [(39,false),(8,true),(65,true),(68,true),(76,false),(79,false),(82,true),(90,false)]
theorem inp_5032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5032 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5032 (by decide) v hb
def cl_5033 : CNF.NClause := [(39,false),(8,false),(65,false),(68,false),(76,true),(79,false),(82,true),(90,false)]
theorem inp_5033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5033 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5033 (by decide) v hb
def cl_5034 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,true),(79,false),(82,true),(90,false)]
theorem inp_5034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5034 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5034 v hb
def cl_5035 : CNF.NClause := [(39,false),(8,false),(65,true),(68,false),(76,true),(79,false),(82,true),(90,false)]
theorem inp_5035 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5035 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5035 (by decide) v hb
def cl_5036 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,true),(79,false),(82,true),(90,false)]
theorem inp_5036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5036 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5036 v hb
def cl_5037 : CNF.NClause := [(39,false),(8,false),(65,false),(68,true),(76,true),(79,false),(82,true),(90,false)]
theorem inp_5037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5037 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5037 (by decide) v hb
def cl_5038 : CNF.NClause := [(39,false),(8,true),(65,false),(68,true),(76,true),(79,false),(82,true),(90,false)]
theorem inp_5038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5038 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5038 (by decide) v hb
def cl_5039 : CNF.NClause := [(39,false),(8,false),(65,true),(68,true),(76,true),(79,false),(82,true),(90,false)]
theorem inp_5039 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5039 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5039 (by decide) v hb
def cl_5040 : CNF.NClause := [(39,false),(8,true),(65,true),(68,true),(76,true),(79,false),(82,true),(90,false)]
theorem inp_5040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5040 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5040 (by decide) v hb
end Percolation.NReplay
