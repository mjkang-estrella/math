import NInputs085
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_5041 : CNF.NClause := [(39,false),(8,false),(65,false),(68,false),(76,false),(79,true),(82,true),(90,false)]
theorem inp_5041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5041 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5041 (by decide) v hb
def cl_5042 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,false),(79,true),(82,true),(90,false)]
theorem inp_5042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5042 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5042 v hb
def cl_5043 : CNF.NClause := [(39,false),(8,false),(65,true),(68,false),(76,false),(79,true),(82,true),(90,false)]
theorem inp_5043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5043 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5043 (by decide) v hb
def cl_5044 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,false),(79,true),(82,true),(90,false)]
theorem inp_5044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5044 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5044 v hb
def cl_5045 : CNF.NClause := [(39,false),(8,false),(65,false),(68,true),(76,false),(79,true),(82,true),(90,false)]
theorem inp_5045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5045 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5045 (by decide) v hb
def cl_5046 : CNF.NClause := [(39,false),(8,true),(65,false),(68,true),(76,false),(79,true),(82,true),(90,false)]
theorem inp_5046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5046 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5046 (by decide) v hb
def cl_5048 : CNF.NClause := [(39,false),(8,true),(65,true),(68,true),(76,false),(79,true),(82,true),(90,false)]
theorem inp_5048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5048 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5048 (by decide) v hb
def cl_5049 : CNF.NClause := [(39,false),(8,false),(65,false),(68,false),(76,true),(79,true),(82,true),(90,false)]
theorem inp_5049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5049 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5049 (by decide) v hb
def cl_5050 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,true),(79,true),(82,true),(90,false)]
theorem inp_5050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5050 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5050 v hb
def cl_5051 : CNF.NClause := [(39,false),(8,false),(65,true),(68,false),(76,true),(79,true),(82,true),(90,false)]
theorem inp_5051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5051 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5051 (by decide) v hb
def cl_5052 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,true),(79,true),(82,true),(90,false)]
theorem inp_5052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5052 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5052 v hb
def cl_5053 : CNF.NClause := [(39,false),(8,false),(65,false),(68,true),(76,true),(79,true),(82,true),(90,false)]
theorem inp_5053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5053 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5053 (by decide) v hb
def cl_5054 : CNF.NClause := [(39,false),(8,true),(65,false),(68,true),(76,true),(79,true),(82,true),(90,false)]
theorem inp_5054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5054 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5054 (by decide) v hb
def cl_5055 : CNF.NClause := [(39,false),(8,false),(65,true),(68,true),(76,true),(79,true),(82,true),(90,false)]
theorem inp_5055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5055 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5055 (by decide) v hb
def cl_5056 : CNF.NClause := [(39,false),(8,true),(65,true),(68,true),(76,true),(79,true),(82,true),(90,false)]
theorem inp_5056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5056 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5056 (by decide) v hb
def cl_5057 : CNF.NClause := [(39,false),(8,false),(65,false),(68,false),(76,false),(79,false),(82,false),(90,true)]
theorem inp_5057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5057 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5057 (by decide) v hb
def cl_5058 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,false),(79,false),(82,false),(90,true)]
theorem inp_5058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5058 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5058 (by decide) v hb
def cl_5059 : CNF.NClause := [(39,false),(8,false),(65,true),(68,false),(76,false),(79,false),(82,false),(90,true)]
theorem inp_5059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5059 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5059 (by decide) v hb
def cl_5060 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,false),(79,false),(82,false),(90,true)]
theorem inp_5060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5060 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5060 (by decide) v hb
def cl_5061 : CNF.NClause := [(39,false),(8,false),(65,false),(68,true),(76,false),(79,false),(82,false),(90,true)]
theorem inp_5061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5061 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5061 (by decide) v hb
def cl_5062 : CNF.NClause := [(39,false),(8,true),(65,false),(68,true),(76,false),(79,false),(82,false),(90,true)]
theorem inp_5062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5062 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5062 (by decide) v hb
def cl_5063 : CNF.NClause := [(39,false),(8,false),(65,true),(68,true),(76,false),(79,false),(82,false),(90,true)]
theorem inp_5063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5063 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5063 (by decide) v hb
def cl_5064 : CNF.NClause := [(39,false),(8,true),(65,true),(68,true),(76,false),(79,false),(82,false),(90,true)]
theorem inp_5064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5064 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5064 (by decide) v hb
def cl_5065 : CNF.NClause := [(39,false),(8,false),(65,false),(68,false),(76,true),(79,false),(82,false),(90,true)]
theorem inp_5065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5065 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5065 (by decide) v hb
def cl_5066 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,true),(79,false),(82,false),(90,true)]
theorem inp_5066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5066 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5066 (by decide) v hb
def cl_5067 : CNF.NClause := [(39,false),(8,false),(65,true),(68,false),(76,true),(79,false),(82,false),(90,true)]
theorem inp_5067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5067 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5067 (by decide) v hb
def cl_5068 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,true),(79,false),(82,false),(90,true)]
theorem inp_5068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5068 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5068 (by decide) v hb
def cl_5069 : CNF.NClause := [(39,false),(8,false),(65,false),(68,true),(76,true),(79,false),(82,false),(90,true)]
theorem inp_5069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5069 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5069 (by decide) v hb
def cl_5070 : CNF.NClause := [(39,false),(8,true),(65,false),(68,true),(76,true),(79,false),(82,false),(90,true)]
theorem inp_5070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5070 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5070 (by decide) v hb
def cl_5071 : CNF.NClause := [(39,false),(8,false),(65,true),(68,true),(76,true),(79,false),(82,false),(90,true)]
theorem inp_5071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5071 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5071 (by decide) v hb
def cl_5072 : CNF.NClause := [(39,false),(8,true),(65,true),(68,true),(76,true),(79,false),(82,false),(90,true)]
theorem inp_5072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5072 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5072 (by decide) v hb
def cl_5073 : CNF.NClause := [(39,false),(8,false),(65,false),(68,false),(76,false),(79,true),(82,false),(90,true)]
theorem inp_5073 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5073 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5073 (by decide) v hb
def cl_5074 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,false),(79,true),(82,false),(90,true)]
theorem inp_5074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5074 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5074 (by decide) v hb
def cl_5075 : CNF.NClause := [(39,false),(8,false),(65,true),(68,false),(76,false),(79,true),(82,false),(90,true)]
theorem inp_5075 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5075 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5075 (by decide) v hb
def cl_5076 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,false),(79,true),(82,false),(90,true)]
theorem inp_5076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5076 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5076 (by decide) v hb
def cl_5077 : CNF.NClause := [(39,false),(8,false),(65,false),(68,true),(76,false),(79,true),(82,false),(90,true)]
theorem inp_5077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5077 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5077 (by decide) v hb
def cl_5078 : CNF.NClause := [(39,false),(8,true),(65,false),(68,true),(76,false),(79,true),(82,false),(90,true)]
theorem inp_5078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5078 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5078 (by decide) v hb
def cl_5080 : CNF.NClause := [(39,false),(8,true),(65,true),(68,true),(76,false),(79,true),(82,false),(90,true)]
theorem inp_5080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5080 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5080 (by decide) v hb
def cl_5081 : CNF.NClause := [(39,false),(8,false),(65,false),(68,false),(76,true),(79,true),(82,false),(90,true)]
theorem inp_5081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5081 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5081 (by decide) v hb
def cl_5082 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,true),(79,true),(82,false),(90,true)]
theorem inp_5082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5082 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5082 (by decide) v hb
def cl_5083 : CNF.NClause := [(39,false),(8,false),(65,true),(68,false),(76,true),(79,true),(82,false),(90,true)]
theorem inp_5083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5083 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5083 (by decide) v hb
def cl_5084 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,true),(79,true),(82,false),(90,true)]
theorem inp_5084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5084 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5084 (by decide) v hb
def cl_5085 : CNF.NClause := [(39,false),(8,false),(65,false),(68,true),(76,true),(79,true),(82,false),(90,true)]
theorem inp_5085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5085 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5085 (by decide) v hb
def cl_5086 : CNF.NClause := [(39,false),(8,true),(65,false),(68,true),(76,true),(79,true),(82,false),(90,true)]
theorem inp_5086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5086 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5086 (by decide) v hb
def cl_5088 : CNF.NClause := [(39,false),(8,true),(65,true),(68,true),(76,true),(79,true),(82,false),(90,true)]
theorem inp_5088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5088 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5088 (by decide) v hb
def cl_5089 : CNF.NClause := [(39,false),(8,false),(65,false),(68,false),(76,false),(79,false),(82,true),(90,true)]
theorem inp_5089 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5089 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5089 (by decide) v hb
def cl_5090 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,false),(79,false),(82,true),(90,true)]
theorem inp_5090 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5090 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5090 (by decide) v hb
def cl_5091 : CNF.NClause := [(39,false),(8,false),(65,true),(68,false),(76,false),(79,false),(82,true),(90,true)]
theorem inp_5091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5091 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5091 (by decide) v hb
def cl_5092 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,false),(79,false),(82,true),(90,true)]
theorem inp_5092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5092 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5092 (by decide) v hb
def cl_5093 : CNF.NClause := [(39,false),(8,false),(65,false),(68,true),(76,false),(79,false),(82,true),(90,true)]
theorem inp_5093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5093 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5093 (by decide) v hb
end Percolation.NReplay
