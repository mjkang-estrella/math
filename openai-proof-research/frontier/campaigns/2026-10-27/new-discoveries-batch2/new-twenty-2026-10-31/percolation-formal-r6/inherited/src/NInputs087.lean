import NInputs086
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_5094 : CNF.NClause := [(39,false),(8,true),(65,false),(68,true),(76,false),(79,false),(82,true),(90,true)]
theorem inp_5094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5094 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5094 (by decide) v hb
def cl_5095 : CNF.NClause := [(39,false),(8,false),(65,true),(68,true),(76,false),(79,false),(82,true),(90,true)]
theorem inp_5095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5095 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5095 (by decide) v hb
def cl_5096 : CNF.NClause := [(39,false),(8,true),(65,true),(68,true),(76,false),(79,false),(82,true),(90,true)]
theorem inp_5096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5096 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5096 (by decide) v hb
def cl_5097 : CNF.NClause := [(39,false),(8,false),(65,false),(68,false),(76,true),(79,false),(82,true),(90,true)]
theorem inp_5097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5097 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5097 (by decide) v hb
def cl_5098 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,true),(79,false),(82,true),(90,true)]
theorem inp_5098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5098 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5098 (by decide) v hb
def cl_5099 : CNF.NClause := [(39,false),(8,false),(65,true),(68,false),(76,true),(79,false),(82,true),(90,true)]
theorem inp_5099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5099 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5099 (by decide) v hb
def cl_5100 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,true),(79,false),(82,true),(90,true)]
theorem inp_5100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5100 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5100 (by decide) v hb
def cl_5101 : CNF.NClause := [(39,false),(8,false),(65,false),(68,true),(76,true),(79,false),(82,true),(90,true)]
theorem inp_5101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5101 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5101 (by decide) v hb
def cl_5102 : CNF.NClause := [(39,false),(8,true),(65,false),(68,true),(76,true),(79,false),(82,true),(90,true)]
theorem inp_5102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5102 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5102 (by decide) v hb
def cl_5104 : CNF.NClause := [(39,false),(8,true),(65,true),(68,true),(76,true),(79,false),(82,true),(90,true)]
theorem inp_5104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5104 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5104 (by decide) v hb
def cl_5105 : CNF.NClause := [(39,false),(8,false),(65,false),(68,false),(76,false),(79,true),(82,true),(90,true)]
theorem inp_5105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5105 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5105 (by decide) v hb
def cl_5106 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,false),(79,true),(82,true),(90,true)]
theorem inp_5106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5106 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5106 (by decide) v hb
def cl_5107 : CNF.NClause := [(39,false),(8,false),(65,true),(68,false),(76,false),(79,true),(82,true),(90,true)]
theorem inp_5107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5107 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5107 (by decide) v hb
def cl_5108 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,false),(79,true),(82,true),(90,true)]
theorem inp_5108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5108 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5108 (by decide) v hb
def cl_5109 : CNF.NClause := [(39,false),(8,false),(65,false),(68,true),(76,false),(79,true),(82,true),(90,true)]
theorem inp_5109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5109 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5109 (by decide) v hb
def cl_5110 : CNF.NClause := [(39,false),(8,true),(65,false),(68,true),(76,false),(79,true),(82,true),(90,true)]
theorem inp_5110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5110 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5110 (by decide) v hb
def cl_5112 : CNF.NClause := [(39,false),(8,true),(65,true),(68,true),(76,false),(79,true),(82,true),(90,true)]
theorem inp_5112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5112 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5112 (by decide) v hb
def cl_5113 : CNF.NClause := [(39,false),(8,false),(65,false),(68,false),(76,true),(79,true),(82,true),(90,true)]
theorem inp_5113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5113 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5113 (by decide) v hb
def cl_5114 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,true),(79,true),(82,true),(90,true)]
theorem inp_5114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5114 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5114 (by decide) v hb
def cl_5115 : CNF.NClause := [(39,false),(8,false),(65,true),(68,false),(76,true),(79,true),(82,true),(90,true)]
theorem inp_5115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5115 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5115 (by decide) v hb
def cl_5116 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,true),(79,true),(82,true),(90,true)]
theorem inp_5116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5116 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5116 (by decide) v hb
def cl_5117 : CNF.NClause := [(39,false),(8,false),(65,false),(68,true),(76,true),(79,true),(82,true),(90,true)]
theorem inp_5117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5117 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5117 (by decide) v hb
def cl_5118 : CNF.NClause := [(39,false),(8,true),(65,false),(68,true),(76,true),(79,true),(82,true),(90,true)]
theorem inp_5118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5118 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5118 (by decide) v hb
def cl_5120 : CNF.NClause := [(39,false),(8,true),(65,true),(68,true),(76,true),(79,true),(82,true),(90,true)]
theorem inp_5120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5120 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) cl_5120 (by decide) v hb
def cl_5121 : CNF.NClause := [(40,true),(9,false),(63,false),(69,false),(75,false),(81,false),(82,false),(88,false)]
theorem inp_5121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5121 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5121 (by decide) v hb
def cl_5122 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,false),(81,false),(82,false),(88,false)]
theorem inp_5122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5122 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5122 (by decide) v hb
def cl_5123 : CNF.NClause := [(40,false),(9,false),(63,true),(69,false),(75,false),(81,false),(82,false),(88,false)]
theorem inp_5123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5123 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5123 (by decide) v hb
def cl_5124 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,false),(81,false),(82,false),(88,false)]
theorem inp_5124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5124 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5124 (by decide) v hb
def cl_5125 : CNF.NClause := [(40,false),(9,false),(63,false),(69,true),(75,false),(81,false),(82,false),(88,false)]
theorem inp_5125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5125 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5125 (by decide) v hb
def cl_5126 : CNF.NClause := [(40,false),(9,true),(63,false),(69,true),(75,false),(81,false),(82,false),(88,false)]
theorem inp_5126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5126 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5126 (by decide) v hb
def cl_5127 : CNF.NClause := [(40,false),(9,false),(63,true),(69,true),(75,false),(81,false),(82,false),(88,false)]
theorem inp_5127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5127 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5127 (by decide) v hb
def cl_5128 : CNF.NClause := [(40,false),(9,true),(63,true),(69,true),(75,false),(81,false),(82,false),(88,false)]
theorem inp_5128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5128 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5128 (by decide) v hb
def cl_5129 : CNF.NClause := [(40,false),(9,false),(63,false),(69,false),(75,true),(81,false),(82,false),(88,false)]
theorem inp_5129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5129 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5129 (by decide) v hb
def cl_5130 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,true),(81,false),(82,false),(88,false)]
theorem inp_5130 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5130 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5130 (by decide) v hb
def cl_5131 : CNF.NClause := [(40,false),(9,false),(63,true),(69,false),(75,true),(81,false),(82,false),(88,false)]
theorem inp_5131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5131 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5131 (by decide) v hb
def cl_5132 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,true),(81,false),(82,false),(88,false)]
theorem inp_5132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5132 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5132 (by decide) v hb
def cl_5133 : CNF.NClause := [(40,false),(9,false),(63,false),(69,true),(75,true),(81,false),(82,false),(88,false)]
theorem inp_5133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5133 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5133 (by decide) v hb
def cl_5134 : CNF.NClause := [(40,false),(9,true),(63,false),(69,true),(75,true),(81,false),(82,false),(88,false)]
theorem inp_5134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5134 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5134 (by decide) v hb
def cl_5135 : CNF.NClause := [(40,false),(9,false),(63,true),(69,true),(75,true),(81,false),(82,false),(88,false)]
theorem inp_5135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5135 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5135 (by decide) v hb
def cl_5136 : CNF.NClause := [(40,false),(9,true),(63,true),(69,true),(75,true),(81,false),(82,false),(88,false)]
theorem inp_5136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5136 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5136 (by decide) v hb
def cl_5137 : CNF.NClause := [(40,false),(9,false),(63,false),(69,false),(75,false),(81,true),(82,false),(88,false)]
theorem inp_5137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5137 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5137 (by decide) v hb
def cl_5138 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,false),(81,true),(82,false),(88,false)]
theorem inp_5138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5138 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5138 (by decide) v hb
def cl_5139 : CNF.NClause := [(40,false),(9,false),(63,true),(69,false),(75,false),(81,true),(82,false),(88,false)]
theorem inp_5139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5139 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5139 (by decide) v hb
def cl_5140 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,false),(81,true),(82,false),(88,false)]
theorem inp_5140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5140 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5140 (by decide) v hb
def cl_5141 : CNF.NClause := [(40,false),(9,false),(63,false),(69,true),(75,false),(81,true),(82,false),(88,false)]
theorem inp_5141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5141 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5141 (by decide) v hb
def cl_5142 : CNF.NClause := [(40,false),(9,true),(63,false),(69,true),(75,false),(81,true),(82,false),(88,false)]
theorem inp_5142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5142 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5142 (by decide) v hb
def cl_5143 : CNF.NClause := [(40,false),(9,false),(63,true),(69,true),(75,false),(81,true),(82,false),(88,false)]
theorem inp_5143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5143 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5143 (by decide) v hb
def cl_5144 : CNF.NClause := [(40,false),(9,true),(63,true),(69,true),(75,false),(81,true),(82,false),(88,false)]
theorem inp_5144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5144 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5144 (by decide) v hb
def cl_5145 : CNF.NClause := [(40,false),(9,false),(63,false),(69,false),(75,true),(81,true),(82,false),(88,false)]
theorem inp_5145 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5145 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5145 (by decide) v hb
def cl_5146 : CNF.NClause := [(40,false),(9,true),(63,false),(69,false),(75,true),(81,true),(82,false),(88,false)]
theorem inp_5146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5146 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 9) (spread_mem 9) cl_5146 (by decide) v hb
end Percolation.NReplay
