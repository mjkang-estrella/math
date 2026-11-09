import NInputs175
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_11061 : CNF.NClause := [(621,true),(629,true),(632,false),(635,true),(643,true),(648,true)]
theorem inp_11061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11061 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 19) (closed_mem 16 19) cl_11061 (by decide) v hb
def cl_11063 : CNF.NClause := [(621,false),(629,true),(632,true),(635,true),(643,true),(648,true)]
theorem inp_11063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11063 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 19) (closed_mem 16 19) cl_11063 (by decide) v hb
def cl_11065 : CNF.NClause := [(625,true),(626,true),(627,true),(628,true),(629,false),(650,true)]
theorem inp_11065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11065 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 20) (closed_mem 16 20) cl_11065 (by decide) v hb
def cl_11066 : CNF.NClause := [(625,true),(626,true),(627,true),(628,false),(629,true),(650,true)]
theorem inp_11066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11066 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 20) (closed_mem 16 20) cl_11066 (by decide) v hb
def cl_11067 : CNF.NClause := [(625,true),(626,true),(627,false),(628,true),(629,true),(650,true)]
theorem inp_11067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11067 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 20) (closed_mem 16 20) cl_11067 (by decide) v hb
def cl_11068 : CNF.NClause := [(625,true),(626,false),(627,true),(628,true),(629,true),(650,true)]
theorem inp_11068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11068 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 20) (closed_mem 16 20) cl_11068 (by decide) v hb
def cl_11069 : CNF.NClause := [(625,false),(626,true),(627,true),(628,true),(629,true),(650,true)]
theorem inp_11069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11069 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 20) (closed_mem 16 20) cl_11069 (by decide) v hb
def cl_11071 : CNF.NClause := [(624,true),(625,true),(631,true),(637,true),(643,false),(646,true)]
theorem inp_11071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11071 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 21) (closed_mem 16 21) cl_11071 (by decide) v hb
def cl_11073 : CNF.NClause := [(624,true),(625,true),(631,false),(637,true),(643,true),(646,true)]
theorem inp_11073 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11073 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 21) (closed_mem 16 21) cl_11073 (by decide) v hb
def cl_11075 : CNF.NClause := [(624,false),(625,true),(631,true),(637,true),(643,true),(646,true)]
theorem inp_11075 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11075 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 21) (closed_mem 16 21) cl_11075 (by decide) v hb
def cl_11078 : CNF.NClause := [(622,true),(625,true),(633,true),(636,false),(644,true),(648,true)]
theorem inp_11078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11078 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 22) (closed_mem 16 22) cl_11078 (by decide) v hb
def cl_11082 : CNF.NClause := [(623,true),(625,true),(632,true),(639,true),(641,true),(647,false)]
theorem inp_11082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11082 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 23) (closed_mem 16 23) cl_11082 (by decide) v hb
def cl_11086 : CNF.NClause := [(623,true),(625,false),(632,true),(639,true),(641,true),(647,true)]
theorem inp_11086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11086 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 23) (closed_mem 16 23) cl_11086 (by decide) v hb
def cl_11087 : CNF.NClause := [(623,false),(625,true),(632,true),(639,true),(641,true),(647,true)]
theorem inp_11087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11087 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 23) (closed_mem 16 23) cl_11087 (by decide) v hb
def cl_11091 : CNF.NClause := [(621,true),(625,true),(634,false),(638,true),(642,true),(649,true)]
theorem inp_11091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11091 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 24) (closed_mem 16 24) cl_11091 (by decide) v hb
def cl_11092 : CNF.NClause := [(621,true),(625,false),(634,true),(638,true),(642,true),(649,true)]
theorem inp_11092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11092 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 24) (closed_mem 16 24) cl_11092 (by decide) v hb
def cl_11093 : CNF.NClause := [(621,false),(625,true),(634,true),(638,true),(642,true),(649,true)]
theorem inp_11093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11093 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 24) (closed_mem 16 24) cl_11093 (by decide) v hb
def cl_11095 : CNF.NClause := [(620,true),(621,true),(622,true),(623,true),(624,false),(650,true)]
theorem inp_11095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11095 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 25) (closed_mem 16 25) cl_11095 (by decide) v hb
def cl_11096 : CNF.NClause := [(620,true),(621,true),(622,true),(623,false),(624,true),(650,true)]
theorem inp_11096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11096 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 25) (closed_mem 16 25) cl_11096 (by decide) v hb
def cl_11097 : CNF.NClause := [(620,true),(621,true),(622,false),(623,true),(624,true),(650,true)]
theorem inp_11097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11097 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 25) (closed_mem 16 25) cl_11097 (by decide) v hb
def cl_11098 : CNF.NClause := [(620,true),(621,false),(622,true),(623,true),(624,true),(650,true)]
theorem inp_11098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11098 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 25) (closed_mem 16 25) cl_11098 (by decide) v hb
def cl_11101 : CNF.NClause := [(620,true),(629,true),(633,true),(637,true),(641,false),(649,true)]
theorem inp_11101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11101 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 26) (closed_mem 16 26) cl_11101 (by decide) v hb
def cl_11102 : CNF.NClause := [(620,true),(629,true),(633,true),(637,false),(641,true),(649,true)]
theorem inp_11102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11102 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 26) (closed_mem 16 26) cl_11102 (by decide) v hb
def cl_11103 : CNF.NClause := [(620,true),(629,true),(633,false),(637,true),(641,true),(649,true)]
theorem inp_11103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11103 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 26) (closed_mem 16 26) cl_11103 (by decide) v hb
def cl_11104 : CNF.NClause := [(620,true),(629,false),(633,true),(637,true),(641,true),(649,true)]
theorem inp_11104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11104 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 26) (closed_mem 16 26) cl_11104 (by decide) v hb
def cl_11108 : CNF.NClause := [(620,true),(627,true),(634,true),(636,false),(643,true),(647,true)]
theorem inp_11108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11108 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 27) (closed_mem 16 27) cl_11108 (by decide) v hb
def cl_11113 : CNF.NClause := [(620,true),(628,true),(631,true),(639,true),(642,false),(648,true)]
theorem inp_11113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11113 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 28) (closed_mem 16 28) cl_11113 (by decide) v hb
def cl_11114 : CNF.NClause := [(620,true),(628,true),(631,true),(639,false),(642,true),(648,true)]
theorem inp_11114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11114 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 28) (closed_mem 16 28) cl_11114 (by decide) v hb
def cl_11115 : CNF.NClause := [(620,true),(628,true),(631,false),(639,true),(642,true),(648,true)]
theorem inp_11115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11115 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 28) (closed_mem 16 28) cl_11115 (by decide) v hb
def cl_11116 : CNF.NClause := [(620,true),(628,false),(631,true),(639,true),(642,true),(648,true)]
theorem inp_11116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11116 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 28) (closed_mem 16 28) cl_11116 (by decide) v hb
def cl_11119 : CNF.NClause := [(620,true),(626,true),(632,true),(638,true),(644,false),(646,true)]
theorem inp_11119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11119 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 29) (closed_mem 16 29) cl_11119 (by decide) v hb
def cl_11120 : CNF.NClause := [(620,true),(626,true),(632,true),(638,false),(644,true),(646,true)]
theorem inp_11120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11120 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 29) (closed_mem 16 29) cl_11120 (by decide) v hb
def cl_11121 : CNF.NClause := [(620,true),(626,true),(632,false),(638,true),(644,true),(646,true)]
theorem inp_11121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11121 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 29) (closed_mem 16 29) cl_11121 (by decide) v hb
def cl_11122 : CNF.NClause := [(620,true),(626,false),(632,true),(638,true),(644,true),(646,true)]
theorem inp_11122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11122 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 29) (closed_mem 16 29) cl_11122 (by decide) v hb
def cl_11125 : CNF.NClause := [(620,true),(625,true),(630,true),(635,true),(640,false),(645,true)]
theorem inp_11125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11125 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 30) (closed_mem 16 30) cl_11125 (by decide) v hb
def cl_11126 : CNF.NClause := [(620,true),(625,true),(630,true),(635,false),(640,true),(645,true)]
theorem inp_11126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11126 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 30) (closed_mem 16 30) cl_11126 (by decide) v hb
def cl_11127 : CNF.NClause := [(620,true),(625,true),(630,false),(635,true),(640,true),(645,true)]
theorem inp_11127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11127 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 30) (closed_mem 16 30) cl_11127 (by decide) v hb
def cl_11128 : CNF.NClause := [(620,true),(625,false),(630,true),(635,true),(640,true),(645,true)]
theorem inp_11128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11128 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 30) (closed_mem 16 30) cl_11128 (by decide) v hb
def cl_11131 : CNF.NClause := [(676,true),(677,true),(678,true),(679,true),(680,false),(681,true)]
theorem inp_11131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11131 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 0) (closed_mem 17 0) cl_11131 (by decide) v hb
def cl_11132 : CNF.NClause := [(676,true),(677,true),(678,true),(679,false),(680,true),(681,true)]
theorem inp_11132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11132 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 0) (closed_mem 17 0) cl_11132 (by decide) v hb
def cl_11133 : CNF.NClause := [(676,true),(677,true),(678,false),(679,true),(680,true),(681,true)]
theorem inp_11133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11133 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 0) (closed_mem 17 0) cl_11133 (by decide) v hb
def cl_11134 : CNF.NClause := [(676,true),(677,false),(678,true),(679,true),(680,true),(681,true)]
theorem inp_11134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11134 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 0) (closed_mem 17 0) cl_11134 (by decide) v hb
def cl_11137 : CNF.NClause := [(655,true),(660,true),(665,true),(670,true),(675,false),(676,true)]
theorem inp_11137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11137 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 1) (closed_mem 17 1) cl_11137 (by decide) v hb
def cl_11139 : CNF.NClause := [(655,true),(660,true),(665,false),(670,true),(675,true),(676,true)]
theorem inp_11139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11139 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 1) (closed_mem 17 1) cl_11139 (by decide) v hb
def cl_11140 : CNF.NClause := [(655,true),(660,false),(665,true),(670,true),(675,true),(676,true)]
theorem inp_11140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11140 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 1) (closed_mem 17 1) cl_11140 (by decide) v hb
def cl_11141 : CNF.NClause := [(655,false),(660,true),(665,true),(670,true),(675,true),(676,true)]
theorem inp_11141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11141 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 1) (closed_mem 17 1) cl_11141 (by decide) v hb
def cl_11144 : CNF.NClause := [(653,true),(658,true),(663,true),(668,false),(673,true),(676,true)]
theorem inp_11144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11144 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 2) (closed_mem 17 2) cl_11144 (by decide) v hb
def cl_11149 : CNF.NClause := [(654,true),(659,true),(664,true),(669,true),(674,false),(676,true)]
theorem inp_11149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11149 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 3) (closed_mem 17 3) cl_11149 (by decide) v hb
def cl_11150 : CNF.NClause := [(654,true),(659,true),(664,true),(669,false),(674,true),(676,true)]
theorem inp_11150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11150 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 3) (closed_mem 17 3) cl_11150 (by decide) v hb
def cl_11152 : CNF.NClause := [(654,true),(659,false),(664,true),(669,true),(674,true),(676,true)]
theorem inp_11152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11152 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 3) (closed_mem 17 3) cl_11152 (by decide) v hb
end Percolation.NReplay
