import NInputs198
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_13101 : CNF.NClause := [(964,true),(968,true),(972,false),(976,true),(985,true),(990,true)]
theorem inp_13101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13101 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 18) (closed_mem 27 18) cl_13101 (by decide) v hb
def cl_13104 : CNF.NClause := [(962,true),(970,true),(973,true),(976,true),(984,true),(989,false)]
theorem inp_13104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13104 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 19) (closed_mem 27 19) cl_13104 (by decide) v hb
def cl_13105 : CNF.NClause := [(962,true),(970,true),(973,true),(976,true),(984,false),(989,true)]
theorem inp_13105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13105 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 19) (closed_mem 27 19) cl_13105 (by decide) v hb
def cl_13106 : CNF.NClause := [(962,true),(970,true),(973,true),(976,false),(984,true),(989,true)]
theorem inp_13106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13106 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 19) (closed_mem 27 19) cl_13106 (by decide) v hb
def cl_13108 : CNF.NClause := [(962,true),(970,false),(973,true),(976,true),(984,true),(989,true)]
theorem inp_13108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13108 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 19) (closed_mem 27 19) cl_13108 (by decide) v hb
def cl_13109 : CNF.NClause := [(962,false),(970,true),(973,true),(976,true),(984,true),(989,true)]
theorem inp_13109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13109 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 19) (closed_mem 27 19) cl_13109 (by decide) v hb
def cl_13111 : CNF.NClause := [(966,true),(967,true),(968,true),(969,true),(970,false),(991,true)]
theorem inp_13111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13111 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 20) (closed_mem 27 20) cl_13111 (by decide) v hb
def cl_13114 : CNF.NClause := [(966,true),(967,false),(968,true),(969,true),(970,true),(991,true)]
theorem inp_13114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13114 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 20) (closed_mem 27 20) cl_13114 (by decide) v hb
def cl_13115 : CNF.NClause := [(966,false),(967,true),(968,true),(969,true),(970,true),(991,true)]
theorem inp_13115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13115 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 20) (closed_mem 27 20) cl_13115 (by decide) v hb
def cl_13117 : CNF.NClause := [(965,true),(966,true),(972,true),(978,true),(984,false),(987,true)]
theorem inp_13117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13117 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 21) (closed_mem 27 21) cl_13117 (by decide) v hb
def cl_13119 : CNF.NClause := [(965,true),(966,true),(972,false),(978,true),(984,true),(987,true)]
theorem inp_13119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13119 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 21) (closed_mem 27 21) cl_13119 (by decide) v hb
def cl_13120 : CNF.NClause := [(965,true),(966,false),(972,true),(978,true),(984,true),(987,true)]
theorem inp_13120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13120 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 21) (closed_mem 27 21) cl_13120 (by decide) v hb
def cl_13121 : CNF.NClause := [(965,false),(966,true),(972,true),(978,true),(984,true),(987,true)]
theorem inp_13121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13121 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 21) (closed_mem 27 21) cl_13121 (by decide) v hb
def cl_13123 : CNF.NClause := [(963,true),(966,true),(974,true),(977,true),(985,false),(989,true)]
theorem inp_13123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13123 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 22) (closed_mem 27 22) cl_13123 (by decide) v hb
def cl_13126 : CNF.NClause := [(963,true),(966,false),(974,true),(977,true),(985,true),(989,true)]
theorem inp_13126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13126 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 22) (closed_mem 27 22) cl_13126 (by decide) v hb
def cl_13128 : CNF.NClause := [(964,true),(966,true),(973,true),(980,true),(982,true),(988,false)]
theorem inp_13128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13128 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 23) (closed_mem 27 23) cl_13128 (by decide) v hb
def cl_13137 : CNF.NClause := [(962,true),(966,true),(975,false),(979,true),(983,true),(990,true)]
theorem inp_13137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13137 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 24) (closed_mem 27 24) cl_13137 (by decide) v hb
def cl_13139 : CNF.NClause := [(962,false),(966,true),(975,true),(979,true),(983,true),(990,true)]
theorem inp_13139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13139 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 24) (closed_mem 27 24) cl_13139 (by decide) v hb
def cl_13141 : CNF.NClause := [(961,true),(962,true),(963,true),(964,true),(965,false),(991,true)]
theorem inp_13141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13141 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 25) (closed_mem 27 25) cl_13141 (by decide) v hb
def cl_13142 : CNF.NClause := [(961,true),(962,true),(963,true),(964,false),(965,true),(991,true)]
theorem inp_13142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13142 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 25) (closed_mem 27 25) cl_13142 (by decide) v hb
def cl_13143 : CNF.NClause := [(961,true),(962,true),(963,false),(964,true),(965,true),(991,true)]
theorem inp_13143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13143 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 25) (closed_mem 27 25) cl_13143 (by decide) v hb
def cl_13144 : CNF.NClause := [(961,true),(962,false),(963,true),(964,true),(965,true),(991,true)]
theorem inp_13144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13144 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 25) (closed_mem 27 25) cl_13144 (by decide) v hb
def cl_13146 : CNF.NClause := [(961,true),(970,true),(974,true),(978,true),(982,true),(990,false)]
theorem inp_13146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13146 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 26) (closed_mem 27 26) cl_13146 (by decide) v hb
def cl_13147 : CNF.NClause := [(961,true),(970,true),(974,true),(978,true),(982,false),(990,true)]
theorem inp_13147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13147 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 26) (closed_mem 27 26) cl_13147 (by decide) v hb
def cl_13149 : CNF.NClause := [(961,true),(970,true),(974,false),(978,true),(982,true),(990,true)]
theorem inp_13149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13149 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 26) (closed_mem 27 26) cl_13149 (by decide) v hb
def cl_13150 : CNF.NClause := [(961,true),(970,false),(974,true),(978,true),(982,true),(990,true)]
theorem inp_13150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13150 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 26) (closed_mem 27 26) cl_13150 (by decide) v hb
def cl_13152 : CNF.NClause := [(961,true),(968,true),(975,true),(977,true),(984,true),(988,false)]
theorem inp_13152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13152 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 27) (closed_mem 27 27) cl_13152 (by decide) v hb
def cl_13158 : CNF.NClause := [(961,true),(969,true),(972,true),(980,true),(983,true),(989,false)]
theorem inp_13158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13158 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 28) (closed_mem 27 28) cl_13158 (by decide) v hb
def cl_13159 : CNF.NClause := [(961,true),(969,true),(972,true),(980,true),(983,false),(989,true)]
theorem inp_13159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13159 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 28) (closed_mem 27 28) cl_13159 (by decide) v hb
def cl_13162 : CNF.NClause := [(961,true),(969,false),(972,true),(980,true),(983,true),(989,true)]
theorem inp_13162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13162 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 28) (closed_mem 27 28) cl_13162 (by decide) v hb
def cl_13165 : CNF.NClause := [(961,true),(967,true),(973,true),(979,true),(985,false),(987,true)]
theorem inp_13165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13165 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 29) (closed_mem 27 29) cl_13165 (by decide) v hb
def cl_13167 : CNF.NClause := [(961,true),(967,true),(973,false),(979,true),(985,true),(987,true)]
theorem inp_13167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13167 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 29) (closed_mem 27 29) cl_13167 (by decide) v hb
def cl_13168 : CNF.NClause := [(961,true),(967,false),(973,true),(979,true),(985,true),(987,true)]
theorem inp_13168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13168 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 29) (closed_mem 27 29) cl_13168 (by decide) v hb
def cl_13172 : CNF.NClause := [(961,true),(966,true),(971,true),(976,false),(981,true),(986,true)]
theorem inp_13172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13172 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 30) (closed_mem 27 30) cl_13172 (by decide) v hb
def cl_13173 : CNF.NClause := [(961,true),(966,true),(971,false),(976,true),(981,true),(986,true)]
theorem inp_13173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13173 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 30) (closed_mem 27 30) cl_13173 (by decide) v hb
def cl_13174 : CNF.NClause := [(961,true),(966,false),(971,true),(976,true),(981,true),(986,true)]
theorem inp_13174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13174 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 30) (closed_mem 27 30) cl_13174 (by decide) v hb
def cl_13178 : CNF.NClause := [(1017,true),(1018,true),(1019,true),(1020,false),(1021,true),(1022,true)]
theorem inp_13178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13178 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 0) (closed_mem 28 0) cl_13178 (by decide) v hb
def cl_13183 : CNF.NClause := [(996,true),(1001,true),(1006,true),(1011,true),(1016,false),(1017,true)]
theorem inp_13183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13183 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 1) (closed_mem 28 1) cl_13183 (by decide) v hb
def cl_13185 : CNF.NClause := [(996,true),(1001,true),(1006,false),(1011,true),(1016,true),(1017,true)]
theorem inp_13185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13185 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 1) (closed_mem 28 1) cl_13185 (by decide) v hb
def cl_13187 : CNF.NClause := [(996,false),(1001,true),(1006,true),(1011,true),(1016,true),(1017,true)]
theorem inp_13187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13187 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 1) (closed_mem 28 1) cl_13187 (by decide) v hb
def cl_13189 : CNF.NClause := [(994,true),(999,true),(1004,true),(1009,true),(1014,false),(1017,true)]
theorem inp_13189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13189 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 2) (closed_mem 28 2) cl_13189 (by decide) v hb
def cl_13190 : CNF.NClause := [(994,true),(999,true),(1004,true),(1009,false),(1014,true),(1017,true)]
theorem inp_13190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13190 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 2) (closed_mem 28 2) cl_13190 (by decide) v hb
def cl_13191 : CNF.NClause := [(994,true),(999,true),(1004,false),(1009,true),(1014,true),(1017,true)]
theorem inp_13191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13191 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 2) (closed_mem 28 2) cl_13191 (by decide) v hb
def cl_13193 : CNF.NClause := [(994,false),(999,true),(1004,true),(1009,true),(1014,true),(1017,true)]
theorem inp_13193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13193 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13193 v hb
def cl_13195 : CNF.NClause := [(995,true),(1000,true),(1005,true),(1010,true),(1015,false),(1017,true)]
theorem inp_13195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13195 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 3) (closed_mem 28 3) cl_13195 (by decide) v hb
def cl_13197 : CNF.NClause := [(995,true),(1000,true),(1005,false),(1010,true),(1015,true),(1017,true)]
theorem inp_13197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13197 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13197 v hb
def cl_13198 : CNF.NClause := [(995,true),(1000,false),(1005,true),(1010,true),(1015,true),(1017,true)]
theorem inp_13198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13198 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 3) (closed_mem 28 3) cl_13198 (by decide) v hb
def cl_13199 : CNF.NClause := [(995,false),(1000,true),(1005,true),(1010,true),(1015,true),(1017,true)]
theorem inp_13199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13199 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 3) (closed_mem 28 3) cl_13199 (by decide) v hb
def cl_13201 : CNF.NClause := [(993,true),(998,true),(1003,true),(1008,true),(1013,false),(1017,true)]
theorem inp_13201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13201 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 4) (closed_mem 28 4) cl_13201 (by decide) v hb
def cl_13202 : CNF.NClause := [(993,true),(998,true),(1003,true),(1008,false),(1013,true),(1017,true)]
theorem inp_13202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13202 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 28 4) (closed_mem 28 4) cl_13202 (by decide) v hb
end Percolation.NReplay
