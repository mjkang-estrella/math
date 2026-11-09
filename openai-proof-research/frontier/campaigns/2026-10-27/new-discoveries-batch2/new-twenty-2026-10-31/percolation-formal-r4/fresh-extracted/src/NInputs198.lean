import NInputs197
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_12976 : CNF.NClause := [(930,true),(938,false),(941,true),(949,true),(952,true),(958,true)]
theorem inp_12976 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12976 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 28) (closed_mem 26 28) cl_12976 (by decide) v hb
def cl_12978 : CNF.NClause := [(930,true),(936,true),(942,true),(948,true),(954,true),(956,false)]
theorem inp_12978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12978 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 29) (closed_mem 26 29) cl_12978 (by decide) v hb
def cl_12985 : CNF.NClause := [(930,true),(935,true),(940,true),(945,true),(950,false),(955,true)]
theorem inp_12985 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12985 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 30) (closed_mem 26 30) cl_12985 (by decide) v hb
def cl_12986 : CNF.NClause := [(930,true),(935,true),(940,true),(945,false),(950,true),(955,true)]
theorem inp_12986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12986 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 30) (closed_mem 26 30) cl_12986 (by decide) v hb
def cl_12987 : CNF.NClause := [(930,true),(935,true),(940,false),(945,true),(950,true),(955,true)]
theorem inp_12987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12987 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 30) (closed_mem 26 30) cl_12987 (by decide) v hb
def cl_12988 : CNF.NClause := [(930,true),(935,false),(940,true),(945,true),(950,true),(955,true)]
theorem inp_12988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12988 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 30) (closed_mem 26 30) cl_12988 (by decide) v hb
def cl_12993 : CNF.NClause := [(986,true),(987,true),(988,false),(989,true),(990,true),(991,true)]
theorem inp_12993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12993 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 0) (closed_mem 27 0) cl_12993 (by decide) v hb
def cl_12997 : CNF.NClause := [(965,true),(970,true),(975,true),(980,true),(985,false),(986,true)]
theorem inp_12997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12997 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 1) (closed_mem 27 1) cl_12997 (by decide) v hb
def cl_12998 : CNF.NClause := [(965,true),(970,true),(975,true),(980,false),(985,true),(986,true)]
theorem inp_12998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12998 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 1) (closed_mem 27 1) cl_12998 (by decide) v hb
def cl_12999 : CNF.NClause := [(965,true),(970,true),(975,false),(980,true),(985,true),(986,true)]
theorem inp_12999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12999 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 1) (closed_mem 27 1) cl_12999 (by decide) v hb
def cl_13001 : CNF.NClause := [(965,false),(970,true),(975,true),(980,true),(985,true),(986,true)]
theorem inp_13001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13001 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 1) (closed_mem 27 1) cl_13001 (by decide) v hb
def cl_13003 : CNF.NClause := [(963,true),(968,true),(973,true),(978,true),(983,false),(986,true)]
theorem inp_13003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13003 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 2) (closed_mem 27 2) cl_13003 (by decide) v hb
def cl_13007 : CNF.NClause := [(963,false),(968,true),(973,true),(978,true),(983,true),(986,true)]
theorem inp_13007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13007 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 2) (closed_mem 27 2) cl_13007 (by decide) v hb
def cl_13011 : CNF.NClause := [(964,true),(969,true),(974,false),(979,true),(984,true),(986,true)]
theorem inp_13011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13011 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 3) (closed_mem 27 3) cl_13011 (by decide) v hb
def cl_13012 : CNF.NClause := [(964,true),(969,false),(974,true),(979,true),(984,true),(986,true)]
theorem inp_13012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13012 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 3) (closed_mem 27 3) cl_13012 (by decide) v hb
def cl_13017 : CNF.NClause := [(962,true),(967,true),(972,false),(977,true),(982,true),(986,true)]
theorem inp_13017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13017 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 4) (closed_mem 27 4) cl_13017 (by decide) v hb
def cl_13018 : CNF.NClause := [(962,true),(967,false),(972,true),(977,true),(982,true),(986,true)]
theorem inp_13018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13018 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 4) (closed_mem 27 4) cl_13018 (by decide) v hb
def cl_13019 : CNF.NClause := [(962,false),(967,true),(972,true),(977,true),(982,true),(986,true)]
theorem inp_13019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13019 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 4) (closed_mem 27 4) cl_13019 (by decide) v hb
def cl_13022 : CNF.NClause := [(981,true),(982,true),(983,true),(984,false),(985,true),(991,true)]
theorem inp_13022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13022 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 5) (closed_mem 27 5) cl_13022 (by decide) v hb
def cl_13023 : CNF.NClause := [(981,true),(982,true),(983,false),(984,true),(985,true),(991,true)]
theorem inp_13023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13023 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 5) (closed_mem 27 5) cl_13023 (by decide) v hb
def cl_13024 : CNF.NClause := [(981,true),(982,false),(983,true),(984,true),(985,true),(991,true)]
theorem inp_13024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13024 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 5) (closed_mem 27 5) cl_13024 (by decide) v hb
def cl_13026 : CNF.NClause := [(965,true),(969,true),(973,true),(977,true),(981,true),(990,false)]
theorem inp_13026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13026 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 6) (closed_mem 27 6) cl_13026 (by decide) v hb
def cl_13028 : CNF.NClause := [(965,true),(969,true),(973,true),(977,false),(981,true),(990,true)]
theorem inp_13028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13028 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 6) (closed_mem 27 6) cl_13028 (by decide) v hb
def cl_13031 : CNF.NClause := [(965,false),(969,true),(973,true),(977,true),(981,true),(990,true)]
theorem inp_13031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13031 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 6) (closed_mem 27 6) cl_13031 (by decide) v hb
def cl_13032 : CNF.NClause := [(963,true),(970,true),(972,true),(979,true),(981,true),(988,false)]
theorem inp_13032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13032 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 7) (closed_mem 27 7) cl_13032 (by decide) v hb
def cl_13038 : CNF.NClause := [(964,true),(967,true),(975,true),(978,true),(981,true),(989,false)]
theorem inp_13038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13038 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13038 v hb
def cl_13040 : CNF.NClause := [(964,true),(967,true),(975,true),(978,false),(981,true),(989,true)]
theorem inp_13040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13040 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 8) (closed_mem 27 8) cl_13040 (by decide) v hb
def cl_13042 : CNF.NClause := [(964,true),(967,false),(975,true),(978,true),(981,true),(989,true)]
theorem inp_13042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13042 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 8) (closed_mem 27 8) cl_13042 (by decide) v hb
def cl_13044 : CNF.NClause := [(962,true),(968,true),(974,true),(980,true),(981,true),(987,false)]
theorem inp_13044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13044 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 9) (closed_mem 27 9) cl_13044 (by decide) v hb
def cl_13045 : CNF.NClause := [(962,true),(968,true),(974,true),(980,true),(981,false),(987,true)]
theorem inp_13045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13045 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 9) (closed_mem 27 9) cl_13045 (by decide) v hb
def cl_13046 : CNF.NClause := [(962,true),(968,true),(974,true),(980,false),(981,true),(987,true)]
theorem inp_13046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13046 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 9) (closed_mem 27 9) cl_13046 (by decide) v hb
def cl_13049 : CNF.NClause := [(962,false),(968,true),(974,true),(980,true),(981,true),(987,true)]
theorem inp_13049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13049 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 9) (closed_mem 27 9) cl_13049 (by decide) v hb
def cl_13053 : CNF.NClause := [(971,true),(972,true),(973,false),(974,true),(975,true),(991,true)]
theorem inp_13053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13053 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 10) (closed_mem 27 10) cl_13053 (by decide) v hb
def cl_13055 : CNF.NClause := [(971,false),(972,true),(973,true),(974,true),(975,true),(991,true)]
theorem inp_13055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13055 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 10) (closed_mem 27 10) cl_13055 (by decide) v hb
def cl_13057 : CNF.NClause := [(965,true),(968,true),(971,true),(979,true),(982,false),(989,true)]
theorem inp_13057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13057 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 11) (closed_mem 27 11) cl_13057 (by decide) v hb
def cl_13062 : CNF.NClause := [(963,true),(967,true),(971,true),(980,true),(984,true),(990,false)]
theorem inp_13062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13062 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 12) (closed_mem 27 12) cl_13062 (by decide) v hb
def cl_13063 : CNF.NClause := [(963,true),(967,true),(971,true),(980,true),(984,false),(990,true)]
theorem inp_13063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13063 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 12) (closed_mem 27 12) cl_13063 (by decide) v hb
def cl_13064 : CNF.NClause := [(963,true),(967,true),(971,true),(980,false),(984,true),(990,true)]
theorem inp_13064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13064 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 12) (closed_mem 27 12) cl_13064 (by decide) v hb
def cl_13066 : CNF.NClause := [(963,true),(967,false),(971,true),(980,true),(984,true),(990,true)]
theorem inp_13066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13066 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 12) (closed_mem 27 12) cl_13066 (by decide) v hb
def cl_13070 : CNF.NClause := [(964,true),(970,true),(971,true),(977,false),(983,true),(987,true)]
theorem inp_13070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13070 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 13) (closed_mem 27 13) cl_13070 (by decide) v hb
def cl_13071 : CNF.NClause := [(964,true),(970,true),(971,false),(977,true),(983,true),(987,true)]
theorem inp_13071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13071 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 13) (closed_mem 27 13) cl_13071 (by decide) v hb
def cl_13073 : CNF.NClause := [(964,false),(970,true),(971,true),(977,true),(983,true),(987,true)]
theorem inp_13073 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13073 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 13) (closed_mem 27 13) cl_13073 (by decide) v hb
def cl_13074 : CNF.NClause := [(962,true),(969,true),(971,true),(978,true),(985,true),(988,false)]
theorem inp_13074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13074 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 14) (closed_mem 27 14) cl_13074 (by decide) v hb
def cl_13083 : CNF.NClause := [(976,true),(977,true),(978,false),(979,true),(980,true),(991,true)]
theorem inp_13083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13083 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 15) (closed_mem 27 15) cl_13083 (by decide) v hb
def cl_13084 : CNF.NClause := [(976,true),(977,false),(978,true),(979,true),(980,true),(991,true)]
theorem inp_13084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13084 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 15) (closed_mem 27 15) cl_13084 (by decide) v hb
def cl_13085 : CNF.NClause := [(976,false),(977,true),(978,true),(979,true),(980,true),(991,true)]
theorem inp_13085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13085 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13085 v hb
def cl_13086 : CNF.NClause := [(965,true),(967,true),(974,true),(976,true),(983,true),(988,false)]
theorem inp_13086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13086 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13086 v hb
def cl_13095 : CNF.NClause := [(963,true),(969,true),(975,false),(976,true),(982,true),(987,true)]
theorem inp_13095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13095 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 17) (closed_mem 27 17) cl_13095 (by decide) v hb
def cl_13096 : CNF.NClause := [(963,true),(969,false),(975,true),(976,true),(982,true),(987,true)]
theorem inp_13096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13096 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 17) (closed_mem 27 17) cl_13096 (by decide) v hb
def cl_13098 : CNF.NClause := [(964,true),(968,true),(972,true),(976,true),(985,true),(990,false)]
theorem inp_13098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13098 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 27 18) (closed_mem 27 18) cl_13098 (by decide) v hb
end Percolation.NReplay
