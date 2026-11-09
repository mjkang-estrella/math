import NInputs188
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_12194 : CNF.NClause := [(808,true),(811,true),(819,true),(822,false),(830,true),(834,true)]
theorem inp_12194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12194 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 22) (closed_mem 22 22) cl_12194 (by decide) v hb
def cl_12195 : CNF.NClause := [(808,true),(811,true),(819,false),(822,true),(830,true),(834,true)]
theorem inp_12195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12195 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 22) (closed_mem 22 22) cl_12195 (by decide) v hb
def cl_12196 : CNF.NClause := [(808,true),(811,false),(819,true),(822,true),(830,true),(834,true)]
theorem inp_12196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12196 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 22) (closed_mem 22 22) cl_12196 (by decide) v hb
def cl_12197 : CNF.NClause := [(808,false),(811,true),(819,true),(822,true),(830,true),(834,true)]
theorem inp_12197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12197 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 22) (closed_mem 22 22) cl_12197 (by decide) v hb
def cl_12198 : CNF.NClause := [(809,true),(811,true),(818,true),(825,true),(827,true),(833,false)]
theorem inp_12198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12198 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 23) (closed_mem 22 23) cl_12198 (by decide) v hb
def cl_12199 : CNF.NClause := [(809,true),(811,true),(818,true),(825,true),(827,false),(833,true)]
theorem inp_12199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12199 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 23) (closed_mem 22 23) cl_12199 (by decide) v hb
def cl_12201 : CNF.NClause := [(809,true),(811,true),(818,false),(825,true),(827,true),(833,true)]
theorem inp_12201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12201 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 23) (closed_mem 22 23) cl_12201 (by decide) v hb
def cl_12202 : CNF.NClause := [(809,true),(811,false),(818,true),(825,true),(827,true),(833,true)]
theorem inp_12202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12202 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 23) (closed_mem 22 23) cl_12202 (by decide) v hb
def cl_12203 : CNF.NClause := [(809,false),(811,true),(818,true),(825,true),(827,true),(833,true)]
theorem inp_12203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12203 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 23) (closed_mem 22 23) cl_12203 (by decide) v hb
def cl_12205 : CNF.NClause := [(807,true),(811,true),(820,true),(824,true),(828,false),(835,true)]
theorem inp_12205 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12205 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 24) (closed_mem 22 24) cl_12205 (by decide) v hb
def cl_12211 : CNF.NClause := [(806,true),(807,true),(808,true),(809,true),(810,false),(836,true)]
theorem inp_12211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12211 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 25) (closed_mem 22 25) cl_12211 (by decide) v hb
def cl_12212 : CNF.NClause := [(806,true),(807,true),(808,true),(809,false),(810,true),(836,true)]
theorem inp_12212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12212 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 25) (closed_mem 22 25) cl_12212 (by decide) v hb
def cl_12213 : CNF.NClause := [(806,true),(807,true),(808,false),(809,true),(810,true),(836,true)]
theorem inp_12213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12213 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 25) (closed_mem 22 25) cl_12213 (by decide) v hb
def cl_12214 : CNF.NClause := [(806,true),(807,false),(808,true),(809,true),(810,true),(836,true)]
theorem inp_12214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12214 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 25) (closed_mem 22 25) cl_12214 (by decide) v hb
def cl_12216 : CNF.NClause := [(806,true),(815,true),(819,true),(823,true),(827,true),(835,false)]
theorem inp_12216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12216 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 26) (closed_mem 22 26) cl_12216 (by decide) v hb
def cl_12218 : CNF.NClause := [(806,true),(815,true),(819,true),(823,false),(827,true),(835,true)]
theorem inp_12218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12218 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 26) (closed_mem 22 26) cl_12218 (by decide) v hb
def cl_12219 : CNF.NClause := [(806,true),(815,true),(819,false),(823,true),(827,true),(835,true)]
theorem inp_12219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12219 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 26) (closed_mem 22 26) cl_12219 (by decide) v hb
def cl_12220 : CNF.NClause := [(806,true),(815,false),(819,true),(823,true),(827,true),(835,true)]
theorem inp_12220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12220 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 26) (closed_mem 22 26) cl_12220 (by decide) v hb
def cl_12222 : CNF.NClause := [(806,true),(813,true),(820,true),(822,true),(829,true),(833,false)]
theorem inp_12222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12222 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 27) (closed_mem 22 27) cl_12222 (by decide) v hb
def cl_12223 : CNF.NClause := [(806,true),(813,true),(820,true),(822,true),(829,false),(833,true)]
theorem inp_12223 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12223 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 27) (closed_mem 22 27) cl_12223 (by decide) v hb
def cl_12224 : CNF.NClause := [(806,true),(813,true),(820,true),(822,false),(829,true),(833,true)]
theorem inp_12224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12224 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 27) (closed_mem 22 27) cl_12224 (by decide) v hb
def cl_12225 : CNF.NClause := [(806,true),(813,true),(820,false),(822,true),(829,true),(833,true)]
theorem inp_12225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12225 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 27) (closed_mem 22 27) cl_12225 (by decide) v hb
def cl_12226 : CNF.NClause := [(806,true),(813,false),(820,true),(822,true),(829,true),(833,true)]
theorem inp_12226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12226 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 27) (closed_mem 22 27) cl_12226 (by decide) v hb
def cl_12229 : CNF.NClause := [(806,true),(814,true),(817,true),(825,true),(828,false),(834,true)]
theorem inp_12229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12229 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 28) (closed_mem 22 28) cl_12229 (by decide) v hb
def cl_12234 : CNF.NClause := [(806,true),(812,true),(818,true),(824,true),(830,true),(832,false)]
theorem inp_12234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12234 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 29) (closed_mem 22 29) cl_12234 (by decide) v hb
def cl_12235 : CNF.NClause := [(806,true),(812,true),(818,true),(824,true),(830,false),(832,true)]
theorem inp_12235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12235 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 29) (closed_mem 22 29) cl_12235 (by decide) v hb
def cl_12236 : CNF.NClause := [(806,true),(812,true),(818,true),(824,false),(830,true),(832,true)]
theorem inp_12236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12236 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 29) (closed_mem 22 29) cl_12236 (by decide) v hb
def cl_12237 : CNF.NClause := [(806,true),(812,true),(818,false),(824,true),(830,true),(832,true)]
theorem inp_12237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12237 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 29) (closed_mem 22 29) cl_12237 (by decide) v hb
def cl_12238 : CNF.NClause := [(806,true),(812,false),(818,true),(824,true),(830,true),(832,true)]
theorem inp_12238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12238 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 29) (closed_mem 22 29) cl_12238 (by decide) v hb
def cl_12241 : CNF.NClause := [(806,true),(811,true),(816,true),(821,true),(826,false),(831,true)]
theorem inp_12241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12241 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 30) (closed_mem 22 30) cl_12241 (by decide) v hb
def cl_12242 : CNF.NClause := [(806,true),(811,true),(816,true),(821,false),(826,true),(831,true)]
theorem inp_12242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12242 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 30) (closed_mem 22 30) cl_12242 (by decide) v hb
def cl_12243 : CNF.NClause := [(806,true),(811,true),(816,false),(821,true),(826,true),(831,true)]
theorem inp_12243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12243 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 30) (closed_mem 22 30) cl_12243 (by decide) v hb
def cl_12244 : CNF.NClause := [(806,true),(811,false),(816,true),(821,true),(826,true),(831,true)]
theorem inp_12244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12244 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 30) (closed_mem 22 30) cl_12244 (by decide) v hb
def cl_12247 : CNF.NClause := [(862,true),(863,true),(864,true),(865,true),(866,false),(867,true)]
theorem inp_12247 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12247 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 0) (closed_mem 23 0) cl_12247 (by decide) v hb
def cl_12248 : CNF.NClause := [(862,true),(863,true),(864,true),(865,false),(866,true),(867,true)]
theorem inp_12248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12248 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 0) (closed_mem 23 0) cl_12248 (by decide) v hb
def cl_12249 : CNF.NClause := [(862,true),(863,true),(864,false),(865,true),(866,true),(867,true)]
theorem inp_12249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12249 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 0) (closed_mem 23 0) cl_12249 (by decide) v hb
def cl_12250 : CNF.NClause := [(862,true),(863,false),(864,true),(865,true),(866,true),(867,true)]
theorem inp_12250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12250 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 0) (closed_mem 23 0) cl_12250 (by decide) v hb
def cl_12254 : CNF.NClause := [(841,true),(846,true),(851,true),(856,false),(861,true),(862,true)]
theorem inp_12254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12254 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 1) (closed_mem 23 1) cl_12254 (by decide) v hb
def cl_12255 : CNF.NClause := [(841,true),(846,true),(851,false),(856,true),(861,true),(862,true)]
theorem inp_12255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12255 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 1) (closed_mem 23 1) cl_12255 (by decide) v hb
def cl_12257 : CNF.NClause := [(841,false),(846,true),(851,true),(856,true),(861,true),(862,true)]
theorem inp_12257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12257 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 1) (closed_mem 23 1) cl_12257 (by decide) v hb
def cl_12260 : CNF.NClause := [(839,true),(844,true),(849,true),(854,false),(859,true),(862,true)]
theorem inp_12260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12260 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 2) (closed_mem 23 2) cl_12260 (by decide) v hb
def cl_12263 : CNF.NClause := [(839,false),(844,true),(849,true),(854,true),(859,true),(862,true)]
theorem inp_12263 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12263 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 2) (closed_mem 23 2) cl_12263 (by decide) v hb
def cl_12265 : CNF.NClause := [(840,true),(845,true),(850,true),(855,true),(860,false),(862,true)]
theorem inp_12265 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12265 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 3) (closed_mem 23 3) cl_12265 (by decide) v hb
def cl_12271 : CNF.NClause := [(838,true),(843,true),(848,true),(853,true),(858,false),(862,true)]
theorem inp_12271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12271 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 4) (closed_mem 23 4) cl_12271 (by decide) v hb
def cl_12272 : CNF.NClause := [(838,true),(843,true),(848,true),(853,false),(858,true),(862,true)]
theorem inp_12272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12272 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 4) (closed_mem 23 4) cl_12272 (by decide) v hb
def cl_12275 : CNF.NClause := [(838,false),(843,true),(848,true),(853,true),(858,true),(862,true)]
theorem inp_12275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12275 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 4) (closed_mem 23 4) cl_12275 (by decide) v hb
def cl_12278 : CNF.NClause := [(857,true),(858,true),(859,true),(860,false),(861,true),(867,true)]
theorem inp_12278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12278 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 5) (closed_mem 23 5) cl_12278 (by decide) v hb
def cl_12284 : CNF.NClause := [(841,true),(845,true),(849,true),(853,false),(857,true),(866,true)]
theorem inp_12284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12284 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 6) (closed_mem 23 6) cl_12284 (by decide) v hb
def cl_12286 : CNF.NClause := [(841,true),(845,false),(849,true),(853,true),(857,true),(866,true)]
theorem inp_12286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12286 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 6) (closed_mem 23 6) cl_12286 (by decide) v hb
def cl_12290 : CNF.NClause := [(839,true),(846,true),(848,true),(855,false),(857,true),(864,true)]
theorem inp_12290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12290 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 23 7) (closed_mem 23 7) cl_12290 (by decide) v hb
end Percolation.NReplay
