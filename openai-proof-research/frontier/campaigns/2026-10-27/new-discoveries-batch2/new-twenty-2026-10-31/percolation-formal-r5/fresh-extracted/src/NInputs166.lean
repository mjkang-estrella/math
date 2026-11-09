import NInputs165
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_10168 : CNF.NClause := [(465,true),(466,false),(467,true),(468,true),(469,true),(495,true)]
theorem inp_10168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10168 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 25) (closed_mem 11 25) cl_10168 (by decide) v hb
def cl_10170 : CNF.NClause := [(465,true),(474,true),(478,true),(482,true),(486,true),(494,false)]
theorem inp_10170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10170 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 26) (closed_mem 11 26) cl_10170 (by decide) v hb
def cl_10171 : CNF.NClause := [(465,true),(474,true),(478,true),(482,true),(486,false),(494,true)]
theorem inp_10171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10171 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 26) (closed_mem 11 26) cl_10171 (by decide) v hb
def cl_10172 : CNF.NClause := [(465,true),(474,true),(478,true),(482,false),(486,true),(494,true)]
theorem inp_10172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10172 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 26) (closed_mem 11 26) cl_10172 (by decide) v hb
def cl_10173 : CNF.NClause := [(465,true),(474,true),(478,false),(482,true),(486,true),(494,true)]
theorem inp_10173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10173 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 26) (closed_mem 11 26) cl_10173 (by decide) v hb
def cl_10174 : CNF.NClause := [(465,true),(474,false),(478,true),(482,true),(486,true),(494,true)]
theorem inp_10174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10174 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 26) (closed_mem 11 26) cl_10174 (by decide) v hb
def cl_10176 : CNF.NClause := [(465,true),(472,true),(479,true),(481,true),(488,true),(492,false)]
theorem inp_10176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10176 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 27) (closed_mem 11 27) cl_10176 (by decide) v hb
def cl_10177 : CNF.NClause := [(465,true),(472,true),(479,true),(481,true),(488,false),(492,true)]
theorem inp_10177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10177 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 27) (closed_mem 11 27) cl_10177 (by decide) v hb
def cl_10178 : CNF.NClause := [(465,true),(472,true),(479,true),(481,false),(488,true),(492,true)]
theorem inp_10178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10178 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 27) (closed_mem 11 27) cl_10178 (by decide) v hb
def cl_10179 : CNF.NClause := [(465,true),(472,true),(479,false),(481,true),(488,true),(492,true)]
theorem inp_10179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10179 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 27) (closed_mem 11 27) cl_10179 (by decide) v hb
def cl_10180 : CNF.NClause := [(465,true),(472,false),(479,true),(481,true),(488,true),(492,true)]
theorem inp_10180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10180 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 27) (closed_mem 11 27) cl_10180 (by decide) v hb
def cl_10185 : CNF.NClause := [(465,true),(473,true),(476,false),(484,true),(487,true),(493,true)]
theorem inp_10185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10185 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 28) (closed_mem 11 28) cl_10185 (by decide) v hb
def cl_10188 : CNF.NClause := [(465,true),(471,true),(477,true),(483,true),(489,true),(491,false)]
theorem inp_10188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10188 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 29) (closed_mem 11 29) cl_10188 (by decide) v hb
def cl_10189 : CNF.NClause := [(465,true),(471,true),(477,true),(483,true),(489,false),(491,true)]
theorem inp_10189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10189 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 29) (closed_mem 11 29) cl_10189 (by decide) v hb
def cl_10190 : CNF.NClause := [(465,true),(471,true),(477,true),(483,false),(489,true),(491,true)]
theorem inp_10190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10190 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 29) (closed_mem 11 29) cl_10190 (by decide) v hb
def cl_10191 : CNF.NClause := [(465,true),(471,true),(477,false),(483,true),(489,true),(491,true)]
theorem inp_10191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10191 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 29) (closed_mem 11 29) cl_10191 (by decide) v hb
def cl_10192 : CNF.NClause := [(465,true),(471,false),(477,true),(483,true),(489,true),(491,true)]
theorem inp_10192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10192 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 29) (closed_mem 11 29) cl_10192 (by decide) v hb
def cl_10195 : CNF.NClause := [(465,true),(470,true),(475,true),(480,true),(485,false),(490,true)]
theorem inp_10195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10195 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 30) (closed_mem 11 30) cl_10195 (by decide) v hb
def cl_10196 : CNF.NClause := [(465,true),(470,true),(475,true),(480,false),(485,true),(490,true)]
theorem inp_10196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10196 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 30) (closed_mem 11 30) cl_10196 (by decide) v hb
def cl_10197 : CNF.NClause := [(465,true),(470,true),(475,false),(480,true),(485,true),(490,true)]
theorem inp_10197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10197 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 30) (closed_mem 11 30) cl_10197 (by decide) v hb
def cl_10198 : CNF.NClause := [(465,true),(470,false),(475,true),(480,true),(485,true),(490,true)]
theorem inp_10198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10198 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 30) (closed_mem 11 30) cl_10198 (by decide) v hb
def cl_10201 : CNF.NClause := [(521,true),(522,true),(523,true),(524,true),(525,false),(526,true)]
theorem inp_10201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10201 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 0) (closed_mem 12 0) cl_10201 (by decide) v hb
def cl_10202 : CNF.NClause := [(521,true),(522,true),(523,true),(524,false),(525,true),(526,true)]
theorem inp_10202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10202 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 0) (closed_mem 12 0) cl_10202 (by decide) v hb
def cl_10203 : CNF.NClause := [(521,true),(522,true),(523,false),(524,true),(525,true),(526,true)]
theorem inp_10203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10203 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 0) (closed_mem 12 0) cl_10203 (by decide) v hb
def cl_10204 : CNF.NClause := [(521,true),(522,false),(523,true),(524,true),(525,true),(526,true)]
theorem inp_10204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10204 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 0) (closed_mem 12 0) cl_10204 (by decide) v hb
def cl_10207 : CNF.NClause := [(500,true),(505,true),(510,true),(515,true),(520,false),(521,true)]
theorem inp_10207 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10207 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 1) (closed_mem 12 1) cl_10207 (by decide) v hb
def cl_10208 : CNF.NClause := [(500,true),(505,true),(510,true),(515,false),(520,true),(521,true)]
theorem inp_10208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10208 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 1) (closed_mem 12 1) cl_10208 (by decide) v hb
def cl_10209 : CNF.NClause := [(500,true),(505,true),(510,false),(515,true),(520,true),(521,true)]
theorem inp_10209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10209 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 1) (closed_mem 12 1) cl_10209 (by decide) v hb
def cl_10210 : CNF.NClause := [(500,true),(505,false),(510,true),(515,true),(520,true),(521,true)]
theorem inp_10210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10210 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 1) (closed_mem 12 1) cl_10210 (by decide) v hb
def cl_10211 : CNF.NClause := [(500,false),(505,true),(510,true),(515,true),(520,true),(521,true)]
theorem inp_10211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10211 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 1) (closed_mem 12 1) cl_10211 (by decide) v hb
def cl_10215 : CNF.NClause := [(498,true),(503,true),(508,false),(513,true),(518,true),(521,true)]
theorem inp_10215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10215 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 2) (closed_mem 12 2) cl_10215 (by decide) v hb
def cl_10219 : CNF.NClause := [(499,true),(504,true),(509,true),(514,true),(519,false),(521,true)]
theorem inp_10219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10219 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 3) (closed_mem 12 3) cl_10219 (by decide) v hb
def cl_10220 : CNF.NClause := [(499,true),(504,true),(509,true),(514,false),(519,true),(521,true)]
theorem inp_10220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10220 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 3) (closed_mem 12 3) cl_10220 (by decide) v hb
def cl_10222 : CNF.NClause := [(499,true),(504,false),(509,true),(514,true),(519,true),(521,true)]
theorem inp_10222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10222 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 3) (closed_mem 12 3) cl_10222 (by decide) v hb
def cl_10223 : CNF.NClause := [(499,false),(504,true),(509,true),(514,true),(519,true),(521,true)]
theorem inp_10223 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10223 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 3) (closed_mem 12 3) cl_10223 (by decide) v hb
def cl_10227 : CNF.NClause := [(497,true),(502,true),(507,false),(512,true),(517,true),(521,true)]
theorem inp_10227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10227 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 4) (closed_mem 12 4) cl_10227 (by decide) v hb
def cl_10228 : CNF.NClause := [(497,true),(502,false),(507,true),(512,true),(517,true),(521,true)]
theorem inp_10228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10228 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 4) (closed_mem 12 4) cl_10228 (by decide) v hb
def cl_10229 : CNF.NClause := [(497,false),(502,true),(507,true),(512,true),(517,true),(521,true)]
theorem inp_10229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10229 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 4) (closed_mem 12 4) cl_10229 (by decide) v hb
def cl_10231 : CNF.NClause := [(516,true),(517,true),(518,true),(519,true),(520,false),(526,true)]
theorem inp_10231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10231 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 5) (closed_mem 12 5) cl_10231 (by decide) v hb
def cl_10232 : CNF.NClause := [(516,true),(517,true),(518,true),(519,false),(520,true),(526,true)]
theorem inp_10232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10232 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 5) (closed_mem 12 5) cl_10232 (by decide) v hb
def cl_10233 : CNF.NClause := [(516,true),(517,true),(518,false),(519,true),(520,true),(526,true)]
theorem inp_10233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10233 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 5) (closed_mem 12 5) cl_10233 (by decide) v hb
def cl_10234 : CNF.NClause := [(516,true),(517,false),(518,true),(519,true),(520,true),(526,true)]
theorem inp_10234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10234 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 5) (closed_mem 12 5) cl_10234 (by decide) v hb
def cl_10235 : CNF.NClause := [(516,false),(517,true),(518,true),(519,true),(520,true),(526,true)]
theorem inp_10235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10235 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 5) (closed_mem 12 5) cl_10235 (by decide) v hb
def cl_10239 : CNF.NClause := [(500,true),(504,true),(508,false),(512,true),(516,true),(525,true)]
theorem inp_10239 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10239 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 6) (closed_mem 12 6) cl_10239 (by decide) v hb
def cl_10243 : CNF.NClause := [(498,true),(505,true),(507,true),(514,true),(516,false),(523,true)]
theorem inp_10243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10243 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 7) (closed_mem 12 7) cl_10243 (by decide) v hb
def cl_10244 : CNF.NClause := [(498,true),(505,true),(507,true),(514,false),(516,true),(523,true)]
theorem inp_10244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10244 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 7) (closed_mem 12 7) cl_10244 (by decide) v hb
def cl_10245 : CNF.NClause := [(498,true),(505,true),(507,false),(514,true),(516,true),(523,true)]
theorem inp_10245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10245 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 7) (closed_mem 12 7) cl_10245 (by decide) v hb
def cl_10246 : CNF.NClause := [(498,true),(505,false),(507,true),(514,true),(516,true),(523,true)]
theorem inp_10246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10246 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 7) (closed_mem 12 7) cl_10246 (by decide) v hb
def cl_10248 : CNF.NClause := [(499,true),(502,true),(510,true),(513,true),(516,true),(524,false)]
theorem inp_10248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10248 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 8) (closed_mem 12 8) cl_10248 (by decide) v hb
def cl_10249 : CNF.NClause := [(499,true),(502,true),(510,true),(513,true),(516,false),(524,true)]
theorem inp_10249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10249 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 8) (closed_mem 12 8) cl_10249 (by decide) v hb
end Percolation.NReplay
