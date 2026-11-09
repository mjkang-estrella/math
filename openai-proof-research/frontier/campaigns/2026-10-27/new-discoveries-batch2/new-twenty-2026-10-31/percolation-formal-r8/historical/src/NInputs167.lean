import NInputs166
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_10250 : CNF.NClause := [(499,true),(502,true),(510,true),(513,false),(516,true),(524,true)]
theorem inp_10250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10250 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 8) (closed_mem 12 8) cl_10250 (by decide) v hb
def cl_10251 : CNF.NClause := [(499,true),(502,true),(510,false),(513,true),(516,true),(524,true)]
theorem inp_10251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10251 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 8) (closed_mem 12 8) cl_10251 (by decide) v hb
def cl_10252 : CNF.NClause := [(499,true),(502,false),(510,true),(513,true),(516,true),(524,true)]
theorem inp_10252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10252 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 8) (closed_mem 12 8) cl_10252 (by decide) v hb
def cl_10253 : CNF.NClause := [(499,false),(502,true),(510,true),(513,true),(516,true),(524,true)]
theorem inp_10253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10253 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 8) (closed_mem 12 8) cl_10253 (by decide) v hb
def cl_10255 : CNF.NClause := [(497,true),(503,true),(509,true),(515,true),(516,false),(522,true)]
theorem inp_10255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10255 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 9) (closed_mem 12 9) cl_10255 (by decide) v hb
def cl_10257 : CNF.NClause := [(497,true),(503,true),(509,false),(515,true),(516,true),(522,true)]
theorem inp_10257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10257 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 9) (closed_mem 12 9) cl_10257 (by decide) v hb
def cl_10259 : CNF.NClause := [(497,false),(503,true),(509,true),(515,true),(516,true),(522,true)]
theorem inp_10259 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10259 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 9) (closed_mem 12 9) cl_10259 (by decide) v hb
def cl_10263 : CNF.NClause := [(506,true),(507,true),(508,false),(509,true),(510,true),(526,true)]
theorem inp_10263 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10263 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 10) (closed_mem 12 10) cl_10263 (by decide) v hb
def cl_10266 : CNF.NClause := [(500,true),(503,true),(506,true),(514,true),(517,true),(524,false)]
theorem inp_10266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10266 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 11) (closed_mem 12 11) cl_10266 (by decide) v hb
def cl_10268 : CNF.NClause := [(500,true),(503,true),(506,true),(514,false),(517,true),(524,true)]
theorem inp_10268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10268 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 11) (closed_mem 12 11) cl_10268 (by decide) v hb
def cl_10270 : CNF.NClause := [(500,true),(503,false),(506,true),(514,true),(517,true),(524,true)]
theorem inp_10270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10270 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 11) (closed_mem 12 11) cl_10270 (by decide) v hb
def cl_10271 : CNF.NClause := [(500,false),(503,true),(506,true),(514,true),(517,true),(524,true)]
theorem inp_10271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10271 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 11) (closed_mem 12 11) cl_10271 (by decide) v hb
def cl_10273 : CNF.NClause := [(498,true),(502,true),(506,true),(515,true),(519,false),(525,true)]
theorem inp_10273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10273 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 12) (closed_mem 12 12) cl_10273 (by decide) v hb
def cl_10274 : CNF.NClause := [(498,true),(502,true),(506,true),(515,false),(519,true),(525,true)]
theorem inp_10274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10274 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 12) (closed_mem 12 12) cl_10274 (by decide) v hb
def cl_10275 : CNF.NClause := [(498,true),(502,true),(506,false),(515,true),(519,true),(525,true)]
theorem inp_10275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10275 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 12) (closed_mem 12 12) cl_10275 (by decide) v hb
def cl_10276 : CNF.NClause := [(498,true),(502,false),(506,true),(515,true),(519,true),(525,true)]
theorem inp_10276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10276 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 12) (closed_mem 12 12) cl_10276 (by decide) v hb
def cl_10277 : CNF.NClause := [(498,false),(502,true),(506,true),(515,true),(519,true),(525,true)]
theorem inp_10277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10277 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 12) (closed_mem 12 12) cl_10277 (by decide) v hb
def cl_10278 : CNF.NClause := [(499,true),(505,true),(506,true),(512,true),(518,true),(522,false)]
theorem inp_10278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10278 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 13) (closed_mem 12 13) cl_10278 (by decide) v hb
def cl_10281 : CNF.NClause := [(499,true),(505,true),(506,false),(512,true),(518,true),(522,true)]
theorem inp_10281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10281 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 13) (closed_mem 12 13) cl_10281 (by decide) v hb
def cl_10283 : CNF.NClause := [(499,false),(505,true),(506,true),(512,true),(518,true),(522,true)]
theorem inp_10283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10283 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 13) (closed_mem 12 13) cl_10283 (by decide) v hb
def cl_10285 : CNF.NClause := [(497,true),(504,true),(506,true),(513,true),(520,false),(523,true)]
theorem inp_10285 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10285 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 14) (closed_mem 12 14) cl_10285 (by decide) v hb
def cl_10286 : CNF.NClause := [(497,true),(504,true),(506,true),(513,false),(520,true),(523,true)]
theorem inp_10286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10286 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 14) (closed_mem 12 14) cl_10286 (by decide) v hb
def cl_10288 : CNF.NClause := [(497,true),(504,false),(506,true),(513,true),(520,true),(523,true)]
theorem inp_10288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10288 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 14) (closed_mem 12 14) cl_10288 (by decide) v hb
def cl_10289 : CNF.NClause := [(497,false),(504,true),(506,true),(513,true),(520,true),(523,true)]
theorem inp_10289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10289 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 14) (closed_mem 12 14) cl_10289 (by decide) v hb
def cl_10292 : CNF.NClause := [(511,true),(512,true),(513,true),(514,false),(515,true),(526,true)]
theorem inp_10292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10292 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 15) (closed_mem 12 15) cl_10292 (by decide) v hb
def cl_10293 : CNF.NClause := [(511,true),(512,true),(513,false),(514,true),(515,true),(526,true)]
theorem inp_10293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10293 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 15) (closed_mem 12 15) cl_10293 (by decide) v hb
def cl_10294 : CNF.NClause := [(511,true),(512,false),(513,true),(514,true),(515,true),(526,true)]
theorem inp_10294 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10294 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 15) (closed_mem 12 15) cl_10294 (by decide) v hb
def cl_10295 : CNF.NClause := [(511,false),(512,true),(513,true),(514,true),(515,true),(526,true)]
theorem inp_10295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10295 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 15) (closed_mem 12 15) cl_10295 (by decide) v hb
def cl_10298 : CNF.NClause := [(500,true),(502,true),(509,true),(511,false),(518,true),(523,true)]
theorem inp_10298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10298 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 16) (closed_mem 12 16) cl_10298 (by decide) v hb
def cl_10300 : CNF.NClause := [(500,true),(502,false),(509,true),(511,true),(518,true),(523,true)]
theorem inp_10300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10300 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 16) (closed_mem 12 16) cl_10300 (by decide) v hb
def cl_10301 : CNF.NClause := [(500,false),(502,true),(509,true),(511,true),(518,true),(523,true)]
theorem inp_10301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10301 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 16) (closed_mem 12 16) cl_10301 (by decide) v hb
def cl_10302 : CNF.NClause := [(498,true),(504,true),(510,true),(511,true),(517,true),(522,false)]
theorem inp_10302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10302 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 17) (closed_mem 12 17) cl_10302 (by decide) v hb
def cl_10304 : CNF.NClause := [(498,true),(504,true),(510,true),(511,false),(517,true),(522,true)]
theorem inp_10304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10304 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 17) (closed_mem 12 17) cl_10304 (by decide) v hb
def cl_10305 : CNF.NClause := [(498,true),(504,true),(510,false),(511,true),(517,true),(522,true)]
theorem inp_10305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10305 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 17) (closed_mem 12 17) cl_10305 (by decide) v hb
def cl_10306 : CNF.NClause := [(498,true),(504,false),(510,true),(511,true),(517,true),(522,true)]
theorem inp_10306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10306 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 17) (closed_mem 12 17) cl_10306 (by decide) v hb
def cl_10307 : CNF.NClause := [(498,false),(504,true),(510,true),(511,true),(517,true),(522,true)]
theorem inp_10307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10307 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 17) (closed_mem 12 17) cl_10307 (by decide) v hb
def cl_10311 : CNF.NClause := [(499,true),(503,true),(507,false),(511,true),(520,true),(525,true)]
theorem inp_10311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10311 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 18) (closed_mem 12 18) cl_10311 (by decide) v hb
def cl_10312 : CNF.NClause := [(499,true),(503,false),(507,true),(511,true),(520,true),(525,true)]
theorem inp_10312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10312 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 18) (closed_mem 12 18) cl_10312 (by decide) v hb
def cl_10317 : CNF.NClause := [(497,true),(505,true),(508,false),(511,true),(519,true),(524,true)]
theorem inp_10317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10317 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 19) (closed_mem 12 19) cl_10317 (by decide) v hb
def cl_10321 : CNF.NClause := [(501,true),(502,true),(503,true),(504,true),(505,false),(526,true)]
theorem inp_10321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10321 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 20) (closed_mem 12 20) cl_10321 (by decide) v hb
def cl_10322 : CNF.NClause := [(501,true),(502,true),(503,true),(504,false),(505,true),(526,true)]
theorem inp_10322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10322 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 20) (closed_mem 12 20) cl_10322 (by decide) v hb
def cl_10323 : CNF.NClause := [(501,true),(502,true),(503,false),(504,true),(505,true),(526,true)]
theorem inp_10323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10323 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 20) (closed_mem 12 20) cl_10323 (by decide) v hb
def cl_10324 : CNF.NClause := [(501,true),(502,false),(503,true),(504,true),(505,true),(526,true)]
theorem inp_10324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10324 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 20) (closed_mem 12 20) cl_10324 (by decide) v hb
def cl_10325 : CNF.NClause := [(501,false),(502,true),(503,true),(504,true),(505,true),(526,true)]
theorem inp_10325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10325 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 20) (closed_mem 12 20) cl_10325 (by decide) v hb
def cl_10326 : CNF.NClause := [(500,true),(501,true),(507,true),(513,true),(519,true),(522,false)]
theorem inp_10326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10326 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 21) (closed_mem 12 21) cl_10326 (by decide) v hb
def cl_10327 : CNF.NClause := [(500,true),(501,true),(507,true),(513,true),(519,false),(522,true)]
theorem inp_10327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10327 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 21) (closed_mem 12 21) cl_10327 (by decide) v hb
def cl_10328 : CNF.NClause := [(500,true),(501,true),(507,true),(513,false),(519,true),(522,true)]
theorem inp_10328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10328 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 21) (closed_mem 12 21) cl_10328 (by decide) v hb
def cl_10329 : CNF.NClause := [(500,true),(501,true),(507,false),(513,true),(519,true),(522,true)]
theorem inp_10329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10329 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 21) (closed_mem 12 21) cl_10329 (by decide) v hb
def cl_10330 : CNF.NClause := [(500,true),(501,false),(507,true),(513,true),(519,true),(522,true)]
theorem inp_10330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10330 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 21) (closed_mem 12 21) cl_10330 (by decide) v hb
def cl_10331 : CNF.NClause := [(500,false),(501,true),(507,true),(513,true),(519,true),(522,true)]
theorem inp_10331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10331 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 12 21) (closed_mem 12 21) cl_10331 (by decide) v hb
end Percolation.NReplay
