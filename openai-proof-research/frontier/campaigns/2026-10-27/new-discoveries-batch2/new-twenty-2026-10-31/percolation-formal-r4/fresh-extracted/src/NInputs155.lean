import NInputs154
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_9235 : CNF.NClause := [(310,true),(311,true),(312,true),(313,true),(314,false),(340,true)]
theorem inp_9235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9235 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 25) (closed_mem 6 25) cl_9235 (by decide) v hb
def cl_9236 : CNF.NClause := [(310,true),(311,true),(312,true),(313,false),(314,true),(340,true)]
theorem inp_9236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9236 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 25) (closed_mem 6 25) cl_9236 (by decide) v hb
def cl_9237 : CNF.NClause := [(310,true),(311,true),(312,false),(313,true),(314,true),(340,true)]
theorem inp_9237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9237 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 25) (closed_mem 6 25) cl_9237 (by decide) v hb
def cl_9238 : CNF.NClause := [(310,true),(311,false),(312,true),(313,true),(314,true),(340,true)]
theorem inp_9238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9238 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 25) (closed_mem 6 25) cl_9238 (by decide) v hb
def cl_9240 : CNF.NClause := [(310,true),(319,true),(323,true),(327,true),(331,true),(339,false)]
theorem inp_9240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9240 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 26) (closed_mem 6 26) cl_9240 (by decide) v hb
def cl_9241 : CNF.NClause := [(310,true),(319,true),(323,true),(327,true),(331,false),(339,true)]
theorem inp_9241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9241 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 26) (closed_mem 6 26) cl_9241 (by decide) v hb
def cl_9242 : CNF.NClause := [(310,true),(319,true),(323,true),(327,false),(331,true),(339,true)]
theorem inp_9242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9242 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 26) (closed_mem 6 26) cl_9242 (by decide) v hb
def cl_9243 : CNF.NClause := [(310,true),(319,true),(323,false),(327,true),(331,true),(339,true)]
theorem inp_9243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9243 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 26) (closed_mem 6 26) cl_9243 (by decide) v hb
def cl_9244 : CNF.NClause := [(310,true),(319,false),(323,true),(327,true),(331,true),(339,true)]
theorem inp_9244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9244 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 26) (closed_mem 6 26) cl_9244 (by decide) v hb
def cl_9246 : CNF.NClause := [(310,true),(317,true),(324,true),(326,true),(333,true),(337,false)]
theorem inp_9246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9246 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 27) (closed_mem 6 27) cl_9246 (by decide) v hb
def cl_9247 : CNF.NClause := [(310,true),(317,true),(324,true),(326,true),(333,false),(337,true)]
theorem inp_9247 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9247 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 27) (closed_mem 6 27) cl_9247 (by decide) v hb
def cl_9248 : CNF.NClause := [(310,true),(317,true),(324,true),(326,false),(333,true),(337,true)]
theorem inp_9248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9248 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 27) (closed_mem 6 27) cl_9248 (by decide) v hb
def cl_9249 : CNF.NClause := [(310,true),(317,true),(324,false),(326,true),(333,true),(337,true)]
theorem inp_9249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9249 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 27) (closed_mem 6 27) cl_9249 (by decide) v hb
def cl_9250 : CNF.NClause := [(310,true),(317,false),(324,true),(326,true),(333,true),(337,true)]
theorem inp_9250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9250 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 27) (closed_mem 6 27) cl_9250 (by decide) v hb
def cl_9252 : CNF.NClause := [(310,true),(318,true),(321,true),(329,true),(332,true),(338,false)]
theorem inp_9252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9252 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 28) (closed_mem 6 28) cl_9252 (by decide) v hb
def cl_9253 : CNF.NClause := [(310,true),(318,true),(321,true),(329,true),(332,false),(338,true)]
theorem inp_9253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9253 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 28) (closed_mem 6 28) cl_9253 (by decide) v hb
def cl_9254 : CNF.NClause := [(310,true),(318,true),(321,true),(329,false),(332,true),(338,true)]
theorem inp_9254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9254 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 28) (closed_mem 6 28) cl_9254 (by decide) v hb
def cl_9255 : CNF.NClause := [(310,true),(318,true),(321,false),(329,true),(332,true),(338,true)]
theorem inp_9255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9255 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 28) (closed_mem 6 28) cl_9255 (by decide) v hb
def cl_9256 : CNF.NClause := [(310,true),(318,false),(321,true),(329,true),(332,true),(338,true)]
theorem inp_9256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9256 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 28) (closed_mem 6 28) cl_9256 (by decide) v hb
def cl_9262 : CNF.NClause := [(310,true),(316,false),(322,true),(328,true),(334,true),(336,true)]
theorem inp_9262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9262 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 29) (closed_mem 6 29) cl_9262 (by decide) v hb
def cl_9265 : CNF.NClause := [(310,true),(315,true),(320,true),(325,true),(330,false),(335,true)]
theorem inp_9265 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9265 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 30) (closed_mem 6 30) cl_9265 (by decide) v hb
def cl_9267 : CNF.NClause := [(310,true),(315,true),(320,false),(325,true),(330,true),(335,true)]
theorem inp_9267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9267 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 30) (closed_mem 6 30) cl_9267 (by decide) v hb
def cl_9268 : CNF.NClause := [(310,true),(315,false),(320,true),(325,true),(330,true),(335,true)]
theorem inp_9268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9268 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 30) (closed_mem 6 30) cl_9268 (by decide) v hb
def cl_9271 : CNF.NClause := [(366,true),(367,true),(368,true),(369,true),(370,false),(371,true)]
theorem inp_9271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9271 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 0) (closed_mem 7 0) cl_9271 (by decide) v hb
def cl_9272 : CNF.NClause := [(366,true),(367,true),(368,true),(369,false),(370,true),(371,true)]
theorem inp_9272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9272 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9272 v hb
def cl_9273 : CNF.NClause := [(366,true),(367,true),(368,false),(369,true),(370,true),(371,true)]
theorem inp_9273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9273 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 0) (closed_mem 7 0) cl_9273 (by decide) v hb
def cl_9274 : CNF.NClause := [(366,true),(367,false),(368,true),(369,true),(370,true),(371,true)]
theorem inp_9274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9274 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 0) (closed_mem 7 0) cl_9274 (by decide) v hb
def cl_9277 : CNF.NClause := [(345,true),(350,true),(355,true),(360,true),(365,false),(366,true)]
theorem inp_9277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9277 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 1) (closed_mem 7 1) cl_9277 (by decide) v hb
def cl_9279 : CNF.NClause := [(345,true),(350,true),(355,false),(360,true),(365,true),(366,true)]
theorem inp_9279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9279 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9279 v hb
def cl_9280 : CNF.NClause := [(345,true),(350,false),(355,true),(360,true),(365,true),(366,true)]
theorem inp_9280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9280 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 1) (closed_mem 7 1) cl_9280 (by decide) v hb
def cl_9281 : CNF.NClause := [(345,false),(350,true),(355,true),(360,true),(365,true),(366,true)]
theorem inp_9281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9281 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 1) (closed_mem 7 1) cl_9281 (by decide) v hb
def cl_9286 : CNF.NClause := [(343,true),(348,false),(353,true),(358,true),(363,true),(366,true)]
theorem inp_9286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9286 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 2) (closed_mem 7 2) cl_9286 (by decide) v hb
def cl_9289 : CNF.NClause := [(344,true),(349,true),(354,true),(359,true),(364,false),(366,true)]
theorem inp_9289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9289 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 3) (closed_mem 7 3) cl_9289 (by decide) v hb
def cl_9290 : CNF.NClause := [(344,true),(349,true),(354,true),(359,false),(364,true),(366,true)]
theorem inp_9290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9290 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 3) (closed_mem 7 3) cl_9290 (by decide) v hb
def cl_9292 : CNF.NClause := [(344,true),(349,false),(354,true),(359,true),(364,true),(366,true)]
theorem inp_9292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9292 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 3) (closed_mem 7 3) cl_9292 (by decide) v hb
def cl_9293 : CNF.NClause := [(344,false),(349,true),(354,true),(359,true),(364,true),(366,true)]
theorem inp_9293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9293 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 3) (closed_mem 7 3) cl_9293 (by decide) v hb
def cl_9295 : CNF.NClause := [(342,true),(347,true),(352,true),(357,true),(362,false),(366,true)]
theorem inp_9295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9295 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 4) (closed_mem 7 4) cl_9295 (by decide) v hb
def cl_9296 : CNF.NClause := [(342,true),(347,true),(352,true),(357,false),(362,true),(366,true)]
theorem inp_9296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9296 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 4) (closed_mem 7 4) cl_9296 (by decide) v hb
def cl_9297 : CNF.NClause := [(342,true),(347,true),(352,false),(357,true),(362,true),(366,true)]
theorem inp_9297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9297 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 4) (closed_mem 7 4) cl_9297 (by decide) v hb
def cl_9298 : CNF.NClause := [(342,true),(347,false),(352,true),(357,true),(362,true),(366,true)]
theorem inp_9298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9298 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 4) (closed_mem 7 4) cl_9298 (by decide) v hb
def cl_9299 : CNF.NClause := [(342,false),(347,true),(352,true),(357,true),(362,true),(366,true)]
theorem inp_9299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9299 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 4) (closed_mem 7 4) cl_9299 (by decide) v hb
def cl_9301 : CNF.NClause := [(361,true),(362,true),(363,true),(364,true),(365,false),(371,true)]
theorem inp_9301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9301 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 5) (closed_mem 7 5) cl_9301 (by decide) v hb
def cl_9302 : CNF.NClause := [(361,true),(362,true),(363,true),(364,false),(365,true),(371,true)]
theorem inp_9302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9302 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 5) (closed_mem 7 5) cl_9302 (by decide) v hb
def cl_9303 : CNF.NClause := [(361,true),(362,true),(363,false),(364,true),(365,true),(371,true)]
theorem inp_9303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9303 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 5) (closed_mem 7 5) cl_9303 (by decide) v hb
def cl_9304 : CNF.NClause := [(361,true),(362,false),(363,true),(364,true),(365,true),(371,true)]
theorem inp_9304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9304 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 5) (closed_mem 7 5) cl_9304 (by decide) v hb
def cl_9305 : CNF.NClause := [(361,false),(362,true),(363,true),(364,true),(365,true),(371,true)]
theorem inp_9305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9305 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9305 v hb
def cl_9307 : CNF.NClause := [(345,true),(349,true),(353,true),(357,true),(361,false),(370,true)]
theorem inp_9307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9307 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 6) (closed_mem 7 6) cl_9307 (by decide) v hb
def cl_9309 : CNF.NClause := [(345,true),(349,true),(353,false),(357,true),(361,true),(370,true)]
theorem inp_9309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9309 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 6) (closed_mem 7 6) cl_9309 (by decide) v hb
def cl_9310 : CNF.NClause := [(345,true),(349,false),(353,true),(357,true),(361,true),(370,true)]
theorem inp_9310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9310 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 7 6) (closed_mem 7 6) cl_9310 (by decide) v hb
def cl_9311 : CNF.NClause := [(345,false),(349,true),(353,true),(357,true),(361,true),(370,true)]
theorem inp_9311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9311 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9311 v hb
end Percolation.NReplay
