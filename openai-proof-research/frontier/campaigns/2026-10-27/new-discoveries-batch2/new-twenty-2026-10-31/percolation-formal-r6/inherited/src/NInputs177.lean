import NInputs176
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_11153 : CNF.NClause := [(654,false),(659,true),(664,true),(669,true),(674,true),(676,true)]
theorem inp_11153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11153 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 3) (closed_mem 17 3) cl_11153 (by decide) v hb
def cl_11156 : CNF.NClause := [(652,true),(657,true),(662,true),(667,false),(672,true),(676,true)]
theorem inp_11156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11156 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 4) (closed_mem 17 4) cl_11156 (by decide) v hb
def cl_11157 : CNF.NClause := [(652,true),(657,true),(662,false),(667,true),(672,true),(676,true)]
theorem inp_11157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11157 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 4) (closed_mem 17 4) cl_11157 (by decide) v hb
def cl_11158 : CNF.NClause := [(652,true),(657,false),(662,true),(667,true),(672,true),(676,true)]
theorem inp_11158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11158 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 4) (closed_mem 17 4) cl_11158 (by decide) v hb
def cl_11159 : CNF.NClause := [(652,false),(657,true),(662,true),(667,true),(672,true),(676,true)]
theorem inp_11159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11159 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 4) (closed_mem 17 4) cl_11159 (by decide) v hb
def cl_11162 : CNF.NClause := [(671,true),(672,true),(673,true),(674,false),(675,true),(681,true)]
theorem inp_11162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11162 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 5) (closed_mem 17 5) cl_11162 (by decide) v hb
def cl_11164 : CNF.NClause := [(671,true),(672,false),(673,true),(674,true),(675,true),(681,true)]
theorem inp_11164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11164 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 5) (closed_mem 17 5) cl_11164 (by decide) v hb
def cl_11165 : CNF.NClause := [(671,false),(672,true),(673,true),(674,true),(675,true),(681,true)]
theorem inp_11165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11165 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 5) (closed_mem 17 5) cl_11165 (by decide) v hb
def cl_11167 : CNF.NClause := [(655,true),(659,true),(663,true),(667,true),(671,false),(680,true)]
theorem inp_11167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11167 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 6) (closed_mem 17 6) cl_11167 (by decide) v hb
def cl_11168 : CNF.NClause := [(655,true),(659,true),(663,true),(667,false),(671,true),(680,true)]
theorem inp_11168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11168 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 6) (closed_mem 17 6) cl_11168 (by decide) v hb
def cl_11170 : CNF.NClause := [(655,true),(659,false),(663,true),(667,true),(671,true),(680,true)]
theorem inp_11170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11170 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 6) (closed_mem 17 6) cl_11170 (by decide) v hb
def cl_11171 : CNF.NClause := [(655,false),(659,true),(663,true),(667,true),(671,true),(680,true)]
theorem inp_11171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11171 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 6) (closed_mem 17 6) cl_11171 (by decide) v hb
def cl_11173 : CNF.NClause := [(653,true),(660,true),(662,true),(669,true),(671,false),(678,true)]
theorem inp_11173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11173 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 7) (closed_mem 17 7) cl_11173 (by decide) v hb
def cl_11174 : CNF.NClause := [(653,true),(660,true),(662,true),(669,false),(671,true),(678,true)]
theorem inp_11174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11174 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 7) (closed_mem 17 7) cl_11174 (by decide) v hb
def cl_11175 : CNF.NClause := [(653,true),(660,true),(662,false),(669,true),(671,true),(678,true)]
theorem inp_11175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11175 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 7) (closed_mem 17 7) cl_11175 (by decide) v hb
def cl_11176 : CNF.NClause := [(653,true),(660,false),(662,true),(669,true),(671,true),(678,true)]
theorem inp_11176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11176 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 7) (closed_mem 17 7) cl_11176 (by decide) v hb
def cl_11177 : CNF.NClause := [(653,false),(660,true),(662,true),(669,true),(671,true),(678,true)]
theorem inp_11177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11177 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 7) (closed_mem 17 7) cl_11177 (by decide) v hb
def cl_11180 : CNF.NClause := [(654,true),(657,true),(665,true),(668,false),(671,true),(679,true)]
theorem inp_11180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11180 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 8) (closed_mem 17 8) cl_11180 (by decide) v hb
def cl_11184 : CNF.NClause := [(652,true),(658,true),(664,true),(670,true),(671,true),(677,false)]
theorem inp_11184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11184 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 9) (closed_mem 17 9) cl_11184 (by decide) v hb
def cl_11186 : CNF.NClause := [(652,true),(658,true),(664,true),(670,false),(671,true),(677,true)]
theorem inp_11186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11186 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 9) (closed_mem 17 9) cl_11186 (by decide) v hb
def cl_11187 : CNF.NClause := [(652,true),(658,true),(664,false),(670,true),(671,true),(677,true)]
theorem inp_11187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11187 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 9) (closed_mem 17 9) cl_11187 (by decide) v hb
def cl_11188 : CNF.NClause := [(652,true),(658,false),(664,true),(670,true),(671,true),(677,true)]
theorem inp_11188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11188 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 9) (closed_mem 17 9) cl_11188 (by decide) v hb
def cl_11189 : CNF.NClause := [(652,false),(658,true),(664,true),(670,true),(671,true),(677,true)]
theorem inp_11189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11189 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 9) (closed_mem 17 9) cl_11189 (by decide) v hb
def cl_11192 : CNF.NClause := [(661,true),(662,true),(663,true),(664,false),(665,true),(681,true)]
theorem inp_11192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11192 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 10) (closed_mem 17 10) cl_11192 (by decide) v hb
def cl_11193 : CNF.NClause := [(661,true),(662,true),(663,false),(664,true),(665,true),(681,true)]
theorem inp_11193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11193 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 10) (closed_mem 17 10) cl_11193 (by decide) v hb
def cl_11194 : CNF.NClause := [(661,true),(662,false),(663,true),(664,true),(665,true),(681,true)]
theorem inp_11194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11194 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 10) (closed_mem 17 10) cl_11194 (by decide) v hb
def cl_11195 : CNF.NClause := [(661,false),(662,true),(663,true),(664,true),(665,true),(681,true)]
theorem inp_11195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11195 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 10) (closed_mem 17 10) cl_11195 (by decide) v hb
def cl_11197 : CNF.NClause := [(655,true),(658,true),(661,true),(669,true),(672,false),(679,true)]
theorem inp_11197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11197 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 11) (closed_mem 17 11) cl_11197 (by decide) v hb
def cl_11199 : CNF.NClause := [(655,true),(658,true),(661,false),(669,true),(672,true),(679,true)]
theorem inp_11199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11199 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 11) (closed_mem 17 11) cl_11199 (by decide) v hb
def cl_11200 : CNF.NClause := [(655,true),(658,false),(661,true),(669,true),(672,true),(679,true)]
theorem inp_11200 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11200 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 11) (closed_mem 17 11) cl_11200 (by decide) v hb
def cl_11201 : CNF.NClause := [(655,false),(658,true),(661,true),(669,true),(672,true),(679,true)]
theorem inp_11201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11201 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 11) (closed_mem 17 11) cl_11201 (by decide) v hb
def cl_11202 : CNF.NClause := [(653,true),(657,true),(661,true),(670,true),(674,true),(680,false)]
theorem inp_11202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11202 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 12) (closed_mem 17 12) cl_11202 (by decide) v hb
def cl_11204 : CNF.NClause := [(653,true),(657,true),(661,true),(670,false),(674,true),(680,true)]
theorem inp_11204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11204 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_11204 v hb
def cl_11207 : CNF.NClause := [(653,false),(657,true),(661,true),(670,true),(674,true),(680,true)]
theorem inp_11207 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11207 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_11207 v hb
def cl_11209 : CNF.NClause := [(654,true),(660,true),(661,true),(667,true),(673,false),(677,true)]
theorem inp_11209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11209 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 13) (closed_mem 17 13) cl_11209 (by decide) v hb
def cl_11211 : CNF.NClause := [(654,true),(660,true),(661,false),(667,true),(673,true),(677,true)]
theorem inp_11211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11211 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 13) (closed_mem 17 13) cl_11211 (by decide) v hb
def cl_11212 : CNF.NClause := [(654,true),(660,false),(661,true),(667,true),(673,true),(677,true)]
theorem inp_11212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11212 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 13) (closed_mem 17 13) cl_11212 (by decide) v hb
def cl_11216 : CNF.NClause := [(652,true),(659,true),(661,true),(668,false),(675,true),(678,true)]
theorem inp_11216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11216 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 14) (closed_mem 17 14) cl_11216 (by decide) v hb
def cl_11223 : CNF.NClause := [(666,true),(667,true),(668,false),(669,true),(670,true),(681,true)]
theorem inp_11223 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11223 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 15) (closed_mem 17 15) cl_11223 (by decide) v hb
def cl_11228 : CNF.NClause := [(655,true),(657,true),(664,true),(666,false),(673,true),(678,true)]
theorem inp_11228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11228 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 16) (closed_mem 17 16) cl_11228 (by decide) v hb
def cl_11229 : CNF.NClause := [(655,true),(657,true),(664,false),(666,true),(673,true),(678,true)]
theorem inp_11229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11229 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 16) (closed_mem 17 16) cl_11229 (by decide) v hb
def cl_11230 : CNF.NClause := [(655,true),(657,false),(664,true),(666,true),(673,true),(678,true)]
theorem inp_11230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11230 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 16) (closed_mem 17 16) cl_11230 (by decide) v hb
def cl_11231 : CNF.NClause := [(655,false),(657,true),(664,true),(666,true),(673,true),(678,true)]
theorem inp_11231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11231 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 16) (closed_mem 17 16) cl_11231 (by decide) v hb
def cl_11232 : CNF.NClause := [(653,true),(659,true),(665,true),(666,true),(672,true),(677,false)]
theorem inp_11232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11232 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 17) (closed_mem 17 17) cl_11232 (by decide) v hb
def cl_11233 : CNF.NClause := [(653,true),(659,true),(665,true),(666,true),(672,false),(677,true)]
theorem inp_11233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11233 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 17) (closed_mem 17 17) cl_11233 (by decide) v hb
def cl_11235 : CNF.NClause := [(653,true),(659,true),(665,false),(666,true),(672,true),(677,true)]
theorem inp_11235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11235 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 17) (closed_mem 17 17) cl_11235 (by decide) v hb
def cl_11237 : CNF.NClause := [(653,false),(659,true),(665,true),(666,true),(672,true),(677,true)]
theorem inp_11237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11237 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 17) (closed_mem 17 17) cl_11237 (by decide) v hb
def cl_11239 : CNF.NClause := [(654,true),(658,true),(662,true),(666,true),(675,false),(680,true)]
theorem inp_11239 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11239 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 18) (closed_mem 17 18) cl_11239 (by decide) v hb
def cl_11241 : CNF.NClause := [(654,true),(658,true),(662,false),(666,true),(675,true),(680,true)]
theorem inp_11241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11241 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 18) (closed_mem 17 18) cl_11241 (by decide) v hb
def cl_11242 : CNF.NClause := [(654,true),(658,false),(662,true),(666,true),(675,true),(680,true)]
theorem inp_11242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11242 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 17 18) (closed_mem 17 18) cl_11242 (by decide) v hb
end Percolation.NReplay
