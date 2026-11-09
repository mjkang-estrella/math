import NInputs142
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_8162 : CNF.NClause := [(159,true),(164,true),(169,true),(174,false),(179,true),(180,true)]
theorem inp_8162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8162 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 1) (closed_mem 1 1) cl_8162 (by decide) v hb
def cl_8163 : CNF.NClause := [(159,true),(164,true),(169,false),(174,true),(179,true),(180,true)]
theorem inp_8163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8163 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 1) (closed_mem 1 1) cl_8163 (by decide) v hb
def cl_8165 : CNF.NClause := [(159,false),(164,true),(169,true),(174,true),(179,true),(180,true)]
theorem inp_8165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8165 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 1) (closed_mem 1 1) cl_8165 (by decide) v hb
def cl_8167 : CNF.NClause := [(157,true),(162,true),(167,true),(172,true),(177,false),(180,true)]
theorem inp_8167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8167 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 2) (closed_mem 1 2) cl_8167 (by decide) v hb
def cl_8168 : CNF.NClause := [(157,true),(162,true),(167,true),(172,false),(177,true),(180,true)]
theorem inp_8168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8168 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 2) (closed_mem 1 2) cl_8168 (by decide) v hb
def cl_8169 : CNF.NClause := [(157,true),(162,true),(167,false),(172,true),(177,true),(180,true)]
theorem inp_8169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8169 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 2) (closed_mem 1 2) cl_8169 (by decide) v hb
def cl_8171 : CNF.NClause := [(157,false),(162,true),(167,true),(172,true),(177,true),(180,true)]
theorem inp_8171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8171 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 2) (closed_mem 1 2) cl_8171 (by decide) v hb
def cl_8175 : CNF.NClause := [(158,true),(163,true),(168,false),(173,true),(178,true),(180,true)]
theorem inp_8175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8175 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 3) (closed_mem 1 3) cl_8175 (by decide) v hb
def cl_8176 : CNF.NClause := [(158,true),(163,false),(168,true),(173,true),(178,true),(180,true)]
theorem inp_8176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8176 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 3) (closed_mem 1 3) cl_8176 (by decide) v hb
def cl_8177 : CNF.NClause := [(158,false),(163,true),(168,true),(173,true),(178,true),(180,true)]
theorem inp_8177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8177 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 3) (closed_mem 1 3) cl_8177 (by decide) v hb
def cl_8183 : CNF.NClause := [(156,false),(161,true),(166,true),(171,true),(176,true),(180,true)]
theorem inp_8183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8183 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 4) (closed_mem 1 4) cl_8183 (by decide) v hb
def cl_8185 : CNF.NClause := [(175,true),(176,true),(177,true),(178,true),(179,false),(185,true)]
theorem inp_8185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8185 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 5) (closed_mem 1 5) cl_8185 (by decide) v hb
def cl_8186 : CNF.NClause := [(175,true),(176,true),(177,true),(178,false),(179,true),(185,true)]
theorem inp_8186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8186 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 5) (closed_mem 1 5) cl_8186 (by decide) v hb
def cl_8188 : CNF.NClause := [(175,true),(176,false),(177,true),(178,true),(179,true),(185,true)]
theorem inp_8188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8188 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 5) (closed_mem 1 5) cl_8188 (by decide) v hb
def cl_8189 : CNF.NClause := [(175,false),(176,true),(177,true),(178,true),(179,true),(185,true)]
theorem inp_8189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8189 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 5) (closed_mem 1 5) cl_8189 (by decide) v hb
def cl_8190 : CNF.NClause := [(159,true),(163,true),(167,true),(171,true),(175,true),(184,false)]
theorem inp_8190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8190 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 6) (closed_mem 1 6) cl_8190 (by decide) v hb
def cl_8191 : CNF.NClause := [(159,true),(163,true),(167,true),(171,true),(175,false),(184,true)]
theorem inp_8191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8191 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 6) (closed_mem 1 6) cl_8191 (by decide) v hb
def cl_8194 : CNF.NClause := [(159,true),(163,false),(167,true),(171,true),(175,true),(184,true)]
theorem inp_8194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8194 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 6) (closed_mem 1 6) cl_8194 (by decide) v hb
def cl_8197 : CNF.NClause := [(157,true),(164,true),(166,true),(173,true),(175,false),(182,true)]
theorem inp_8197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8197 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 7) (closed_mem 1 7) cl_8197 (by decide) v hb
def cl_8198 : CNF.NClause := [(157,true),(164,true),(166,true),(173,false),(175,true),(182,true)]
theorem inp_8198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8198 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 7) (closed_mem 1 7) cl_8198 (by decide) v hb
def cl_8199 : CNF.NClause := [(157,true),(164,true),(166,false),(173,true),(175,true),(182,true)]
theorem inp_8199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8199 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 7) (closed_mem 1 7) cl_8199 (by decide) v hb
def cl_8204 : CNF.NClause := [(158,true),(161,true),(169,true),(172,false),(175,true),(183,true)]
theorem inp_8204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8204 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 8) (closed_mem 1 8) cl_8204 (by decide) v hb
def cl_8213 : CNF.NClause := [(156,false),(162,true),(168,true),(174,true),(175,true),(181,true)]
theorem inp_8213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8213 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 9) (closed_mem 1 9) cl_8213 (by decide) v hb
def cl_8215 : CNF.NClause := [(165,true),(166,true),(167,true),(168,true),(169,false),(185,true)]
theorem inp_8215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8215 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 10) (closed_mem 1 10) cl_8215 (by decide) v hb
def cl_8216 : CNF.NClause := [(165,true),(166,true),(167,true),(168,false),(169,true),(185,true)]
theorem inp_8216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8216 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 10) (closed_mem 1 10) cl_8216 (by decide) v hb
def cl_8218 : CNF.NClause := [(165,true),(166,false),(167,true),(168,true),(169,true),(185,true)]
theorem inp_8218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8218 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 10) (closed_mem 1 10) cl_8218 (by decide) v hb
def cl_8219 : CNF.NClause := [(165,false),(166,true),(167,true),(168,true),(169,true),(185,true)]
theorem inp_8219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8219 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 10) (closed_mem 1 10) cl_8219 (by decide) v hb
def cl_8222 : CNF.NClause := [(159,true),(162,true),(165,true),(173,false),(176,true),(183,true)]
theorem inp_8222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8222 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 11) (closed_mem 1 11) cl_8222 (by decide) v hb
def cl_8225 : CNF.NClause := [(159,false),(162,true),(165,true),(173,true),(176,true),(183,true)]
theorem inp_8225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8225 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 11) (closed_mem 1 11) cl_8225 (by decide) v hb
def cl_8227 : CNF.NClause := [(157,true),(161,true),(165,true),(174,true),(178,false),(184,true)]
theorem inp_8227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8227 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 12) (closed_mem 1 12) cl_8227 (by decide) v hb
def cl_8237 : CNF.NClause := [(158,false),(164,true),(165,true),(171,true),(177,true),(181,true)]
theorem inp_8237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8237 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 13) (closed_mem 1 13) cl_8237 (by decide) v hb
def cl_8243 : CNF.NClause := [(156,false),(163,true),(165,true),(172,true),(179,true),(182,true)]
theorem inp_8243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8243 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 14) (closed_mem 1 14) cl_8243 (by decide) v hb
def cl_8245 : CNF.NClause := [(170,true),(171,true),(172,true),(173,true),(174,false),(185,true)]
theorem inp_8245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8245 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 15) (closed_mem 1 15) cl_8245 (by decide) v hb
def cl_8248 : CNF.NClause := [(170,true),(171,false),(172,true),(173,true),(174,true),(185,true)]
theorem inp_8248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8248 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 15) (closed_mem 1 15) cl_8248 (by decide) v hb
def cl_8249 : CNF.NClause := [(170,false),(171,true),(172,true),(173,true),(174,true),(185,true)]
theorem inp_8249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8249 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 15) (closed_mem 1 15) cl_8249 (by decide) v hb
def cl_8250 : CNF.NClause := [(159,true),(161,true),(168,true),(170,true),(177,true),(182,false)]
theorem inp_8250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8250 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 16) (closed_mem 1 16) cl_8250 (by decide) v hb
def cl_8251 : CNF.NClause := [(159,true),(161,true),(168,true),(170,true),(177,false),(182,true)]
theorem inp_8251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8251 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 16) (closed_mem 1 16) cl_8251 (by decide) v hb
def cl_8252 : CNF.NClause := [(159,true),(161,true),(168,true),(170,false),(177,true),(182,true)]
theorem inp_8252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8252 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 16) (closed_mem 1 16) cl_8252 (by decide) v hb
def cl_8253 : CNF.NClause := [(159,true),(161,true),(168,false),(170,true),(177,true),(182,true)]
theorem inp_8253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8253 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 16) (closed_mem 1 16) cl_8253 (by decide) v hb
def cl_8255 : CNF.NClause := [(159,false),(161,true),(168,true),(170,true),(177,true),(182,true)]
theorem inp_8255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8255 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 16) (closed_mem 1 16) cl_8255 (by decide) v hb
def cl_8258 : CNF.NClause := [(157,true),(163,true),(169,true),(170,false),(176,true),(181,true)]
theorem inp_8258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8258 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 17) (closed_mem 1 17) cl_8258 (by decide) v hb
def cl_8260 : CNF.NClause := [(157,true),(163,false),(169,true),(170,true),(176,true),(181,true)]
theorem inp_8260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8260 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 17) (closed_mem 1 17) cl_8260 (by decide) v hb
def cl_8264 : CNF.NClause := [(158,true),(162,true),(166,true),(170,false),(179,true),(184,true)]
theorem inp_8264 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8264 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 18) (closed_mem 1 18) cl_8264 (by decide) v hb
def cl_8267 : CNF.NClause := [(158,false),(162,true),(166,true),(170,true),(179,true),(184,true)]
theorem inp_8267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8267 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 18) (closed_mem 1 18) cl_8267 (by decide) v hb
def cl_8273 : CNF.NClause := [(156,false),(164,true),(167,true),(170,true),(178,true),(183,true)]
theorem inp_8273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8273 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 19) (closed_mem 1 19) cl_8273 (by decide) v hb
def cl_8278 : CNF.NClause := [(160,true),(161,false),(162,true),(163,true),(164,true),(185,true)]
theorem inp_8278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8278 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 20) (closed_mem 1 20) cl_8278 (by decide) v hb
def cl_8279 : CNF.NClause := [(160,false),(161,true),(162,true),(163,true),(164,true),(185,true)]
theorem inp_8279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8279 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 20) (closed_mem 1 20) cl_8279 (by decide) v hb
def cl_8280 : CNF.NClause := [(159,true),(160,true),(166,true),(172,true),(178,true),(181,false)]
theorem inp_8280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8280 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 21) (closed_mem 1 21) cl_8280 (by decide) v hb
def cl_8281 : CNF.NClause := [(159,true),(160,true),(166,true),(172,true),(178,false),(181,true)]
theorem inp_8281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8281 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 21) (closed_mem 1 21) cl_8281 (by decide) v hb
def cl_8282 : CNF.NClause := [(159,true),(160,true),(166,true),(172,false),(178,true),(181,true)]
theorem inp_8282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8282 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 1 21) (closed_mem 1 21) cl_8282 (by decide) v hb
end Percolation.NReplay
