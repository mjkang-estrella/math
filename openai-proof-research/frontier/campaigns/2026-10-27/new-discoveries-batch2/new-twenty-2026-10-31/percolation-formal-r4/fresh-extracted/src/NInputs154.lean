import NInputs153
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_9155 : CNF.NClause := [(314,false),(317,true),(320,true),(328,true),(331,true),(338,true)]
theorem inp_9155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9155 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 11) (closed_mem 6 11) cl_9155 (by decide) v hb
def cl_9160 : CNF.NClause := [(312,true),(316,false),(320,true),(329,true),(333,true),(339,true)]
theorem inp_9160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9160 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 12) (closed_mem 6 12) cl_9160 (by decide) v hb
def cl_9162 : CNF.NClause := [(313,true),(319,true),(320,true),(326,true),(332,true),(336,false)]
theorem inp_9162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9162 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 13) (closed_mem 6 13) cl_9162 (by decide) v hb
def cl_9163 : CNF.NClause := [(313,true),(319,true),(320,true),(326,true),(332,false),(336,true)]
theorem inp_9163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9163 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 13) (closed_mem 6 13) cl_9163 (by decide) v hb
def cl_9165 : CNF.NClause := [(313,true),(319,true),(320,false),(326,true),(332,true),(336,true)]
theorem inp_9165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9165 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 13) (closed_mem 6 13) cl_9165 (by decide) v hb
def cl_9166 : CNF.NClause := [(313,true),(319,false),(320,true),(326,true),(332,true),(336,true)]
theorem inp_9166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9166 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 13) (closed_mem 6 13) cl_9166 (by decide) v hb
def cl_9167 : CNF.NClause := [(313,false),(319,true),(320,true),(326,true),(332,true),(336,true)]
theorem inp_9167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9167 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 13) (closed_mem 6 13) cl_9167 (by decide) v hb
def cl_9169 : CNF.NClause := [(311,true),(318,true),(320,true),(327,true),(334,false),(337,true)]
theorem inp_9169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9169 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 14) (closed_mem 6 14) cl_9169 (by decide) v hb
def cl_9170 : CNF.NClause := [(311,true),(318,true),(320,true),(327,false),(334,true),(337,true)]
theorem inp_9170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9170 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 14) (closed_mem 6 14) cl_9170 (by decide) v hb
def cl_9171 : CNF.NClause := [(311,true),(318,true),(320,false),(327,true),(334,true),(337,true)]
theorem inp_9171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9171 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 14) (closed_mem 6 14) cl_9171 (by decide) v hb
def cl_9172 : CNF.NClause := [(311,true),(318,false),(320,true),(327,true),(334,true),(337,true)]
theorem inp_9172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9172 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 14) (closed_mem 6 14) cl_9172 (by decide) v hb
def cl_9175 : CNF.NClause := [(325,true),(326,true),(327,true),(328,true),(329,false),(340,true)]
theorem inp_9175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9175 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 15) (closed_mem 6 15) cl_9175 (by decide) v hb
def cl_9176 : CNF.NClause := [(325,true),(326,true),(327,true),(328,false),(329,true),(340,true)]
theorem inp_9176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9176 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 15) (closed_mem 6 15) cl_9176 (by decide) v hb
def cl_9177 : CNF.NClause := [(325,true),(326,true),(327,false),(328,true),(329,true),(340,true)]
theorem inp_9177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9177 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 15) (closed_mem 6 15) cl_9177 (by decide) v hb
def cl_9178 : CNF.NClause := [(325,true),(326,false),(327,true),(328,true),(329,true),(340,true)]
theorem inp_9178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9178 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 15) (closed_mem 6 15) cl_9178 (by decide) v hb
def cl_9179 : CNF.NClause := [(325,false),(326,true),(327,true),(328,true),(329,true),(340,true)]
theorem inp_9179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9179 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 15) (closed_mem 6 15) cl_9179 (by decide) v hb
def cl_9184 : CNF.NClause := [(314,true),(316,false),(323,true),(325,true),(332,true),(337,true)]
theorem inp_9184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9184 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 16) (closed_mem 6 16) cl_9184 (by decide) v hb
def cl_9186 : CNF.NClause := [(312,true),(318,true),(324,true),(325,true),(331,true),(336,false)]
theorem inp_9186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9186 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 17) (closed_mem 6 17) cl_9186 (by decide) v hb
def cl_9187 : CNF.NClause := [(312,true),(318,true),(324,true),(325,true),(331,false),(336,true)]
theorem inp_9187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9187 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 17) (closed_mem 6 17) cl_9187 (by decide) v hb
def cl_9188 : CNF.NClause := [(312,true),(318,true),(324,true),(325,false),(331,true),(336,true)]
theorem inp_9188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9188 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 17) (closed_mem 6 17) cl_9188 (by decide) v hb
def cl_9189 : CNF.NClause := [(312,true),(318,true),(324,false),(325,true),(331,true),(336,true)]
theorem inp_9189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9189 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 17) (closed_mem 6 17) cl_9189 (by decide) v hb
def cl_9190 : CNF.NClause := [(312,true),(318,false),(324,true),(325,true),(331,true),(336,true)]
theorem inp_9190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9190 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 17) (closed_mem 6 17) cl_9190 (by decide) v hb
def cl_9191 : CNF.NClause := [(312,false),(318,true),(324,true),(325,true),(331,true),(336,true)]
theorem inp_9191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9191 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 17) (closed_mem 6 17) cl_9191 (by decide) v hb
def cl_9192 : CNF.NClause := [(313,true),(317,true),(321,true),(325,true),(334,true),(339,false)]
theorem inp_9192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9192 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 18) (closed_mem 6 18) cl_9192 (by decide) v hb
def cl_9193 : CNF.NClause := [(313,true),(317,true),(321,true),(325,true),(334,false),(339,true)]
theorem inp_9193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9193 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 18) (closed_mem 6 18) cl_9193 (by decide) v hb
def cl_9194 : CNF.NClause := [(313,true),(317,true),(321,true),(325,false),(334,true),(339,true)]
theorem inp_9194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9194 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 18) (closed_mem 6 18) cl_9194 (by decide) v hb
def cl_9195 : CNF.NClause := [(313,true),(317,true),(321,false),(325,true),(334,true),(339,true)]
theorem inp_9195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9195 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 18) (closed_mem 6 18) cl_9195 (by decide) v hb
def cl_9198 : CNF.NClause := [(311,true),(319,true),(322,true),(325,true),(333,true),(338,false)]
theorem inp_9198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9198 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 19) (closed_mem 6 19) cl_9198 (by decide) v hb
def cl_9199 : CNF.NClause := [(311,true),(319,true),(322,true),(325,true),(333,false),(338,true)]
theorem inp_9199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9199 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 19) (closed_mem 6 19) cl_9199 (by decide) v hb
def cl_9201 : CNF.NClause := [(311,true),(319,true),(322,false),(325,true),(333,true),(338,true)]
theorem inp_9201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9201 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 19) (closed_mem 6 19) cl_9201 (by decide) v hb
def cl_9202 : CNF.NClause := [(311,true),(319,false),(322,true),(325,true),(333,true),(338,true)]
theorem inp_9202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9202 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 19) (closed_mem 6 19) cl_9202 (by decide) v hb
def cl_9203 : CNF.NClause := [(311,false),(319,true),(322,true),(325,true),(333,true),(338,true)]
theorem inp_9203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9203 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 19) (closed_mem 6 19) cl_9203 (by decide) v hb
def cl_9208 : CNF.NClause := [(315,true),(316,false),(317,true),(318,true),(319,true),(340,true)]
theorem inp_9208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9208 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 20) (closed_mem 6 20) cl_9208 (by decide) v hb
def cl_9211 : CNF.NClause := [(314,true),(315,true),(321,true),(327,true),(333,false),(336,true)]
theorem inp_9211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9211 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 21) (closed_mem 6 21) cl_9211 (by decide) v hb
def cl_9212 : CNF.NClause := [(314,true),(315,true),(321,true),(327,false),(333,true),(336,true)]
theorem inp_9212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9212 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 21) (closed_mem 6 21) cl_9212 (by decide) v hb
def cl_9214 : CNF.NClause := [(314,true),(315,false),(321,true),(327,true),(333,true),(336,true)]
theorem inp_9214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9214 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 21) (closed_mem 6 21) cl_9214 (by decide) v hb
def cl_9216 : CNF.NClause := [(312,true),(315,true),(323,true),(326,true),(334,true),(338,false)]
theorem inp_9216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9216 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 22) (closed_mem 6 22) cl_9216 (by decide) v hb
def cl_9217 : CNF.NClause := [(312,true),(315,true),(323,true),(326,true),(334,false),(338,true)]
theorem inp_9217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9217 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 22) (closed_mem 6 22) cl_9217 (by decide) v hb
def cl_9218 : CNF.NClause := [(312,true),(315,true),(323,true),(326,false),(334,true),(338,true)]
theorem inp_9218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9218 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 22) (closed_mem 6 22) cl_9218 (by decide) v hb
def cl_9219 : CNF.NClause := [(312,true),(315,true),(323,false),(326,true),(334,true),(338,true)]
theorem inp_9219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9219 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 22) (closed_mem 6 22) cl_9219 (by decide) v hb
def cl_9220 : CNF.NClause := [(312,true),(315,false),(323,true),(326,true),(334,true),(338,true)]
theorem inp_9220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9220 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 22) (closed_mem 6 22) cl_9220 (by decide) v hb
def cl_9221 : CNF.NClause := [(312,false),(315,true),(323,true),(326,true),(334,true),(338,true)]
theorem inp_9221 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9221 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 22) (closed_mem 6 22) cl_9221 (by decide) v hb
def cl_9223 : CNF.NClause := [(313,true),(315,true),(322,true),(329,true),(331,false),(337,true)]
theorem inp_9223 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9223 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 23) (closed_mem 6 23) cl_9223 (by decide) v hb
def cl_9225 : CNF.NClause := [(313,true),(315,true),(322,false),(329,true),(331,true),(337,true)]
theorem inp_9225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9225 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 23) (closed_mem 6 23) cl_9225 (by decide) v hb
def cl_9226 : CNF.NClause := [(313,true),(315,false),(322,true),(329,true),(331,true),(337,true)]
theorem inp_9226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9226 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 23) (closed_mem 6 23) cl_9226 (by decide) v hb
def cl_9228 : CNF.NClause := [(311,true),(315,true),(324,true),(328,true),(332,true),(339,false)]
theorem inp_9228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9228 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 24) (closed_mem 6 24) cl_9228 (by decide) v hb
def cl_9230 : CNF.NClause := [(311,true),(315,true),(324,true),(328,false),(332,true),(339,true)]
theorem inp_9230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9230 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 24) (closed_mem 6 24) cl_9230 (by decide) v hb
def cl_9231 : CNF.NClause := [(311,true),(315,true),(324,false),(328,true),(332,true),(339,true)]
theorem inp_9231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9231 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 24) (closed_mem 6 24) cl_9231 (by decide) v hb
def cl_9232 : CNF.NClause := [(311,true),(315,false),(324,true),(328,true),(332,true),(339,true)]
theorem inp_9232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9232 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 24) (closed_mem 6 24) cl_9232 (by decide) v hb
def cl_9233 : CNF.NClause := [(311,false),(315,true),(324,true),(328,true),(332,true),(339,true)]
theorem inp_9233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9233 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 24) (closed_mem 6 24) cl_9233 (by decide) v hb
end Percolation.NReplay
