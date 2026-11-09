import NInputs174
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_10955 : CNF.NClause := [(624,false),(629,true),(634,true),(639,true),(644,true),(645,true)]
theorem inp_10955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10955 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 1) (closed_mem 16 1) cl_10955 (by decide) v hb
def cl_10958 : CNF.NClause := [(622,true),(627,true),(632,true),(637,false),(642,true),(645,true)]
theorem inp_10958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10958 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 2) (closed_mem 16 2) cl_10958 (by decide) v hb
def cl_10960 : CNF.NClause := [(622,true),(627,false),(632,true),(637,true),(642,true),(645,true)]
theorem inp_10960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10960 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 2) (closed_mem 16 2) cl_10960 (by decide) v hb
def cl_10961 : CNF.NClause := [(622,false),(627,true),(632,true),(637,true),(642,true),(645,true)]
theorem inp_10961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10961 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 2) (closed_mem 16 2) cl_10961 (by decide) v hb
def cl_10963 : CNF.NClause := [(623,true),(628,true),(633,true),(638,true),(643,false),(645,true)]
theorem inp_10963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10963 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 3) (closed_mem 16 3) cl_10963 (by decide) v hb
def cl_10966 : CNF.NClause := [(623,true),(628,false),(633,true),(638,true),(643,true),(645,true)]
theorem inp_10966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10966 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 3) (closed_mem 16 3) cl_10966 (by decide) v hb
def cl_10970 : CNF.NClause := [(621,true),(626,true),(631,true),(636,false),(641,true),(645,true)]
theorem inp_10970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10970 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 4) (closed_mem 16 4) cl_10970 (by decide) v hb
def cl_10975 : CNF.NClause := [(640,true),(641,true),(642,true),(643,true),(644,false),(650,true)]
theorem inp_10975 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10975 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 5) (closed_mem 16 5) cl_10975 (by decide) v hb
def cl_10978 : CNF.NClause := [(640,true),(641,false),(642,true),(643,true),(644,true),(650,true)]
theorem inp_10978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10978 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 5) (closed_mem 16 5) cl_10978 (by decide) v hb
def cl_10979 : CNF.NClause := [(640,false),(641,true),(642,true),(643,true),(644,true),(650,true)]
theorem inp_10979 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10979 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 5) (closed_mem 16 5) cl_10979 (by decide) v hb
def cl_10982 : CNF.NClause := [(624,true),(628,true),(632,true),(636,false),(640,true),(649,true)]
theorem inp_10982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10982 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 6) (closed_mem 16 6) cl_10982 (by decide) v hb
def cl_10986 : CNF.NClause := [(622,true),(629,true),(631,true),(638,true),(640,true),(647,false)]
theorem inp_10986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10986 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 7) (closed_mem 16 7) cl_10986 (by decide) v hb
def cl_10987 : CNF.NClause := [(622,true),(629,true),(631,true),(638,true),(640,false),(647,true)]
theorem inp_10987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10987 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 7) (closed_mem 16 7) cl_10987 (by decide) v hb
def cl_10989 : CNF.NClause := [(622,true),(629,true),(631,false),(638,true),(640,true),(647,true)]
theorem inp_10989 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10989 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 7) (closed_mem 16 7) cl_10989 (by decide) v hb
def cl_10992 : CNF.NClause := [(623,true),(626,true),(634,true),(637,true),(640,true),(648,false)]
theorem inp_10992 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10992 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 8) (closed_mem 16 8) cl_10992 (by decide) v hb
def cl_10993 : CNF.NClause := [(623,true),(626,true),(634,true),(637,true),(640,false),(648,true)]
theorem inp_10993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10993 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 8) (closed_mem 16 8) cl_10993 (by decide) v hb
def cl_10994 : CNF.NClause := [(623,true),(626,true),(634,true),(637,false),(640,true),(648,true)]
theorem inp_10994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10994 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 8) (closed_mem 16 8) cl_10994 (by decide) v hb
def cl_10995 : CNF.NClause := [(623,true),(626,true),(634,false),(637,true),(640,true),(648,true)]
theorem inp_10995 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10995 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 8) (closed_mem 16 8) cl_10995 (by decide) v hb
def cl_10996 : CNF.NClause := [(623,true),(626,false),(634,true),(637,true),(640,true),(648,true)]
theorem inp_10996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10996 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 8) (closed_mem 16 8) cl_10996 (by decide) v hb
def cl_10997 : CNF.NClause := [(623,false),(626,true),(634,true),(637,true),(640,true),(648,true)]
theorem inp_10997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10997 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 8) (closed_mem 16 8) cl_10997 (by decide) v hb
def cl_10998 : CNF.NClause := [(621,true),(627,true),(633,true),(639,true),(640,true),(646,false)]
theorem inp_10998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10998 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 9) (closed_mem 16 9) cl_10998 (by decide) v hb
def cl_10999 : CNF.NClause := [(621,true),(627,true),(633,true),(639,true),(640,false),(646,true)]
theorem inp_10999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10999 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 9) (closed_mem 16 9) cl_10999 (by decide) v hb
def cl_11000 : CNF.NClause := [(621,true),(627,true),(633,true),(639,false),(640,true),(646,true)]
theorem inp_11000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11000 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 9) (closed_mem 16 9) cl_11000 (by decide) v hb
def cl_11003 : CNF.NClause := [(621,false),(627,true),(633,true),(639,true),(640,true),(646,true)]
theorem inp_11003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11003 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 9) (closed_mem 16 9) cl_11003 (by decide) v hb
def cl_11005 : CNF.NClause := [(630,true),(631,true),(632,true),(633,true),(634,false),(650,true)]
theorem inp_11005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11005 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 10) (closed_mem 16 10) cl_11005 (by decide) v hb
def cl_11006 : CNF.NClause := [(630,true),(631,true),(632,true),(633,false),(634,true),(650,true)]
theorem inp_11006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11006 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 10) (closed_mem 16 10) cl_11006 (by decide) v hb
def cl_11007 : CNF.NClause := [(630,true),(631,true),(632,false),(633,true),(634,true),(650,true)]
theorem inp_11007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11007 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 10) (closed_mem 16 10) cl_11007 (by decide) v hb
def cl_11008 : CNF.NClause := [(630,true),(631,false),(632,true),(633,true),(634,true),(650,true)]
theorem inp_11008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11008 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 10) (closed_mem 16 10) cl_11008 (by decide) v hb
def cl_11009 : CNF.NClause := [(630,false),(631,true),(632,true),(633,true),(634,true),(650,true)]
theorem inp_11009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11009 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 10) (closed_mem 16 10) cl_11009 (by decide) v hb
def cl_11013 : CNF.NClause := [(624,true),(627,true),(630,false),(638,true),(641,true),(648,true)]
theorem inp_11013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11013 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 11) (closed_mem 16 11) cl_11013 (by decide) v hb
def cl_11015 : CNF.NClause := [(624,false),(627,true),(630,true),(638,true),(641,true),(648,true)]
theorem inp_11015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11015 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 11) (closed_mem 16 11) cl_11015 (by decide) v hb
def cl_11017 : CNF.NClause := [(622,true),(626,true),(630,true),(639,true),(643,false),(649,true)]
theorem inp_11017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11017 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 12) (closed_mem 16 12) cl_11017 (by decide) v hb
def cl_11019 : CNF.NClause := [(622,true),(626,true),(630,false),(639,true),(643,true),(649,true)]
theorem inp_11019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11019 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 12) (closed_mem 16 12) cl_11019 (by decide) v hb
def cl_11020 : CNF.NClause := [(622,true),(626,false),(630,true),(639,true),(643,true),(649,true)]
theorem inp_11020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11020 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 12) (closed_mem 16 12) cl_11020 (by decide) v hb
def cl_11024 : CNF.NClause := [(623,true),(629,true),(630,true),(636,false),(642,true),(646,true)]
theorem inp_11024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11024 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 13) (closed_mem 16 13) cl_11024 (by decide) v hb
def cl_11029 : CNF.NClause := [(621,true),(628,true),(630,true),(637,true),(644,false),(647,true)]
theorem inp_11029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11029 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 14) (closed_mem 16 14) cl_11029 (by decide) v hb
def cl_11030 : CNF.NClause := [(621,true),(628,true),(630,true),(637,false),(644,true),(647,true)]
theorem inp_11030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11030 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 14) (closed_mem 16 14) cl_11030 (by decide) v hb
def cl_11032 : CNF.NClause := [(621,true),(628,false),(630,true),(637,true),(644,true),(647,true)]
theorem inp_11032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11032 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 14) (closed_mem 16 14) cl_11032 (by decide) v hb
def cl_11038 : CNF.NClause := [(635,true),(636,false),(637,true),(638,true),(639,true),(650,true)]
theorem inp_11038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11038 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 15) (closed_mem 16 15) cl_11038 (by decide) v hb
def cl_11040 : CNF.NClause := [(624,true),(626,true),(633,true),(635,true),(642,true),(647,false)]
theorem inp_11040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11040 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 16) (closed_mem 16 16) cl_11040 (by decide) v hb
def cl_11042 : CNF.NClause := [(624,true),(626,true),(633,true),(635,false),(642,true),(647,true)]
theorem inp_11042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11042 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 16) (closed_mem 16 16) cl_11042 (by decide) v hb
def cl_11045 : CNF.NClause := [(624,false),(626,true),(633,true),(635,true),(642,true),(647,true)]
theorem inp_11045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11045 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 16) (closed_mem 16 16) cl_11045 (by decide) v hb
def cl_11047 : CNF.NClause := [(622,true),(628,true),(634,true),(635,true),(641,false),(646,true)]
theorem inp_11047 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11047 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 17) (closed_mem 16 17) cl_11047 (by decide) v hb
def cl_11048 : CNF.NClause := [(622,true),(628,true),(634,true),(635,false),(641,true),(646,true)]
theorem inp_11048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11048 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 17) (closed_mem 16 17) cl_11048 (by decide) v hb
def cl_11049 : CNF.NClause := [(622,true),(628,true),(634,false),(635,true),(641,true),(646,true)]
theorem inp_11049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11049 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 17) (closed_mem 16 17) cl_11049 (by decide) v hb
def cl_11052 : CNF.NClause := [(623,true),(627,true),(631,true),(635,true),(644,true),(649,false)]
theorem inp_11052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11052 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 18) (closed_mem 16 18) cl_11052 (by decide) v hb
def cl_11055 : CNF.NClause := [(623,true),(627,true),(631,false),(635,true),(644,true),(649,true)]
theorem inp_11055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11055 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 18) (closed_mem 16 18) cl_11055 (by decide) v hb
def cl_11056 : CNF.NClause := [(623,true),(627,false),(631,true),(635,true),(644,true),(649,true)]
theorem inp_11056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11056 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 18) (closed_mem 16 18) cl_11056 (by decide) v hb
def cl_11058 : CNF.NClause := [(621,true),(629,true),(632,true),(635,true),(643,true),(648,false)]
theorem inp_11058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11058 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 19) (closed_mem 16 19) cl_11058 (by decide) v hb
def cl_11060 : CNF.NClause := [(621,true),(629,true),(632,true),(635,false),(643,true),(648,true)]
theorem inp_11060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11060 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 19) (closed_mem 16 19) cl_11060 (by decide) v hb
end Percolation.NReplay
