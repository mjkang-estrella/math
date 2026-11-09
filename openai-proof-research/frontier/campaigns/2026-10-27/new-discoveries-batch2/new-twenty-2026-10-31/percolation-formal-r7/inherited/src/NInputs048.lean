import NInputs047
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_3005 : CNF.NClause := [(108,true),(46,false),(47,false),(48,true),(49,true),(50,true),(61,true)]
theorem inp_3005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3005 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_3005 (by decide) v hb
def cl_3006 : CNF.NClause := [(108,false),(46,true),(47,false),(48,true),(49,true),(50,true),(61,true)]
theorem inp_3006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3006 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_3006 (by decide) v hb
def cl_3007 : CNF.NClause := [(108,false),(46,false),(47,true),(48,true),(49,true),(50,true),(61,true)]
theorem inp_3007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3007 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_3007 (by decide) v hb
def cl_3008 : CNF.NClause := [(108,false),(46,true),(47,true),(48,true),(49,true),(50,true),(61,true)]
theorem inp_3008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3008 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_3008 (by decide) v hb
def cl_3009 : CNF.NClause := [(109,true),(35,false),(37,false),(44,false),(46,false),(53,false),(58,false)]
theorem inp_3009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3009 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3009 (by decide) v hb
def cl_3010 : CNF.NClause := [(109,true),(35,true),(37,false),(44,false),(46,false),(53,false),(58,false)]
theorem inp_3010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3010 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3010 (by decide) v hb
def cl_3011 : CNF.NClause := [(109,true),(35,false),(37,true),(44,false),(46,false),(53,false),(58,false)]
theorem inp_3011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3011 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3011 (by decide) v hb
def cl_3012 : CNF.NClause := [(109,true),(35,true),(37,true),(44,false),(46,false),(53,false),(58,false)]
theorem inp_3012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3012 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3012 (by decide) v hb
def cl_3013 : CNF.NClause := [(109,true),(35,false),(37,false),(44,true),(46,false),(53,false),(58,false)]
theorem inp_3013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3013 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3013 (by decide) v hb
def cl_3014 : CNF.NClause := [(109,true),(35,true),(37,false),(44,true),(46,false),(53,false),(58,false)]
theorem inp_3014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3014 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3014 (by decide) v hb
def cl_3015 : CNF.NClause := [(109,true),(35,false),(37,true),(44,true),(46,false),(53,false),(58,false)]
theorem inp_3015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3015 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3015 (by decide) v hb
def cl_3016 : CNF.NClause := [(109,true),(35,true),(37,true),(44,true),(46,false),(53,false),(58,false)]
theorem inp_3016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3016 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3016 (by decide) v hb
def cl_3017 : CNF.NClause := [(109,true),(35,false),(37,false),(44,false),(46,true),(53,false),(58,false)]
theorem inp_3017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3017 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3017 (by decide) v hb
def cl_3018 : CNF.NClause := [(109,true),(35,true),(37,false),(44,false),(46,true),(53,false),(58,false)]
theorem inp_3018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3018 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3018 (by decide) v hb
def cl_3019 : CNF.NClause := [(109,true),(35,false),(37,true),(44,false),(46,true),(53,false),(58,false)]
theorem inp_3019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3019 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3019 (by decide) v hb
def cl_3020 : CNF.NClause := [(109,true),(35,true),(37,true),(44,false),(46,true),(53,false),(58,false)]
theorem inp_3020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3020 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3020 (by decide) v hb
def cl_3021 : CNF.NClause := [(109,true),(35,false),(37,false),(44,true),(46,true),(53,false),(58,false)]
theorem inp_3021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3021 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3021 (by decide) v hb
def cl_3022 : CNF.NClause := [(109,true),(35,true),(37,false),(44,true),(46,true),(53,false),(58,false)]
theorem inp_3022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3022 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3022 (by decide) v hb
def cl_3023 : CNF.NClause := [(109,true),(35,false),(37,true),(44,true),(46,true),(53,false),(58,false)]
theorem inp_3023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3023 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3023 (by decide) v hb
def cl_3024 : CNF.NClause := [(109,true),(35,true),(37,true),(44,true),(46,true),(53,false),(58,false)]
theorem inp_3024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3024 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3024 (by decide) v hb
def cl_3025 : CNF.NClause := [(109,true),(35,false),(37,false),(44,false),(46,false),(53,true),(58,false)]
theorem inp_3025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3025 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3025 (by decide) v hb
def cl_3026 : CNF.NClause := [(109,true),(35,true),(37,false),(44,false),(46,false),(53,true),(58,false)]
theorem inp_3026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3026 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3026 (by decide) v hb
def cl_3027 : CNF.NClause := [(109,true),(35,false),(37,true),(44,false),(46,false),(53,true),(58,false)]
theorem inp_3027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3027 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3027 (by decide) v hb
def cl_3028 : CNF.NClause := [(109,true),(35,true),(37,true),(44,false),(46,false),(53,true),(58,false)]
theorem inp_3028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3028 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3028 v hb
def cl_3029 : CNF.NClause := [(109,true),(35,false),(37,false),(44,true),(46,false),(53,true),(58,false)]
theorem inp_3029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3029 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3029 (by decide) v hb
def cl_3030 : CNF.NClause := [(109,true),(35,true),(37,false),(44,true),(46,false),(53,true),(58,false)]
theorem inp_3030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3030 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3030 (by decide) v hb
def cl_3031 : CNF.NClause := [(109,true),(35,false),(37,true),(44,true),(46,false),(53,true),(58,false)]
theorem inp_3031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3031 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3031 (by decide) v hb
def cl_3032 : CNF.NClause := [(109,true),(35,true),(37,true),(44,true),(46,false),(53,true),(58,false)]
theorem inp_3032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3032 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3032 (by decide) v hb
def cl_3033 : CNF.NClause := [(109,true),(35,false),(37,false),(44,false),(46,true),(53,true),(58,false)]
theorem inp_3033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3033 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3033 (by decide) v hb
def cl_3034 : CNF.NClause := [(109,true),(35,true),(37,false),(44,false),(46,true),(53,true),(58,false)]
theorem inp_3034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3034 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3034 (by decide) v hb
def cl_3035 : CNF.NClause := [(109,true),(35,false),(37,true),(44,false),(46,true),(53,true),(58,false)]
theorem inp_3035 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3035 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3035 (by decide) v hb
def cl_3036 : CNF.NClause := [(109,true),(35,true),(37,true),(44,false),(46,true),(53,true),(58,false)]
theorem inp_3036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3036 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3036 (by decide) v hb
def cl_3037 : CNF.NClause := [(109,true),(35,false),(37,false),(44,true),(46,true),(53,true),(58,false)]
theorem inp_3037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3037 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3037 (by decide) v hb
def cl_3038 : CNF.NClause := [(109,true),(35,true),(37,false),(44,true),(46,true),(53,true),(58,false)]
theorem inp_3038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3038 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3038 (by decide) v hb
def cl_3039 : CNF.NClause := [(109,true),(35,false),(37,true),(44,true),(46,true),(53,true),(58,false)]
theorem inp_3039 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3039 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3039 (by decide) v hb
def cl_3040 : CNF.NClause := [(109,false),(35,true),(37,true),(44,true),(46,true),(53,true),(58,false)]
theorem inp_3040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3040 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3040 (by decide) v hb
def cl_3041 : CNF.NClause := [(109,true),(35,false),(37,false),(44,false),(46,false),(53,false),(58,true)]
theorem inp_3041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3041 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3041 (by decide) v hb
def cl_3042 : CNF.NClause := [(109,true),(35,true),(37,false),(44,false),(46,false),(53,false),(58,true)]
theorem inp_3042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3042 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3042 (by decide) v hb
def cl_3043 : CNF.NClause := [(109,true),(35,false),(37,true),(44,false),(46,false),(53,false),(58,true)]
theorem inp_3043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3043 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3043 (by decide) v hb
def cl_3044 : CNF.NClause := [(109,true),(35,true),(37,true),(44,false),(46,false),(53,false),(58,true)]
theorem inp_3044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3044 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3044 (by decide) v hb
def cl_3045 : CNF.NClause := [(109,true),(35,false),(37,false),(44,true),(46,false),(53,false),(58,true)]
theorem inp_3045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3045 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3045 (by decide) v hb
def cl_3046 : CNF.NClause := [(109,true),(35,true),(37,false),(44,true),(46,false),(53,false),(58,true)]
theorem inp_3046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3046 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3046 (by decide) v hb
def cl_3047 : CNF.NClause := [(109,true),(35,false),(37,true),(44,true),(46,false),(53,false),(58,true)]
theorem inp_3047 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3047 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3047 (by decide) v hb
def cl_3048 : CNF.NClause := [(109,true),(35,true),(37,true),(44,true),(46,false),(53,false),(58,true)]
theorem inp_3048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3048 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3048 (by decide) v hb
def cl_3049 : CNF.NClause := [(109,true),(35,false),(37,false),(44,false),(46,true),(53,false),(58,true)]
theorem inp_3049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3049 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3049 (by decide) v hb
def cl_3050 : CNF.NClause := [(109,true),(35,true),(37,false),(44,false),(46,true),(53,false),(58,true)]
theorem inp_3050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3050 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3050 (by decide) v hb
def cl_3051 : CNF.NClause := [(109,true),(35,false),(37,true),(44,false),(46,true),(53,false),(58,true)]
theorem inp_3051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3051 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3051 (by decide) v hb
def cl_3052 : CNF.NClause := [(109,true),(35,true),(37,true),(44,false),(46,true),(53,false),(58,true)]
theorem inp_3052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3052 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3052 (by decide) v hb
def cl_3053 : CNF.NClause := [(109,true),(35,false),(37,false),(44,true),(46,true),(53,false),(58,true)]
theorem inp_3053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3053 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3053 (by decide) v hb
def cl_3054 : CNF.NClause := [(109,true),(35,true),(37,false),(44,true),(46,true),(53,false),(58,true)]
theorem inp_3054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3054 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3054 (by decide) v hb
end Percolation.NReplay
