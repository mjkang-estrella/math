import NInputs163
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_10024 : CNF.NClause := [(469,true),(474,false),(479,true),(484,true),(489,true),(490,true)]
theorem inp_10024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10024 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 1) (closed_mem 11 1) cl_10024 (by decide) v hb
def cl_10025 : CNF.NClause := [(469,false),(474,true),(479,true),(484,true),(489,true),(490,true)]
theorem inp_10025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10025 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 1) (closed_mem 11 1) cl_10025 (by decide) v hb
def cl_10027 : CNF.NClause := [(467,true),(472,true),(477,true),(482,true),(487,false),(490,true)]
theorem inp_10027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10027 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 2) (closed_mem 11 2) cl_10027 (by decide) v hb
def cl_10028 : CNF.NClause := [(467,true),(472,true),(477,true),(482,false),(487,true),(490,true)]
theorem inp_10028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10028 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 2) (closed_mem 11 2) cl_10028 (by decide) v hb
def cl_10029 : CNF.NClause := [(467,true),(472,true),(477,false),(482,true),(487,true),(490,true)]
theorem inp_10029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10029 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 2) (closed_mem 11 2) cl_10029 (by decide) v hb
def cl_10030 : CNF.NClause := [(467,true),(472,false),(477,true),(482,true),(487,true),(490,true)]
theorem inp_10030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10030 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 2) (closed_mem 11 2) cl_10030 (by decide) v hb
def cl_10031 : CNF.NClause := [(467,false),(472,true),(477,true),(482,true),(487,true),(490,true)]
theorem inp_10031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10031 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 2) (closed_mem 11 2) cl_10031 (by decide) v hb
def cl_10033 : CNF.NClause := [(468,true),(473,true),(478,true),(483,true),(488,false),(490,true)]
theorem inp_10033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10033 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 3) (closed_mem 11 3) cl_10033 (by decide) v hb
def cl_10034 : CNF.NClause := [(468,true),(473,true),(478,true),(483,false),(488,true),(490,true)]
theorem inp_10034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10034 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 3) (closed_mem 11 3) cl_10034 (by decide) v hb
def cl_10035 : CNF.NClause := [(468,true),(473,true),(478,false),(483,true),(488,true),(490,true)]
theorem inp_10035 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10035 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 3) (closed_mem 11 3) cl_10035 (by decide) v hb
def cl_10036 : CNF.NClause := [(468,true),(473,false),(478,true),(483,true),(488,true),(490,true)]
theorem inp_10036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10036 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 3) (closed_mem 11 3) cl_10036 (by decide) v hb
def cl_10037 : CNF.NClause := [(468,false),(473,true),(478,true),(483,true),(488,true),(490,true)]
theorem inp_10037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10037 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 3) (closed_mem 11 3) cl_10037 (by decide) v hb
def cl_10041 : CNF.NClause := [(466,true),(471,true),(476,false),(481,true),(486,true),(490,true)]
theorem inp_10041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10041 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 4) (closed_mem 11 4) cl_10041 (by decide) v hb
def cl_10045 : CNF.NClause := [(485,true),(486,true),(487,true),(488,true),(489,false),(495,true)]
theorem inp_10045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10045 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 5) (closed_mem 11 5) cl_10045 (by decide) v hb
def cl_10046 : CNF.NClause := [(485,true),(486,true),(487,true),(488,false),(489,true),(495,true)]
theorem inp_10046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10046 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 5) (closed_mem 11 5) cl_10046 (by decide) v hb
def cl_10047 : CNF.NClause := [(485,true),(486,true),(487,false),(488,true),(489,true),(495,true)]
theorem inp_10047 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10047 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 5) (closed_mem 11 5) cl_10047 (by decide) v hb
def cl_10048 : CNF.NClause := [(485,true),(486,false),(487,true),(488,true),(489,true),(495,true)]
theorem inp_10048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10048 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 5) (closed_mem 11 5) cl_10048 (by decide) v hb
def cl_10049 : CNF.NClause := [(485,false),(486,true),(487,true),(488,true),(489,true),(495,true)]
theorem inp_10049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10049 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 5) (closed_mem 11 5) cl_10049 (by decide) v hb
def cl_10050 : CNF.NClause := [(469,true),(473,true),(477,true),(481,true),(485,true),(494,false)]
theorem inp_10050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10050 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 6) (closed_mem 11 6) cl_10050 (by decide) v hb
def cl_10051 : CNF.NClause := [(469,true),(473,true),(477,true),(481,true),(485,false),(494,true)]
theorem inp_10051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10051 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 6) (closed_mem 11 6) cl_10051 (by decide) v hb
def cl_10052 : CNF.NClause := [(469,true),(473,true),(477,true),(481,false),(485,true),(494,true)]
theorem inp_10052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10052 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 6) (closed_mem 11 6) cl_10052 (by decide) v hb
def cl_10053 : CNF.NClause := [(469,true),(473,true),(477,false),(481,true),(485,true),(494,true)]
theorem inp_10053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10053 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 6) (closed_mem 11 6) cl_10053 (by decide) v hb
def cl_10055 : CNF.NClause := [(469,false),(473,true),(477,true),(481,true),(485,true),(494,true)]
theorem inp_10055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10055 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 6) (closed_mem 11 6) cl_10055 (by decide) v hb
def cl_10059 : CNF.NClause := [(467,true),(474,true),(476,false),(483,true),(485,true),(492,true)]
theorem inp_10059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10059 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 7) (closed_mem 11 7) cl_10059 (by decide) v hb
def cl_10062 : CNF.NClause := [(468,true),(471,true),(479,true),(482,true),(485,true),(493,false)]
theorem inp_10062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10062 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 8) (closed_mem 11 8) cl_10062 (by decide) v hb
def cl_10063 : CNF.NClause := [(468,true),(471,true),(479,true),(482,true),(485,false),(493,true)]
theorem inp_10063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10063 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 8) (closed_mem 11 8) cl_10063 (by decide) v hb
def cl_10065 : CNF.NClause := [(468,true),(471,true),(479,false),(482,true),(485,true),(493,true)]
theorem inp_10065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10065 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 8) (closed_mem 11 8) cl_10065 (by decide) v hb
def cl_10066 : CNF.NClause := [(468,true),(471,false),(479,true),(482,true),(485,true),(493,true)]
theorem inp_10066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10066 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 8) (closed_mem 11 8) cl_10066 (by decide) v hb
def cl_10067 : CNF.NClause := [(468,false),(471,true),(479,true),(482,true),(485,true),(493,true)]
theorem inp_10067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10067 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 8) (closed_mem 11 8) cl_10067 (by decide) v hb
def cl_10068 : CNF.NClause := [(466,true),(472,true),(478,true),(484,true),(485,true),(491,false)]
theorem inp_10068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10068 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 9) (closed_mem 11 9) cl_10068 (by decide) v hb
def cl_10069 : CNF.NClause := [(466,true),(472,true),(478,true),(484,true),(485,false),(491,true)]
theorem inp_10069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10069 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 9) (closed_mem 11 9) cl_10069 (by decide) v hb
def cl_10071 : CNF.NClause := [(466,true),(472,true),(478,false),(484,true),(485,true),(491,true)]
theorem inp_10071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10071 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 9) (closed_mem 11 9) cl_10071 (by decide) v hb
def cl_10072 : CNF.NClause := [(466,true),(472,false),(478,true),(484,true),(485,true),(491,true)]
theorem inp_10072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10072 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 9) (closed_mem 11 9) cl_10072 (by decide) v hb
def cl_10078 : CNF.NClause := [(475,true),(476,false),(477,true),(478,true),(479,true),(495,true)]
theorem inp_10078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10078 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_10078 v hb
def cl_10080 : CNF.NClause := [(469,true),(472,true),(475,true),(483,true),(486,true),(493,false)]
theorem inp_10080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10080 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 11) (closed_mem 11 11) cl_10080 (by decide) v hb
def cl_10081 : CNF.NClause := [(469,true),(472,true),(475,true),(483,true),(486,false),(493,true)]
theorem inp_10081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10081 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 11) (closed_mem 11 11) cl_10081 (by decide) v hb
def cl_10082 : CNF.NClause := [(469,true),(472,true),(475,true),(483,false),(486,true),(493,true)]
theorem inp_10082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10082 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_10082 v hb
def cl_10083 : CNF.NClause := [(469,true),(472,true),(475,false),(483,true),(486,true),(493,true)]
theorem inp_10083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10083 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 11) (closed_mem 11 11) cl_10083 (by decide) v hb
def cl_10084 : CNF.NClause := [(469,true),(472,false),(475,true),(483,true),(486,true),(493,true)]
theorem inp_10084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10084 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 11) (closed_mem 11 11) cl_10084 (by decide) v hb
def cl_10085 : CNF.NClause := [(469,false),(472,true),(475,true),(483,true),(486,true),(493,true)]
theorem inp_10085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10085 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 11) (closed_mem 11 11) cl_10085 (by decide) v hb
def cl_10086 : CNF.NClause := [(467,true),(471,true),(475,true),(484,true),(488,true),(494,false)]
theorem inp_10086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10086 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 12) (closed_mem 11 12) cl_10086 (by decide) v hb
def cl_10087 : CNF.NClause := [(467,true),(471,true),(475,true),(484,true),(488,false),(494,true)]
theorem inp_10087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10087 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 12) (closed_mem 11 12) cl_10087 (by decide) v hb
def cl_10088 : CNF.NClause := [(467,true),(471,true),(475,true),(484,false),(488,true),(494,true)]
theorem inp_10088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10088 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 12) (closed_mem 11 12) cl_10088 (by decide) v hb
def cl_10089 : CNF.NClause := [(467,true),(471,true),(475,false),(484,true),(488,true),(494,true)]
theorem inp_10089 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10089 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 12) (closed_mem 11 12) cl_10089 (by decide) v hb
def cl_10091 : CNF.NClause := [(467,false),(471,true),(475,true),(484,true),(488,true),(494,true)]
theorem inp_10091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10091 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 12) (closed_mem 11 12) cl_10091 (by decide) v hb
def cl_10092 : CNF.NClause := [(468,true),(474,true),(475,true),(481,true),(487,true),(491,false)]
theorem inp_10092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10092 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 13) (closed_mem 11 13) cl_10092 (by decide) v hb
def cl_10093 : CNF.NClause := [(468,true),(474,true),(475,true),(481,true),(487,false),(491,true)]
theorem inp_10093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10093 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 13) (closed_mem 11 13) cl_10093 (by decide) v hb
def cl_10095 : CNF.NClause := [(468,true),(474,true),(475,false),(481,true),(487,true),(491,true)]
theorem inp_10095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10095 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 13) (closed_mem 11 13) cl_10095 (by decide) v hb
def cl_10096 : CNF.NClause := [(468,true),(474,false),(475,true),(481,true),(487,true),(491,true)]
theorem inp_10096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10096 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 13) (closed_mem 11 13) cl_10096 (by decide) v hb
def cl_10097 : CNF.NClause := [(468,false),(474,true),(475,true),(481,true),(487,true),(491,true)]
theorem inp_10097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10097 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 13) (closed_mem 11 13) cl_10097 (by decide) v hb
end Percolation.NReplay
