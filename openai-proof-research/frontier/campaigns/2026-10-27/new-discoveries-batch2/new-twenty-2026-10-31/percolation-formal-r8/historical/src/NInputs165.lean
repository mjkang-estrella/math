import NInputs164
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_10098 : CNF.NClause := [(466,true),(473,true),(475,true),(482,true),(489,true),(492,false)]
theorem inp_10098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10098 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 14) (closed_mem 11 14) cl_10098 (by decide) v hb
def cl_10099 : CNF.NClause := [(466,true),(473,true),(475,true),(482,true),(489,false),(492,true)]
theorem inp_10099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10099 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 14) (closed_mem 11 14) cl_10099 (by decide) v hb
def cl_10100 : CNF.NClause := [(466,true),(473,true),(475,true),(482,false),(489,true),(492,true)]
theorem inp_10100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10100 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 14) (closed_mem 11 14) cl_10100 (by decide) v hb
def cl_10101 : CNF.NClause := [(466,true),(473,true),(475,false),(482,true),(489,true),(492,true)]
theorem inp_10101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10101 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 14) (closed_mem 11 14) cl_10101 (by decide) v hb
def cl_10102 : CNF.NClause := [(466,true),(473,false),(475,true),(482,true),(489,true),(492,true)]
theorem inp_10102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10102 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 14) (closed_mem 11 14) cl_10102 (by decide) v hb
def cl_10103 : CNF.NClause := [(466,false),(473,true),(475,true),(482,true),(489,true),(492,true)]
theorem inp_10103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10103 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_10103 v hb
def cl_10105 : CNF.NClause := [(480,true),(481,true),(482,true),(483,true),(484,false),(495,true)]
theorem inp_10105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10105 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 15) (closed_mem 11 15) cl_10105 (by decide) v hb
def cl_10106 : CNF.NClause := [(480,true),(481,true),(482,true),(483,false),(484,true),(495,true)]
theorem inp_10106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10106 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 15) (closed_mem 11 15) cl_10106 (by decide) v hb
def cl_10107 : CNF.NClause := [(480,true),(481,true),(482,false),(483,true),(484,true),(495,true)]
theorem inp_10107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10107 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 15) (closed_mem 11 15) cl_10107 (by decide) v hb
def cl_10108 : CNF.NClause := [(480,true),(481,false),(482,true),(483,true),(484,true),(495,true)]
theorem inp_10108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10108 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 15) (closed_mem 11 15) cl_10108 (by decide) v hb
def cl_10109 : CNF.NClause := [(480,false),(481,true),(482,true),(483,true),(484,true),(495,true)]
theorem inp_10109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10109 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 15) (closed_mem 11 15) cl_10109 (by decide) v hb
def cl_10110 : CNF.NClause := [(469,true),(471,true),(478,true),(480,true),(487,true),(492,false)]
theorem inp_10110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10110 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 16) (closed_mem 11 16) cl_10110 (by decide) v hb
def cl_10111 : CNF.NClause := [(469,true),(471,true),(478,true),(480,true),(487,false),(492,true)]
theorem inp_10111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10111 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 16) (closed_mem 11 16) cl_10111 (by decide) v hb
def cl_10112 : CNF.NClause := [(469,true),(471,true),(478,true),(480,false),(487,true),(492,true)]
theorem inp_10112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10112 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 16) (closed_mem 11 16) cl_10112 (by decide) v hb
def cl_10113 : CNF.NClause := [(469,true),(471,true),(478,false),(480,true),(487,true),(492,true)]
theorem inp_10113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10113 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 16) (closed_mem 11 16) cl_10113 (by decide) v hb
def cl_10115 : CNF.NClause := [(469,false),(471,true),(478,true),(480,true),(487,true),(492,true)]
theorem inp_10115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10115 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 16) (closed_mem 11 16) cl_10115 (by decide) v hb
def cl_10116 : CNF.NClause := [(467,true),(473,true),(479,true),(480,true),(486,true),(491,false)]
theorem inp_10116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10116 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 17) (closed_mem 11 17) cl_10116 (by decide) v hb
def cl_10117 : CNF.NClause := [(467,true),(473,true),(479,true),(480,true),(486,false),(491,true)]
theorem inp_10117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10117 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 17) (closed_mem 11 17) cl_10117 (by decide) v hb
def cl_10118 : CNF.NClause := [(467,true),(473,true),(479,true),(480,false),(486,true),(491,true)]
theorem inp_10118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10118 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 17) (closed_mem 11 17) cl_10118 (by decide) v hb
def cl_10119 : CNF.NClause := [(467,true),(473,true),(479,false),(480,true),(486,true),(491,true)]
theorem inp_10119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10119 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 17) (closed_mem 11 17) cl_10119 (by decide) v hb
def cl_10121 : CNF.NClause := [(467,false),(473,true),(479,true),(480,true),(486,true),(491,true)]
theorem inp_10121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10121 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 17) (closed_mem 11 17) cl_10121 (by decide) v hb
def cl_10125 : CNF.NClause := [(468,true),(472,true),(476,false),(480,true),(489,true),(494,true)]
theorem inp_10125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10125 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_10125 v hb
def cl_10128 : CNF.NClause := [(466,true),(474,true),(477,true),(480,true),(488,true),(493,false)]
theorem inp_10128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10128 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 19) (closed_mem 11 19) cl_10128 (by decide) v hb
def cl_10129 : CNF.NClause := [(466,true),(474,true),(477,true),(480,true),(488,false),(493,true)]
theorem inp_10129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10129 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 19) (closed_mem 11 19) cl_10129 (by decide) v hb
def cl_10130 : CNF.NClause := [(466,true),(474,true),(477,true),(480,false),(488,true),(493,true)]
theorem inp_10130 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10130 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_10130 v hb
def cl_10131 : CNF.NClause := [(466,true),(474,true),(477,false),(480,true),(488,true),(493,true)]
theorem inp_10131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10131 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 19) (closed_mem 11 19) cl_10131 (by decide) v hb
def cl_10132 : CNF.NClause := [(466,true),(474,false),(477,true),(480,true),(488,true),(493,true)]
theorem inp_10132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10132 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 19) (closed_mem 11 19) cl_10132 (by decide) v hb
def cl_10133 : CNF.NClause := [(466,false),(474,true),(477,true),(480,true),(488,true),(493,true)]
theorem inp_10133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10133 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_10133 v hb
def cl_10135 : CNF.NClause := [(470,true),(471,true),(472,true),(473,true),(474,false),(495,true)]
theorem inp_10135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10135 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 20) (closed_mem 11 20) cl_10135 (by decide) v hb
def cl_10136 : CNF.NClause := [(470,true),(471,true),(472,true),(473,false),(474,true),(495,true)]
theorem inp_10136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10136 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 20) (closed_mem 11 20) cl_10136 (by decide) v hb
def cl_10137 : CNF.NClause := [(470,true),(471,true),(472,false),(473,true),(474,true),(495,true)]
theorem inp_10137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10137 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 20) (closed_mem 11 20) cl_10137 (by decide) v hb
def cl_10138 : CNF.NClause := [(470,true),(471,false),(472,true),(473,true),(474,true),(495,true)]
theorem inp_10138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10138 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 20) (closed_mem 11 20) cl_10138 (by decide) v hb
def cl_10139 : CNF.NClause := [(470,false),(471,true),(472,true),(473,true),(474,true),(495,true)]
theorem inp_10139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10139 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 20) (closed_mem 11 20) cl_10139 (by decide) v hb
def cl_10143 : CNF.NClause := [(469,true),(470,true),(476,false),(482,true),(488,true),(491,true)]
theorem inp_10143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10143 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 21) (closed_mem 11 21) cl_10143 (by decide) v hb
def cl_10146 : CNF.NClause := [(467,true),(470,true),(478,true),(481,true),(489,true),(493,false)]
theorem inp_10146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10146 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 22) (closed_mem 11 22) cl_10146 (by decide) v hb
def cl_10147 : CNF.NClause := [(467,true),(470,true),(478,true),(481,true),(489,false),(493,true)]
theorem inp_10147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10147 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_10147 v hb
def cl_10148 : CNF.NClause := [(467,true),(470,true),(478,true),(481,false),(489,true),(493,true)]
theorem inp_10148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10148 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 22) (closed_mem 11 22) cl_10148 (by decide) v hb
def cl_10149 : CNF.NClause := [(467,true),(470,true),(478,false),(481,true),(489,true),(493,true)]
theorem inp_10149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10149 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 22) (closed_mem 11 22) cl_10149 (by decide) v hb
def cl_10150 : CNF.NClause := [(467,true),(470,false),(478,true),(481,true),(489,true),(493,true)]
theorem inp_10150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10150 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 22) (closed_mem 11 22) cl_10150 (by decide) v hb
def cl_10152 : CNF.NClause := [(468,true),(470,true),(477,true),(484,true),(486,true),(492,false)]
theorem inp_10152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10152 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 23) (closed_mem 11 23) cl_10152 (by decide) v hb
def cl_10153 : CNF.NClause := [(468,true),(470,true),(477,true),(484,true),(486,false),(492,true)]
theorem inp_10153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10153 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 23) (closed_mem 11 23) cl_10153 (by decide) v hb
def cl_10154 : CNF.NClause := [(468,true),(470,true),(477,true),(484,false),(486,true),(492,true)]
theorem inp_10154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10154 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 23) (closed_mem 11 23) cl_10154 (by decide) v hb
def cl_10155 : CNF.NClause := [(468,true),(470,true),(477,false),(484,true),(486,true),(492,true)]
theorem inp_10155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10155 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_10155 v hb
def cl_10156 : CNF.NClause := [(468,true),(470,false),(477,true),(484,true),(486,true),(492,true)]
theorem inp_10156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10156 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 23) (closed_mem 11 23) cl_10156 (by decide) v hb
def cl_10157 : CNF.NClause := [(468,false),(470,true),(477,true),(484,true),(486,true),(492,true)]
theorem inp_10157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10157 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 23) (closed_mem 11 23) cl_10157 (by decide) v hb
def cl_10159 : CNF.NClause := [(466,true),(470,true),(479,true),(483,true),(487,false),(494,true)]
theorem inp_10159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10159 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 24) (closed_mem 11 24) cl_10159 (by decide) v hb
def cl_10161 : CNF.NClause := [(466,true),(470,true),(479,false),(483,true),(487,true),(494,true)]
theorem inp_10161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10161 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 24) (closed_mem 11 24) cl_10161 (by decide) v hb
def cl_10165 : CNF.NClause := [(465,true),(466,true),(467,true),(468,true),(469,false),(495,true)]
theorem inp_10165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10165 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 25) (closed_mem 11 25) cl_10165 (by decide) v hb
def cl_10166 : CNF.NClause := [(465,true),(466,true),(467,true),(468,false),(469,true),(495,true)]
theorem inp_10166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10166 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 25) (closed_mem 11 25) cl_10166 (by decide) v hb
def cl_10167 : CNF.NClause := [(465,true),(466,true),(467,false),(468,true),(469,true),(495,true)]
theorem inp_10167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10167 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 11 25) (closed_mem 11 25) cl_10167 (by decide) v hb
end Percolation.NReplay
