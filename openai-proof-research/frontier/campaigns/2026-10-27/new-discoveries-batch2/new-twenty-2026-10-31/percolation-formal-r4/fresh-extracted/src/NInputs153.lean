import NInputs152
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_9070 : CNF.NClause := [(279,true),(287,false),(290,true),(298,true),(301,true),(307,true)]
theorem inp_9070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9070 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 28) (closed_mem 5 28) cl_9070 (by decide) v hb
def cl_9072 : CNF.NClause := [(279,true),(285,true),(291,true),(297,true),(303,true),(305,false)]
theorem inp_9072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9072 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9072 v hb
def cl_9073 : CNF.NClause := [(279,true),(285,true),(291,true),(297,true),(303,false),(305,true)]
theorem inp_9073 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9073 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9073 v hb
def cl_9074 : CNF.NClause := [(279,true),(285,true),(291,true),(297,false),(303,true),(305,true)]
theorem inp_9074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9074 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 29) (closed_mem 5 29) cl_9074 (by decide) v hb
def cl_9076 : CNF.NClause := [(279,true),(285,false),(291,true),(297,true),(303,true),(305,true)]
theorem inp_9076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9076 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 29) (closed_mem 5 29) cl_9076 (by decide) v hb
def cl_9082 : CNF.NClause := [(279,true),(284,false),(289,true),(294,true),(299,true),(304,true)]
theorem inp_9082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9082 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 30) (closed_mem 5 30) cl_9082 (by decide) v hb
def cl_9085 : CNF.NClause := [(335,true),(336,true),(337,true),(338,true),(339,false),(340,true)]
theorem inp_9085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9085 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 0) (closed_mem 6 0) cl_9085 (by decide) v hb
def cl_9086 : CNF.NClause := [(335,true),(336,true),(337,true),(338,false),(339,true),(340,true)]
theorem inp_9086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9086 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 0) (closed_mem 6 0) cl_9086 (by decide) v hb
def cl_9087 : CNF.NClause := [(335,true),(336,true),(337,false),(338,true),(339,true),(340,true)]
theorem inp_9087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9087 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 0) (closed_mem 6 0) cl_9087 (by decide) v hb
def cl_9088 : CNF.NClause := [(335,true),(336,false),(337,true),(338,true),(339,true),(340,true)]
theorem inp_9088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9088 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 0) (closed_mem 6 0) cl_9088 (by decide) v hb
def cl_9091 : CNF.NClause := [(314,true),(319,true),(324,true),(329,true),(334,false),(335,true)]
theorem inp_9091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9091 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 1) (closed_mem 6 1) cl_9091 (by decide) v hb
def cl_9092 : CNF.NClause := [(314,true),(319,true),(324,true),(329,false),(334,true),(335,true)]
theorem inp_9092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9092 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 1) (closed_mem 6 1) cl_9092 (by decide) v hb
def cl_9093 : CNF.NClause := [(314,true),(319,true),(324,false),(329,true),(334,true),(335,true)]
theorem inp_9093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9093 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 1) (closed_mem 6 1) cl_9093 (by decide) v hb
def cl_9094 : CNF.NClause := [(314,true),(319,false),(324,true),(329,true),(334,true),(335,true)]
theorem inp_9094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9094 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 1) (closed_mem 6 1) cl_9094 (by decide) v hb
def cl_9095 : CNF.NClause := [(314,false),(319,true),(324,true),(329,true),(334,true),(335,true)]
theorem inp_9095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9095 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 1) (closed_mem 6 1) cl_9095 (by decide) v hb
def cl_9097 : CNF.NClause := [(312,true),(317,true),(322,true),(327,true),(332,false),(335,true)]
theorem inp_9097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9097 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 2) (closed_mem 6 2) cl_9097 (by decide) v hb
def cl_9098 : CNF.NClause := [(312,true),(317,true),(322,true),(327,false),(332,true),(335,true)]
theorem inp_9098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9098 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 2) (closed_mem 6 2) cl_9098 (by decide) v hb
def cl_9099 : CNF.NClause := [(312,true),(317,true),(322,false),(327,true),(332,true),(335,true)]
theorem inp_9099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9099 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 2) (closed_mem 6 2) cl_9099 (by decide) v hb
def cl_9100 : CNF.NClause := [(312,true),(317,false),(322,true),(327,true),(332,true),(335,true)]
theorem inp_9100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9100 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 2) (closed_mem 6 2) cl_9100 (by decide) v hb
def cl_9101 : CNF.NClause := [(312,false),(317,true),(322,true),(327,true),(332,true),(335,true)]
theorem inp_9101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9101 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 2) (closed_mem 6 2) cl_9101 (by decide) v hb
def cl_9103 : CNF.NClause := [(313,true),(318,true),(323,true),(328,true),(333,false),(335,true)]
theorem inp_9103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9103 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 3) (closed_mem 6 3) cl_9103 (by decide) v hb
def cl_9104 : CNF.NClause := [(313,true),(318,true),(323,true),(328,false),(333,true),(335,true)]
theorem inp_9104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9104 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 3) (closed_mem 6 3) cl_9104 (by decide) v hb
def cl_9106 : CNF.NClause := [(313,true),(318,false),(323,true),(328,true),(333,true),(335,true)]
theorem inp_9106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9106 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 3) (closed_mem 6 3) cl_9106 (by decide) v hb
def cl_9107 : CNF.NClause := [(313,false),(318,true),(323,true),(328,true),(333,true),(335,true)]
theorem inp_9107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9107 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 3) (closed_mem 6 3) cl_9107 (by decide) v hb
def cl_9112 : CNF.NClause := [(311,true),(316,false),(321,true),(326,true),(331,true),(335,true)]
theorem inp_9112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9112 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 4) (closed_mem 6 4) cl_9112 (by decide) v hb
def cl_9115 : CNF.NClause := [(330,true),(331,true),(332,true),(333,true),(334,false),(340,true)]
theorem inp_9115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9115 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 5) (closed_mem 6 5) cl_9115 (by decide) v hb
def cl_9116 : CNF.NClause := [(330,true),(331,true),(332,true),(333,false),(334,true),(340,true)]
theorem inp_9116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9116 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 5) (closed_mem 6 5) cl_9116 (by decide) v hb
def cl_9117 : CNF.NClause := [(330,true),(331,true),(332,false),(333,true),(334,true),(340,true)]
theorem inp_9117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9117 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 5) (closed_mem 6 5) cl_9117 (by decide) v hb
def cl_9118 : CNF.NClause := [(330,true),(331,false),(332,true),(333,true),(334,true),(340,true)]
theorem inp_9118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9118 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 5) (closed_mem 6 5) cl_9118 (by decide) v hb
def cl_9119 : CNF.NClause := [(330,false),(331,true),(332,true),(333,true),(334,true),(340,true)]
theorem inp_9119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9119 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 5) (closed_mem 6 5) cl_9119 (by decide) v hb
def cl_9121 : CNF.NClause := [(314,true),(318,true),(322,true),(326,true),(330,false),(339,true)]
theorem inp_9121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9121 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 6) (closed_mem 6 6) cl_9121 (by decide) v hb
def cl_9122 : CNF.NClause := [(314,true),(318,true),(322,true),(326,false),(330,true),(339,true)]
theorem inp_9122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9122 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 6) (closed_mem 6 6) cl_9122 (by decide) v hb
def cl_9126 : CNF.NClause := [(312,true),(319,true),(321,true),(328,true),(330,true),(337,false)]
theorem inp_9126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9126 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 7) (closed_mem 6 7) cl_9126 (by decide) v hb
def cl_9127 : CNF.NClause := [(312,true),(319,true),(321,true),(328,true),(330,false),(337,true)]
theorem inp_9127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9127 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 7) (closed_mem 6 7) cl_9127 (by decide) v hb
def cl_9129 : CNF.NClause := [(312,true),(319,true),(321,false),(328,true),(330,true),(337,true)]
theorem inp_9129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9129 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 7) (closed_mem 6 7) cl_9129 (by decide) v hb
def cl_9131 : CNF.NClause := [(312,false),(319,true),(321,true),(328,true),(330,true),(337,true)]
theorem inp_9131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9131 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 7) (closed_mem 6 7) cl_9131 (by decide) v hb
def cl_9136 : CNF.NClause := [(313,true),(316,false),(324,true),(327,true),(330,true),(338,true)]
theorem inp_9136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9136 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 8) (closed_mem 6 8) cl_9136 (by decide) v hb
def cl_9138 : CNF.NClause := [(311,true),(317,true),(323,true),(329,true),(330,true),(336,false)]
theorem inp_9138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9138 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 9) (closed_mem 6 9) cl_9138 (by decide) v hb
def cl_9139 : CNF.NClause := [(311,true),(317,true),(323,true),(329,true),(330,false),(336,true)]
theorem inp_9139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9139 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 9) (closed_mem 6 9) cl_9139 (by decide) v hb
def cl_9140 : CNF.NClause := [(311,true),(317,true),(323,true),(329,false),(330,true),(336,true)]
theorem inp_9140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9140 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 9) (closed_mem 6 9) cl_9140 (by decide) v hb
def cl_9142 : CNF.NClause := [(311,true),(317,false),(323,true),(329,true),(330,true),(336,true)]
theorem inp_9142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9142 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 9) (closed_mem 6 9) cl_9142 (by decide) v hb
def cl_9143 : CNF.NClause := [(311,false),(317,true),(323,true),(329,true),(330,true),(336,true)]
theorem inp_9143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9143 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 9) (closed_mem 6 9) cl_9143 (by decide) v hb
def cl_9146 : CNF.NClause := [(320,true),(321,true),(322,true),(323,false),(324,true),(340,true)]
theorem inp_9146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9146 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 10) (closed_mem 6 10) cl_9146 (by decide) v hb
def cl_9147 : CNF.NClause := [(320,true),(321,true),(322,false),(323,true),(324,true),(340,true)]
theorem inp_9147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9147 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 10) (closed_mem 6 10) cl_9147 (by decide) v hb
def cl_9148 : CNF.NClause := [(320,true),(321,false),(322,true),(323,true),(324,true),(340,true)]
theorem inp_9148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9148 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 10) (closed_mem 6 10) cl_9148 (by decide) v hb
def cl_9149 : CNF.NClause := [(320,false),(321,true),(322,true),(323,true),(324,true),(340,true)]
theorem inp_9149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9149 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 10) (closed_mem 6 10) cl_9149 (by decide) v hb
def cl_9150 : CNF.NClause := [(314,true),(317,true),(320,true),(328,true),(331,true),(338,false)]
theorem inp_9150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9150 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 11) (closed_mem 6 11) cl_9150 (by decide) v hb
def cl_9152 : CNF.NClause := [(314,true),(317,true),(320,true),(328,false),(331,true),(338,true)]
theorem inp_9152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9152 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 11) (closed_mem 6 11) cl_9152 (by decide) v hb
def cl_9153 : CNF.NClause := [(314,true),(317,true),(320,false),(328,true),(331,true),(338,true)]
theorem inp_9153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9153 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 11) (closed_mem 6 11) cl_9153 (by decide) v hb
def cl_9154 : CNF.NClause := [(314,true),(317,false),(320,true),(328,true),(331,true),(338,true)]
theorem inp_9154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9154 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 6 11) (closed_mem 6 11) cl_9154 (by decide) v hb
end Percolation.NReplay
