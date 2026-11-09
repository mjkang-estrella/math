import NInputs151
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_8973 : CNF.NClause := [(281,true),(285,true),(289,false),(298,true),(302,true),(308,true)]
theorem inp_8973 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8973 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 12) (closed_mem 5 12) cl_8973 (by decide) v hb
def cl_8974 : CNF.NClause := [(281,true),(285,false),(289,true),(298,true),(302,true),(308,true)]
theorem inp_8974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8974 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_8974 v hb
def cl_8976 : CNF.NClause := [(282,true),(288,true),(289,true),(295,true),(301,true),(305,false)]
theorem inp_8976 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8976 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 13) (closed_mem 5 13) cl_8976 (by decide) v hb
def cl_8977 : CNF.NClause := [(282,true),(288,true),(289,true),(295,true),(301,false),(305,true)]
theorem inp_8977 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8977 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 13) (closed_mem 5 13) cl_8977 (by decide) v hb
def cl_8978 : CNF.NClause := [(282,true),(288,true),(289,true),(295,false),(301,true),(305,true)]
theorem inp_8978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8978 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 13) (closed_mem 5 13) cl_8978 (by decide) v hb
def cl_8979 : CNF.NClause := [(282,true),(288,true),(289,false),(295,true),(301,true),(305,true)]
theorem inp_8979 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8979 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 13) (closed_mem 5 13) cl_8979 (by decide) v hb
def cl_8980 : CNF.NClause := [(282,true),(288,false),(289,true),(295,true),(301,true),(305,true)]
theorem inp_8980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8980 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 13) (closed_mem 5 13) cl_8980 (by decide) v hb
def cl_8981 : CNF.NClause := [(282,false),(288,true),(289,true),(295,true),(301,true),(305,true)]
theorem inp_8981 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8981 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 13) (closed_mem 5 13) cl_8981 (by decide) v hb
def cl_8982 : CNF.NClause := [(280,true),(287,true),(289,true),(296,true),(303,true),(306,false)]
theorem inp_8982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8982 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 14) (closed_mem 5 14) cl_8982 (by decide) v hb
def cl_8983 : CNF.NClause := [(280,true),(287,true),(289,true),(296,true),(303,false),(306,true)]
theorem inp_8983 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8983 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 14) (closed_mem 5 14) cl_8983 (by decide) v hb
def cl_8984 : CNF.NClause := [(280,true),(287,true),(289,true),(296,false),(303,true),(306,true)]
theorem inp_8984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8984 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 14) (closed_mem 5 14) cl_8984 (by decide) v hb
def cl_8987 : CNF.NClause := [(280,false),(287,true),(289,true),(296,true),(303,true),(306,true)]
theorem inp_8987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8987 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 14) (closed_mem 5 14) cl_8987 (by decide) v hb
def cl_8989 : CNF.NClause := [(294,true),(295,true),(296,true),(297,true),(298,false),(309,true)]
theorem inp_8989 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8989 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_8989 v hb
def cl_8990 : CNF.NClause := [(294,true),(295,true),(296,true),(297,false),(298,true),(309,true)]
theorem inp_8990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8990 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 15) (closed_mem 5 15) cl_8990 (by decide) v hb
def cl_8991 : CNF.NClause := [(294,true),(295,true),(296,false),(297,true),(298,true),(309,true)]
theorem inp_8991 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8991 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 15) (closed_mem 5 15) cl_8991 (by decide) v hb
def cl_8992 : CNF.NClause := [(294,true),(295,false),(296,true),(297,true),(298,true),(309,true)]
theorem inp_8992 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8992 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 15) (closed_mem 5 15) cl_8992 (by decide) v hb
def cl_8993 : CNF.NClause := [(294,false),(295,true),(296,true),(297,true),(298,true),(309,true)]
theorem inp_8993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8993 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 15) (closed_mem 5 15) cl_8993 (by decide) v hb
def cl_8995 : CNF.NClause := [(283,true),(285,true),(292,true),(294,true),(301,false),(306,true)]
theorem inp_8995 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8995 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 16) (closed_mem 5 16) cl_8995 (by decide) v hb
def cl_8996 : CNF.NClause := [(283,true),(285,true),(292,true),(294,false),(301,true),(306,true)]
theorem inp_8996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8996 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 16) (closed_mem 5 16) cl_8996 (by decide) v hb
def cl_8997 : CNF.NClause := [(283,true),(285,true),(292,false),(294,true),(301,true),(306,true)]
theorem inp_8997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8997 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 16) (closed_mem 5 16) cl_8997 (by decide) v hb
def cl_8998 : CNF.NClause := [(283,true),(285,false),(292,true),(294,true),(301,true),(306,true)]
theorem inp_8998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8998 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_8998 v hb
def cl_9002 : CNF.NClause := [(281,true),(287,true),(293,true),(294,false),(300,true),(305,true)]
theorem inp_9002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9002 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 17) (closed_mem 5 17) cl_9002 (by decide) v hb
def cl_9005 : CNF.NClause := [(281,false),(287,true),(293,true),(294,true),(300,true),(305,true)]
theorem inp_9005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9005 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 17) (closed_mem 5 17) cl_9005 (by decide) v hb
def cl_9007 : CNF.NClause := [(282,true),(286,true),(290,true),(294,true),(303,false),(308,true)]
theorem inp_9007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9007 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 18) (closed_mem 5 18) cl_9007 (by decide) v hb
def cl_9008 : CNF.NClause := [(282,true),(286,true),(290,true),(294,false),(303,true),(308,true)]
theorem inp_9008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9008 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 18) (closed_mem 5 18) cl_9008 (by decide) v hb
def cl_9011 : CNF.NClause := [(282,false),(286,true),(290,true),(294,true),(303,true),(308,true)]
theorem inp_9011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9011 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 18) (closed_mem 5 18) cl_9011 (by decide) v hb
def cl_9012 : CNF.NClause := [(280,true),(288,true),(291,true),(294,true),(302,true),(307,false)]
theorem inp_9012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9012 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 19) (closed_mem 5 19) cl_9012 (by decide) v hb
def cl_9014 : CNF.NClause := [(280,true),(288,true),(291,true),(294,false),(302,true),(307,true)]
theorem inp_9014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9014 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 19) (closed_mem 5 19) cl_9014 (by decide) v hb
def cl_9016 : CNF.NClause := [(280,true),(288,false),(291,true),(294,true),(302,true),(307,true)]
theorem inp_9016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9016 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 19) (closed_mem 5 19) cl_9016 (by decide) v hb
def cl_9023 : CNF.NClause := [(284,false),(285,true),(286,true),(287,true),(288,true),(309,true)]
theorem inp_9023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9023 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 20) (closed_mem 5 20) cl_9023 (by decide) v hb
def cl_9028 : CNF.NClause := [(283,true),(284,false),(290,true),(296,true),(302,true),(305,true)]
theorem inp_9028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9028 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 21) (closed_mem 5 21) cl_9028 (by decide) v hb
def cl_9034 : CNF.NClause := [(281,true),(284,false),(292,true),(295,true),(303,true),(307,true)]
theorem inp_9034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9034 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 22) (closed_mem 5 22) cl_9034 (by decide) v hb
def cl_9040 : CNF.NClause := [(282,true),(284,false),(291,true),(298,true),(300,true),(306,true)]
theorem inp_9040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9040 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9040 v hb
def cl_9046 : CNF.NClause := [(280,true),(284,false),(293,true),(297,true),(301,true),(308,true)]
theorem inp_9046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9046 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 24) (closed_mem 5 24) cl_9046 (by decide) v hb
def cl_9049 : CNF.NClause := [(279,true),(280,true),(281,true),(282,true),(283,false),(309,true)]
theorem inp_9049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9049 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 25) (closed_mem 5 25) cl_9049 (by decide) v hb
def cl_9050 : CNF.NClause := [(279,true),(280,true),(281,true),(282,false),(283,true),(309,true)]
theorem inp_9050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9050 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 25) (closed_mem 5 25) cl_9050 (by decide) v hb
def cl_9051 : CNF.NClause := [(279,true),(280,true),(281,false),(282,true),(283,true),(309,true)]
theorem inp_9051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9051 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 25) (closed_mem 5 25) cl_9051 (by decide) v hb
def cl_9052 : CNF.NClause := [(279,true),(280,false),(281,true),(282,true),(283,true),(309,true)]
theorem inp_9052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9052 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 25) (closed_mem 5 25) cl_9052 (by decide) v hb
def cl_9055 : CNF.NClause := [(279,true),(288,true),(292,true),(296,true),(300,false),(308,true)]
theorem inp_9055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9055 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 26) (closed_mem 5 26) cl_9055 (by decide) v hb
def cl_9056 : CNF.NClause := [(279,true),(288,true),(292,true),(296,false),(300,true),(308,true)]
theorem inp_9056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9056 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 26) (closed_mem 5 26) cl_9056 (by decide) v hb
def cl_9057 : CNF.NClause := [(279,true),(288,true),(292,false),(296,true),(300,true),(308,true)]
theorem inp_9057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9057 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 26) (closed_mem 5 26) cl_9057 (by decide) v hb
def cl_9058 : CNF.NClause := [(279,true),(288,false),(292,true),(296,true),(300,true),(308,true)]
theorem inp_9058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9058 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9058 v hb
def cl_9060 : CNF.NClause := [(279,true),(286,true),(293,true),(295,true),(302,true),(306,false)]
theorem inp_9060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9060 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 27) (closed_mem 5 27) cl_9060 (by decide) v hb
def cl_9061 : CNF.NClause := [(279,true),(286,true),(293,true),(295,true),(302,false),(306,true)]
theorem inp_9061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9061 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 27) (closed_mem 5 27) cl_9061 (by decide) v hb
def cl_9062 : CNF.NClause := [(279,true),(286,true),(293,true),(295,false),(302,true),(306,true)]
theorem inp_9062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9062 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 27) (closed_mem 5 27) cl_9062 (by decide) v hb
def cl_9063 : CNF.NClause := [(279,true),(286,true),(293,false),(295,true),(302,true),(306,true)]
theorem inp_9063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9063 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 27) (closed_mem 5 27) cl_9063 (by decide) v hb
def cl_9064 : CNF.NClause := [(279,true),(286,false),(293,true),(295,true),(302,true),(306,true)]
theorem inp_9064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9064 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 27) (closed_mem 5 27) cl_9064 (by decide) v hb
def cl_9067 : CNF.NClause := [(279,true),(287,true),(290,true),(298,true),(301,false),(307,true)]
theorem inp_9067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9067 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 28) (closed_mem 5 28) cl_9067 (by decide) v hb
def cl_9068 : CNF.NClause := [(279,true),(287,true),(290,true),(298,false),(301,true),(307,true)]
theorem inp_9068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9068 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 28) (closed_mem 5 28) cl_9068 (by decide) v hb
def cl_9069 : CNF.NClause := [(279,true),(287,true),(290,false),(298,true),(301,true),(307,true)]
theorem inp_9069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9069 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9069 v hb
end Percolation.NReplay
