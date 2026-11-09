import NInputs083
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_4940 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,true),(80,false),(82,false),(89,true)]
theorem inp_4940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4940 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4940 (by decide) v hb
def cl_4941 : CNF.NClause := [(38,false),(7,false),(64,false),(71,true),(73,true),(80,false),(82,false),(89,true)]
theorem inp_4941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4941 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4941 (by decide) v hb
def cl_4942 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,true),(80,false),(82,false),(89,true)]
theorem inp_4942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4942 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4942 (by decide) v hb
def cl_4943 : CNF.NClause := [(38,false),(7,false),(64,true),(71,true),(73,true),(80,false),(82,false),(89,true)]
theorem inp_4943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4943 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4943 (by decide) v hb
def cl_4944 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,true),(80,false),(82,false),(89,true)]
theorem inp_4944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4944 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4944 (by decide) v hb
def cl_4945 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,false),(80,true),(82,false),(89,true)]
theorem inp_4945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4945 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4945 (by decide) v hb
def cl_4946 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,false),(80,true),(82,false),(89,true)]
theorem inp_4946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4946 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4946 (by decide) v hb
def cl_4947 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,false),(80,true),(82,false),(89,true)]
theorem inp_4947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4947 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4947 (by decide) v hb
def cl_4948 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,false),(80,true),(82,false),(89,true)]
theorem inp_4948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4948 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4948 (by decide) v hb
def cl_4949 : CNF.NClause := [(38,false),(7,false),(64,false),(71,true),(73,false),(80,true),(82,false),(89,true)]
theorem inp_4949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4949 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4949 (by decide) v hb
def cl_4950 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,false),(80,true),(82,false),(89,true)]
theorem inp_4950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4950 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4950 (by decide) v hb
def cl_4951 : CNF.NClause := [(38,false),(7,false),(64,true),(71,true),(73,false),(80,true),(82,false),(89,true)]
theorem inp_4951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4951 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4951 (by decide) v hb
def cl_4952 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,false),(80,true),(82,false),(89,true)]
theorem inp_4952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4952 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4952 (by decide) v hb
def cl_4953 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,true),(80,true),(82,false),(89,true)]
theorem inp_4953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4953 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4953 (by decide) v hb
def cl_4954 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,true),(80,true),(82,false),(89,true)]
theorem inp_4954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4954 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4954 (by decide) v hb
def cl_4955 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,true),(80,true),(82,false),(89,true)]
theorem inp_4955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4955 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4955 (by decide) v hb
def cl_4956 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,true),(80,true),(82,false),(89,true)]
theorem inp_4956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4956 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4956 (by decide) v hb
def cl_4957 : CNF.NClause := [(38,false),(7,false),(64,false),(71,true),(73,true),(80,true),(82,false),(89,true)]
theorem inp_4957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4957 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4957 (by decide) v hb
def cl_4958 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,true),(80,true),(82,false),(89,true)]
theorem inp_4958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4958 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4958 (by decide) v hb
def cl_4959 : CNF.NClause := [(38,false),(7,false),(64,true),(71,true),(73,true),(80,true),(82,false),(89,true)]
theorem inp_4959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4959 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4959 (by decide) v hb
def cl_4960 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,true),(80,true),(82,false),(89,true)]
theorem inp_4960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4960 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4960 (by decide) v hb
def cl_4961 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,false),(80,false),(82,true),(89,true)]
theorem inp_4961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4961 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4961 (by decide) v hb
def cl_4962 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,false),(80,false),(82,true),(89,true)]
theorem inp_4962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4962 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4962 v hb
def cl_4963 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,false),(80,false),(82,true),(89,true)]
theorem inp_4963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4963 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4963 (by decide) v hb
def cl_4964 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,false),(80,false),(82,true),(89,true)]
theorem inp_4964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4964 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4964 (by decide) v hb
def cl_4965 : CNF.NClause := [(38,false),(7,false),(64,false),(71,true),(73,false),(80,false),(82,true),(89,true)]
theorem inp_4965 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4965 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4965 (by decide) v hb
def cl_4966 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,false),(80,false),(82,true),(89,true)]
theorem inp_4966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4966 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4966 v hb
def cl_4967 : CNF.NClause := [(38,false),(7,false),(64,true),(71,true),(73,false),(80,false),(82,true),(89,true)]
theorem inp_4967 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4967 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4967 (by decide) v hb
def cl_4968 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,false),(80,false),(82,true),(89,true)]
theorem inp_4968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4968 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4968 (by decide) v hb
def cl_4969 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,true),(80,false),(82,true),(89,true)]
theorem inp_4969 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4969 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4969 (by decide) v hb
def cl_4970 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,true),(80,false),(82,true),(89,true)]
theorem inp_4970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4970 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4970 v hb
def cl_4971 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,true),(80,false),(82,true),(89,true)]
theorem inp_4971 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4971 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4971 (by decide) v hb
def cl_4972 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,true),(80,false),(82,true),(89,true)]
theorem inp_4972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4972 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4972 (by decide) v hb
def cl_4973 : CNF.NClause := [(38,false),(7,false),(64,false),(71,true),(73,true),(80,false),(82,true),(89,true)]
theorem inp_4973 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4973 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4973 (by decide) v hb
def cl_4974 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,true),(80,false),(82,true),(89,true)]
theorem inp_4974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4974 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4974 (by decide) v hb
def cl_4975 : CNF.NClause := [(38,false),(7,false),(64,true),(71,true),(73,true),(80,false),(82,true),(89,true)]
theorem inp_4975 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4975 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4975 (by decide) v hb
def cl_4976 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,true),(80,false),(82,true),(89,true)]
theorem inp_4976 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4976 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4976 (by decide) v hb
def cl_4977 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,false),(80,true),(82,true),(89,true)]
theorem inp_4977 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4977 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4977 (by decide) v hb
def cl_4978 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,false),(80,true),(82,true),(89,true)]
theorem inp_4978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4978 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4978 v hb
def cl_4979 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,false),(80,true),(82,true),(89,true)]
theorem inp_4979 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4979 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4979 (by decide) v hb
def cl_4980 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,false),(80,true),(82,true),(89,true)]
theorem inp_4980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4980 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4980 (by decide) v hb
def cl_4981 : CNF.NClause := [(38,false),(7,false),(64,false),(71,true),(73,false),(80,true),(82,true),(89,true)]
theorem inp_4981 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4981 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4981 (by decide) v hb
def cl_4982 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,false),(80,true),(82,true),(89,true)]
theorem inp_4982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4982 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4982 (by decide) v hb
def cl_4984 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,false),(80,true),(82,true),(89,true)]
theorem inp_4984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4984 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4984 (by decide) v hb
def cl_4985 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,true),(80,true),(82,true),(89,true)]
theorem inp_4985 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4985 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4985 (by decide) v hb
def cl_4986 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,true),(80,true),(82,true),(89,true)]
theorem inp_4986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4986 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4986 v hb
def cl_4987 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,true),(80,true),(82,true),(89,true)]
theorem inp_4987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4987 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4987 (by decide) v hb
def cl_4988 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,true),(80,true),(82,true),(89,true)]
theorem inp_4988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4988 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4988 (by decide) v hb
def cl_4989 : CNF.NClause := [(38,false),(7,false),(64,false),(71,true),(73,true),(80,true),(82,true),(89,true)]
theorem inp_4989 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4989 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4989 (by decide) v hb
def cl_4990 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,true),(80,true),(82,true),(89,true)]
theorem inp_4990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4990 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4990 (by decide) v hb
end Percolation.NReplay
