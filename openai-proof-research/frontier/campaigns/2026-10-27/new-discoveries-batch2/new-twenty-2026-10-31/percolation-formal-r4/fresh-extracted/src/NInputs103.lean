import NInputs102
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_5924 : CNF.NClause := [(46,false),(15,true),(77,true),(78,false),(79,false),(80,false),(81,true),(92,false)]
theorem inp_5924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5924 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5924 (by decide) v hb
def cl_5925 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(79,false),(80,false),(81,true),(92,false)]
theorem inp_5925 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5925 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5925 (by decide) v hb
def cl_5926 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(79,false),(80,false),(81,true),(92,false)]
theorem inp_5926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5926 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5926 (by decide) v hb
def cl_5927 : CNF.NClause := [(46,false),(15,false),(77,true),(78,true),(79,false),(80,false),(81,true),(92,false)]
theorem inp_5927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5927 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5927 (by decide) v hb
def cl_5928 : CNF.NClause := [(46,false),(15,true),(77,true),(78,true),(79,false),(80,false),(81,true),(92,false)]
theorem inp_5928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5928 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5928 (by decide) v hb
def cl_5929 : CNF.NClause := [(46,false),(15,false),(77,false),(78,false),(79,true),(80,false),(81,true),(92,false)]
theorem inp_5929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5929 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5929 (by decide) v hb
def cl_5930 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,true),(80,false),(81,true),(92,false)]
theorem inp_5930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5930 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5930 (by decide) v hb
def cl_5931 : CNF.NClause := [(46,false),(15,false),(77,true),(78,false),(79,true),(80,false),(81,true),(92,false)]
theorem inp_5931 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5931 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5931 (by decide) v hb
def cl_5932 : CNF.NClause := [(46,false),(15,true),(77,true),(78,false),(79,true),(80,false),(81,true),(92,false)]
theorem inp_5932 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5932 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5932 (by decide) v hb
def cl_5933 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(79,true),(80,false),(81,true),(92,false)]
theorem inp_5933 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5933 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5933 (by decide) v hb
def cl_5934 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(79,true),(80,false),(81,true),(92,false)]
theorem inp_5934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5934 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5934 (by decide) v hb
def cl_5935 : CNF.NClause := [(46,false),(15,false),(77,true),(78,true),(79,true),(80,false),(81,true),(92,false)]
theorem inp_5935 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5935 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5935 (by decide) v hb
def cl_5936 : CNF.NClause := [(46,false),(15,true),(77,true),(78,true),(79,true),(80,false),(81,true),(92,false)]
theorem inp_5936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5936 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5936 (by decide) v hb
def cl_5937 : CNF.NClause := [(46,false),(15,false),(77,false),(78,false),(79,false),(80,true),(81,true),(92,false)]
theorem inp_5937 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5937 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5937 (by decide) v hb
def cl_5938 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,false),(80,true),(81,true),(92,false)]
theorem inp_5938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5938 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5938 (by decide) v hb
def cl_5939 : CNF.NClause := [(46,false),(15,false),(77,true),(78,false),(79,false),(80,true),(81,true),(92,false)]
theorem inp_5939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5939 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5939 (by decide) v hb
def cl_5940 : CNF.NClause := [(46,false),(15,true),(77,true),(78,false),(79,false),(80,true),(81,true),(92,false)]
theorem inp_5940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5940 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5940 (by decide) v hb
def cl_5941 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(79,false),(80,true),(81,true),(92,false)]
theorem inp_5941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5941 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5941 (by decide) v hb
def cl_5942 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(79,false),(80,true),(81,true),(92,false)]
theorem inp_5942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5942 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5942 (by decide) v hb
def cl_5943 : CNF.NClause := [(46,false),(15,false),(77,true),(78,true),(79,false),(80,true),(81,true),(92,false)]
theorem inp_5943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5943 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5943 (by decide) v hb
def cl_5944 : CNF.NClause := [(46,false),(15,true),(77,true),(78,true),(79,false),(80,true),(81,true),(92,false)]
theorem inp_5944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5944 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5944 (by decide) v hb
def cl_5945 : CNF.NClause := [(46,false),(15,false),(77,false),(78,false),(79,true),(80,true),(81,true),(92,false)]
theorem inp_5945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5945 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5945 (by decide) v hb
def cl_5946 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,true),(80,true),(81,true),(92,false)]
theorem inp_5946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5946 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5946 (by decide) v hb
def cl_5947 : CNF.NClause := [(46,false),(15,false),(77,true),(78,false),(79,true),(80,true),(81,true),(92,false)]
theorem inp_5947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5947 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5947 (by decide) v hb
def cl_5948 : CNF.NClause := [(46,false),(15,true),(77,true),(78,false),(79,true),(80,true),(81,true),(92,false)]
theorem inp_5948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5948 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5948 (by decide) v hb
def cl_5949 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(79,true),(80,true),(81,true),(92,false)]
theorem inp_5949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5949 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5949 (by decide) v hb
def cl_5950 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(79,true),(80,true),(81,true),(92,false)]
theorem inp_5950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5950 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5950 (by decide) v hb
def cl_5951 : CNF.NClause := [(46,false),(15,false),(77,true),(78,true),(79,true),(80,true),(81,true),(92,false)]
theorem inp_5951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5951 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5951 (by decide) v hb
def cl_5952 : CNF.NClause := [(46,false),(15,true),(77,true),(78,true),(79,true),(80,true),(81,true),(92,false)]
theorem inp_5952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5952 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5952 (by decide) v hb
def cl_5953 : CNF.NClause := [(46,false),(15,false),(77,false),(78,false),(79,false),(80,false),(81,false),(92,true)]
theorem inp_5953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5953 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5953 v hb
def cl_5954 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,false),(80,false),(81,false),(92,true)]
theorem inp_5954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5954 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5954 v hb
def cl_5955 : CNF.NClause := [(46,false),(15,false),(77,true),(78,false),(79,false),(80,false),(81,false),(92,true)]
theorem inp_5955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5955 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5955 (by decide) v hb
def cl_5956 : CNF.NClause := [(46,false),(15,true),(77,true),(78,false),(79,false),(80,false),(81,false),(92,true)]
theorem inp_5956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5956 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5956 (by decide) v hb
def cl_5957 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(79,false),(80,false),(81,false),(92,true)]
theorem inp_5957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5957 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5957 (by decide) v hb
def cl_5958 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(79,false),(80,false),(81,false),(92,true)]
theorem inp_5958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5958 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5958 (by decide) v hb
def cl_5959 : CNF.NClause := [(46,false),(15,false),(77,true),(78,true),(79,false),(80,false),(81,false),(92,true)]
theorem inp_5959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5959 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5959 (by decide) v hb
def cl_5960 : CNF.NClause := [(46,false),(15,true),(77,true),(78,true),(79,false),(80,false),(81,false),(92,true)]
theorem inp_5960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5960 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5960 (by decide) v hb
def cl_5961 : CNF.NClause := [(46,false),(15,false),(77,false),(78,false),(79,true),(80,false),(81,false),(92,true)]
theorem inp_5961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5961 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5961 (by decide) v hb
def cl_5962 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,true),(80,false),(81,false),(92,true)]
theorem inp_5962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5962 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5962 (by decide) v hb
def cl_5963 : CNF.NClause := [(46,false),(15,false),(77,true),(78,false),(79,true),(80,false),(81,false),(92,true)]
theorem inp_5963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5963 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5963 (by decide) v hb
def cl_5964 : CNF.NClause := [(46,false),(15,true),(77,true),(78,false),(79,true),(80,false),(81,false),(92,true)]
theorem inp_5964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5964 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5964 (by decide) v hb
def cl_5965 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(79,true),(80,false),(81,false),(92,true)]
theorem inp_5965 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5965 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5965 (by decide) v hb
def cl_5966 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(79,true),(80,false),(81,false),(92,true)]
theorem inp_5966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5966 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5966 (by decide) v hb
def cl_5967 : CNF.NClause := [(46,false),(15,false),(77,true),(78,true),(79,true),(80,false),(81,false),(92,true)]
theorem inp_5967 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5967 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5967 (by decide) v hb
def cl_5968 : CNF.NClause := [(46,false),(15,true),(77,true),(78,true),(79,true),(80,false),(81,false),(92,true)]
theorem inp_5968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5968 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5968 (by decide) v hb
def cl_5969 : CNF.NClause := [(46,false),(15,false),(77,false),(78,false),(79,false),(80,true),(81,false),(92,true)]
theorem inp_5969 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5969 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5969 (by decide) v hb
def cl_5970 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,false),(80,true),(81,false),(92,true)]
theorem inp_5970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5970 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5970 v hb
def cl_5971 : CNF.NClause := [(46,false),(15,false),(77,true),(78,false),(79,false),(80,true),(81,false),(92,true)]
theorem inp_5971 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5971 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5971 (by decide) v hb
def cl_5972 : CNF.NClause := [(46,false),(15,true),(77,true),(78,false),(79,false),(80,true),(81,false),(92,true)]
theorem inp_5972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5972 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5972 (by decide) v hb
def cl_5973 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(79,false),(80,true),(81,false),(92,true)]
theorem inp_5973 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5973 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) cl_5973 (by decide) v hb
end Percolation.NReplay
