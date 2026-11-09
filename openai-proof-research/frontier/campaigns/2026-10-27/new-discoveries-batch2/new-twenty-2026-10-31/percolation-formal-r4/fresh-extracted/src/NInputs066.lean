import NInputs065
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_3953 : CNF.NClause := [(123,true),(31,false),(36,false),(41,false),(46,false),(51,true),(56,true)]
theorem inp_3953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3953 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3953 (by decide) v hb
def cl_3954 : CNF.NClause := [(123,true),(31,true),(36,false),(41,false),(46,false),(51,true),(56,true)]
theorem inp_3954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3954 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3954 (by decide) v hb
def cl_3955 : CNF.NClause := [(123,true),(31,false),(36,true),(41,false),(46,false),(51,true),(56,true)]
theorem inp_3955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3955 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3955 (by decide) v hb
def cl_3956 : CNF.NClause := [(123,true),(31,true),(36,true),(41,false),(46,false),(51,true),(56,true)]
theorem inp_3956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3956 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3956 (by decide) v hb
def cl_3957 : CNF.NClause := [(123,true),(31,false),(36,false),(41,true),(46,false),(51,true),(56,true)]
theorem inp_3957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3957 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3957 (by decide) v hb
def cl_3958 : CNF.NClause := [(123,true),(31,true),(36,false),(41,true),(46,false),(51,true),(56,true)]
theorem inp_3958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3958 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3958 (by decide) v hb
def cl_3959 : CNF.NClause := [(123,true),(31,false),(36,true),(41,true),(46,false),(51,true),(56,true)]
theorem inp_3959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3959 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3959 v hb
def cl_3960 : CNF.NClause := [(123,false),(31,true),(36,true),(41,true),(46,false),(51,true),(56,true)]
theorem inp_3960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3960 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3960 (by decide) v hb
def cl_3961 : CNF.NClause := [(123,true),(31,false),(36,false),(41,false),(46,true),(51,true),(56,true)]
theorem inp_3961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3961 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3961 (by decide) v hb
def cl_3962 : CNF.NClause := [(123,true),(31,true),(36,false),(41,false),(46,true),(51,true),(56,true)]
theorem inp_3962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3962 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3962 (by decide) v hb
def cl_3964 : CNF.NClause := [(123,false),(31,true),(36,true),(41,false),(46,true),(51,true),(56,true)]
theorem inp_3964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3964 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3964 (by decide) v hb
def cl_3966 : CNF.NClause := [(123,false),(31,true),(36,false),(41,true),(46,true),(51,true),(56,true)]
theorem inp_3966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3966 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3966 (by decide) v hb
def cl_3968 : CNF.NClause := [(123,false),(31,true),(36,true),(41,true),(46,true),(51,true),(56,true)]
theorem inp_3968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3968 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3968 (by decide) v hb
def cl_3970 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,false),(90,false),(91,false),(92,false)]
theorem inp_3970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3970 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3970 v hb
def cl_3972 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,false),(90,false),(91,false),(92,false)]
theorem inp_3972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3972 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3972 v hb
def cl_3974 : CNF.NClause := [(31,false),(0,true),(87,false),(88,true),(89,false),(90,false),(91,false),(92,false)]
theorem inp_3974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3974 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3974 v hb
def cl_3976 : CNF.NClause := [(31,false),(0,true),(87,true),(88,true),(89,false),(90,false),(91,false),(92,false)]
theorem inp_3976 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3976 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3976 v hb
def cl_3978 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,true),(90,false),(91,false),(92,false)]
theorem inp_3978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3978 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3978 v hb
def cl_3980 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,true),(90,false),(91,false),(92,false)]
theorem inp_3980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3980 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3980 v hb
def cl_3982 : CNF.NClause := [(31,false),(0,true),(87,false),(88,true),(89,true),(90,false),(91,false),(92,false)]
theorem inp_3982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3982 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_3982 (by decide) v hb
def cl_3984 : CNF.NClause := [(31,false),(0,true),(87,true),(88,true),(89,true),(90,false),(91,false),(92,false)]
theorem inp_3984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3984 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_3984 (by decide) v hb
def cl_3986 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,false),(90,true),(91,false),(92,false)]
theorem inp_3986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3986 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_3986 (by decide) v hb
def cl_3988 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,false),(90,true),(91,false),(92,false)]
theorem inp_3988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3988 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_3988 (by decide) v hb
def cl_3990 : CNF.NClause := [(31,false),(0,true),(87,false),(88,true),(89,false),(90,true),(91,false),(92,false)]
theorem inp_3990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3990 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_3990 (by decide) v hb
def cl_3992 : CNF.NClause := [(31,false),(0,true),(87,true),(88,true),(89,false),(90,true),(91,false),(92,false)]
theorem inp_3992 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3992 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_3992 (by decide) v hb
def cl_3994 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,true),(90,true),(91,false),(92,false)]
theorem inp_3994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3994 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_3994 (by decide) v hb
def cl_3996 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,true),(90,true),(91,false),(92,false)]
theorem inp_3996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3996 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_3996 (by decide) v hb
def cl_3998 : CNF.NClause := [(31,false),(0,true),(87,false),(88,true),(89,true),(90,true),(91,false),(92,false)]
theorem inp_3998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3998 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_3998 (by decide) v hb
def cl_4000 : CNF.NClause := [(31,false),(0,true),(87,true),(88,true),(89,true),(90,true),(91,false),(92,false)]
theorem inp_4000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4000 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4000 (by decide) v hb
def cl_4002 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,false),(90,false),(91,true),(92,false)]
theorem inp_4002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4002 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4002 (by decide) v hb
def cl_4004 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,false),(90,false),(91,true),(92,false)]
theorem inp_4004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4004 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4004 (by decide) v hb
def cl_4006 : CNF.NClause := [(31,false),(0,true),(87,false),(88,true),(89,false),(90,false),(91,true),(92,false)]
theorem inp_4006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4006 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4006 (by decide) v hb
def cl_4008 : CNF.NClause := [(31,false),(0,true),(87,true),(88,true),(89,false),(90,false),(91,true),(92,false)]
theorem inp_4008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4008 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4008 (by decide) v hb
def cl_4010 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,true),(90,false),(91,true),(92,false)]
theorem inp_4010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4010 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4010 (by decide) v hb
def cl_4012 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,true),(90,false),(91,true),(92,false)]
theorem inp_4012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4012 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4012 (by decide) v hb
def cl_4014 : CNF.NClause := [(31,false),(0,true),(87,false),(88,true),(89,true),(90,false),(91,true),(92,false)]
theorem inp_4014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4014 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4014 (by decide) v hb
def cl_4016 : CNF.NClause := [(31,false),(0,true),(87,true),(88,true),(89,true),(90,false),(91,true),(92,false)]
theorem inp_4016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4016 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4016 (by decide) v hb
def cl_4018 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,false),(90,true),(91,true),(92,false)]
theorem inp_4018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4018 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4018 (by decide) v hb
def cl_4020 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,false),(90,true),(91,true),(92,false)]
theorem inp_4020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4020 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4020 (by decide) v hb
def cl_4022 : CNF.NClause := [(31,false),(0,true),(87,false),(88,true),(89,false),(90,true),(91,true),(92,false)]
theorem inp_4022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4022 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4022 (by decide) v hb
def cl_4024 : CNF.NClause := [(31,false),(0,true),(87,true),(88,true),(89,false),(90,true),(91,true),(92,false)]
theorem inp_4024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4024 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4024 (by decide) v hb
def cl_4026 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,true),(90,true),(91,true),(92,false)]
theorem inp_4026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4026 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4026 (by decide) v hb
def cl_4028 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,true),(90,true),(91,true),(92,false)]
theorem inp_4028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4028 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4028 (by decide) v hb
def cl_4030 : CNF.NClause := [(31,false),(0,true),(87,false),(88,true),(89,true),(90,true),(91,true),(92,false)]
theorem inp_4030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4030 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4030 (by decide) v hb
def cl_4032 : CNF.NClause := [(31,false),(0,true),(87,true),(88,true),(89,true),(90,true),(91,true),(92,false)]
theorem inp_4032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4032 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4032 (by decide) v hb
def cl_4034 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,false),(90,false),(91,false),(92,true)]
theorem inp_4034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4034 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4034 v hb
def cl_4036 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,false),(90,false),(91,false),(92,true)]
theorem inp_4036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4036 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4036 (by decide) v hb
def cl_4038 : CNF.NClause := [(31,false),(0,true),(87,false),(88,true),(89,false),(90,false),(91,false),(92,true)]
theorem inp_4038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4038 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4038 (by decide) v hb
def cl_4040 : CNF.NClause := [(31,false),(0,true),(87,true),(88,true),(89,false),(90,false),(91,false),(92,true)]
theorem inp_4040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4040 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4040 (by decide) v hb
def cl_4042 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,true),(90,false),(91,false),(92,true)]
theorem inp_4042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4042 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4042 (by decide) v hb
end Percolation.NReplay
