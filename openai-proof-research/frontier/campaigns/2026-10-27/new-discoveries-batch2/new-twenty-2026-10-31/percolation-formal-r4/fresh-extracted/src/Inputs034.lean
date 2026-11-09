import Inputs033
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_3880 : CNF.NClause := [(122,true),(31,true),(37,true),(43,true),(49,false),(55,false),(57,true)]
theorem inp_3880 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3880 := by
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3880 (by decide) v h
def cl_3883 : CNF.NClause := [(122,true),(31,false),(37,true),(43,false),(49,true),(55,false),(57,true)]
theorem inp_3883 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3883 := by
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3883 (by decide) v h
def cl_3887 : CNF.NClause := [(122,true),(31,false),(37,true),(43,true),(49,true),(55,false),(57,true)]
theorem inp_3887 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3887 := by
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3887 (by decide) v h
def cl_3891 : CNF.NClause := [(122,true),(31,false),(37,true),(43,false),(49,false),(55,true),(57,true)]
theorem inp_3891 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3891 := by
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3891 (by decide) v h
def cl_3892 : CNF.NClause := [(122,true),(31,true),(37,true),(43,false),(49,false),(55,true),(57,true)]
theorem inp_3892 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3892 := by
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3892 (by decide) v h
def cl_3895 : CNF.NClause := [(122,true),(31,false),(37,true),(43,true),(49,false),(55,true),(57,true)]
theorem inp_3895 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3895 := by
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3895 (by decide) v h
def cl_3899 : CNF.NClause := [(122,true),(31,false),(37,true),(43,false),(49,true),(55,true),(57,true)]
theorem inp_3899 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3899 := by
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3899 (by decide) v h
def cl_3903 : CNF.NClause := [(122,false),(31,false),(37,true),(43,true),(49,true),(55,true),(57,true)]
theorem inp_3903 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3903 := by
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3903 (by decide) v h
def cl_3904 : CNF.NClause := [(122,false),(31,true),(37,true),(43,true),(49,true),(55,true),(57,true)]
theorem inp_3904 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3904 := by
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3904 (by decide) v h
def cl_3907 : CNF.NClause := [(123,true),(31,false),(36,true),(41,false),(46,false),(51,false),(56,false)]
theorem inp_3907 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3907 := by
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3907 (by decide) v h
def cl_3908 : CNF.NClause := [(123,true),(31,true),(36,true),(41,false),(46,false),(51,false),(56,false)]
theorem inp_3908 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3908 := by
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3908 (by decide) v h
def cl_3911 : CNF.NClause := [(123,true),(31,false),(36,true),(41,true),(46,false),(51,false),(56,false)]
theorem inp_3911 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3911 := by
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3911 (by decide) v h
def cl_3912 : CNF.NClause := [(123,true),(31,true),(36,true),(41,true),(46,false),(51,false),(56,false)]
theorem inp_3912 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3912 := by
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3912 (by decide) v h
def cl_3915 : CNF.NClause := [(123,true),(31,false),(36,true),(41,false),(46,true),(51,false),(56,false)]
theorem inp_3915 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3915 := by
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3915 (by decide) v h
def cl_3919 : CNF.NClause := [(123,true),(31,false),(36,true),(41,true),(46,true),(51,false),(56,false)]
theorem inp_3919 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3919 := by
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3919 (by decide) v h
def cl_3920 : CNF.NClause := [(123,true),(31,true),(36,true),(41,true),(46,true),(51,false),(56,false)]
theorem inp_3920 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3920 := by
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3920 (by decide) v h
def cl_3923 : CNF.NClause := [(123,true),(31,false),(36,true),(41,false),(46,false),(51,true),(56,false)]
theorem inp_3923 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3923 := by
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3923 (by decide) v h
def cl_3924 : CNF.NClause := [(123,true),(31,true),(36,true),(41,false),(46,false),(51,true),(56,false)]
theorem inp_3924 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3924 := by
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3924 (by decide) v h
def cl_3927 : CNF.NClause := [(123,true),(31,false),(36,true),(41,true),(46,false),(51,true),(56,false)]
theorem inp_3927 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3927 := by
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3927 (by decide) v h
def cl_3928 : CNF.NClause := [(123,true),(31,true),(36,true),(41,true),(46,false),(51,true),(56,false)]
theorem inp_3928 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3928 := by
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3928 (by decide) v h
def cl_3935 : CNF.NClause := [(123,true),(31,false),(36,true),(41,true),(46,true),(51,true),(56,false)]
theorem inp_3935 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3935 := by
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3935 (by decide) v h
def cl_3943 : CNF.NClause := [(123,true),(31,false),(36,true),(41,true),(46,false),(51,false),(56,true)]
theorem inp_3943 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3943 := by
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3943 (by decide) v h
def cl_3944 : CNF.NClause := [(123,true),(31,true),(36,true),(41,true),(46,false),(51,false),(56,true)]
theorem inp_3944 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3944 := by
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3944 (by decide) v h
def cl_3951 : CNF.NClause := [(123,true),(31,false),(36,true),(41,true),(46,true),(51,false),(56,true)]
theorem inp_3951 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3951 := by
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3951 (by decide) v h
def cl_3959 : CNF.NClause := [(123,true),(31,false),(36,true),(41,true),(46,false),(51,true),(56,true)]
theorem inp_3959 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3959 := by
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3959 (by decide) v h
def cl_3970 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,false),(90,false),(91,false),(92,false)]
theorem inp_3970 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3970 := by
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_3970 (by decide) v h
def cl_3971 : CNF.NClause := [(31,false),(0,false),(87,true),(88,false),(89,false),(90,false),(91,false),(92,false)]
theorem inp_3971 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3971 := by
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_3971 (by decide) v h
def cl_3972 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,false),(90,false),(91,false),(92,false)]
theorem inp_3972 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3972 := by
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_3972 (by decide) v h
def cl_3974 : CNF.NClause := [(31,false),(0,true),(87,false),(88,true),(89,false),(90,false),(91,false),(92,false)]
theorem inp_3974 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3974 := by
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_3974 (by decide) v h
def cl_3976 : CNF.NClause := [(31,false),(0,true),(87,true),(88,true),(89,false),(90,false),(91,false),(92,false)]
theorem inp_3976 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3976 := by
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_3976 (by decide) v h
def cl_3978 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,true),(90,false),(91,false),(92,false)]
theorem inp_3978 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3978 := by
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_3978 (by decide) v h
def cl_3980 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,true),(90,false),(91,false),(92,false)]
theorem inp_3980 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3980 := by
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_3980 (by decide) v h
def cl_4003 : CNF.NClause := [(31,false),(0,false),(87,true),(88,false),(89,false),(90,false),(91,true),(92,false)]
theorem inp_4003 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4003 := by
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4003 (by decide) v h
def cl_4034 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,false),(90,false),(91,false),(92,true)]
theorem inp_4034 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4034 := by
  exact input_gate (spreadGate5 0) (spread_mem 0) cl_4034 (by decide) v h
def cl_4097 : CNF.NClause := [(32,true),(1,false),(66,false),(71,false),(76,false),(81,false),(86,false),(87,false)]
theorem inp_4097 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4097 := by
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4097 (by decide) v h
def cl_4098 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,false),(81,false),(86,false),(87,false)]
theorem inp_4098 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4098 := by
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4098 (by decide) v h
def cl_4105 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,true),(81,false),(86,false),(87,false)]
theorem inp_4105 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4105 := by
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4105 (by decide) v h
def cl_4106 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,true),(81,false),(86,false),(87,false)]
theorem inp_4106 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4106 := by
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4106 (by decide) v h
def cl_4162 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,false),(81,false),(86,false),(87,true)]
theorem inp_4162 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4162 := by
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4162 (by decide) v h
def cl_4169 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,true),(81,false),(86,false),(87,true)]
theorem inp_4169 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4169 := by
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4169 (by decide) v h
def cl_4170 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,true),(81,false),(86,false),(87,true)]
theorem inp_4170 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4170 := by
  exact input_gate (spreadGate5 1) (spread_mem 1) cl_4170 (by decide) v h
def cl_4226 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,false),(79,false),(84,false),(87,false)]
theorem inp_4226 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4226 := by
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4226 (by decide) v h
def cl_4241 : CNF.NClause := [(33,false),(2,false),(64,false),(69,false),(74,false),(79,true),(84,false),(87,false)]
theorem inp_4241 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4241 := by
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4241 (by decide) v h
def cl_4243 : CNF.NClause := [(33,false),(2,false),(64,true),(69,false),(74,false),(79,true),(84,false),(87,false)]
theorem inp_4243 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4243 := by
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4243 (by decide) v h
def cl_4257 : CNF.NClause := [(33,false),(2,false),(64,false),(69,false),(74,false),(79,false),(84,true),(87,false)]
theorem inp_4257 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4257 := by
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4257 (by decide) v h
def cl_4258 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,false),(79,false),(84,true),(87,false)]
theorem inp_4258 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4258 := by
  exact input_gate (spreadGate5 2) (spread_mem 2) cl_4258 (by decide) v h
def cl_4354 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,false),(80,false),(85,false),(87,false)]
theorem inp_4354 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4354 := by
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4354 (by decide) v h
def cl_4362 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,true),(80,false),(85,false),(87,false)]
theorem inp_4362 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4362 := by
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4362 (by decide) v h
def cl_4364 : CNF.NClause := [(34,false),(3,true),(65,true),(70,false),(75,true),(80,false),(85,false),(87,false)]
theorem inp_4364 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4364 := by
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4364 (by decide) v h
def cl_4378 : CNF.NClause := [(34,false),(3,true),(65,false),(70,false),(75,true),(80,true),(85,false),(87,false)]
theorem inp_4378 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4378 := by
  exact input_gate (spreadGate5 3) (spread_mem 3) cl_4378 (by decide) v h
end Percolation.Replay
