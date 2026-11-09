import Inputs039
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_8697 : CNF.NClause := [(217,true),(225,true),(228,false),(236,true),(239,true),(245,true)]
theorem inp_8697 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8697 := by
  exact input_gate (closedGate5 3 28) (closed_mem 3 28) cl_8697 (by decide) v h
def cl_8908 : CNF.NClause := [(283,true),(288,false),(293,true),(298,true),(303,true),(304,true)]
theorem inp_8908 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8908 := by
  exact input_gate (closedGate5 5 1) (closed_mem 5 1) cl_8908 (by decide) v h
def cl_8918 : CNF.NClause := [(282,true),(287,true),(292,true),(297,false),(302,true),(304,true)]
theorem inp_8918 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8918 := by
  exact input_gate (closedGate5 5 3) (closed_mem 5 3) cl_8918 (by decide) v h
def cl_8919 : CNF.NClause := [(282,true),(287,true),(292,false),(297,true),(302,true),(304,true)]
theorem inp_8919 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8919 := by
  exact input_gate (closedGate5 5 3) (closed_mem 5 3) cl_8919 (by decide) v h
def cl_8941 : CNF.NClause := [(281,true),(288,true),(290,true),(297,true),(299,false),(306,true)]
theorem inp_8941 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8941 := by
  exact input_gate (closedGate5 5 7) (closed_mem 5 7) cl_8941 (by decide) v h
def cl_8954 : CNF.NClause := [(280,true),(286,true),(292,true),(298,false),(299,true),(305,true)]
theorem inp_8954 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8954 := by
  exact input_gate (closedGate5 5 9) (closed_mem 5 9) cl_8954 (by decide) v h
def cl_8969 : CNF.NClause := [(283,false),(286,true),(289,true),(297,true),(300,true),(307,true)]
theorem inp_8969 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8969 := by
  exact input_gate (closedGate5 5 11) (closed_mem 5 11) cl_8969 (by decide) v h
def cl_8974 : CNF.NClause := [(281,true),(285,false),(289,true),(298,true),(302,true),(308,true)]
theorem inp_8974 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8974 := by
  exact input_gate (closedGate5 5 12) (closed_mem 5 12) cl_8974 (by decide) v h
def cl_8975 : CNF.NClause := [(281,false),(285,true),(289,true),(298,true),(302,true),(308,true)]
theorem inp_8975 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8975 := by
  exact input_gate (closedGate5 5 12) (closed_mem 5 12) cl_8975 (by decide) v h
def cl_8989 : CNF.NClause := [(294,true),(295,true),(296,true),(297,true),(298,false),(309,true)]
theorem inp_8989 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8989 := by
  exact input_gate (closedGate5 5 15) (closed_mem 5 15) cl_8989 (by decide) v h
def cl_8998 : CNF.NClause := [(283,true),(285,false),(292,true),(294,true),(301,true),(306,true)]
theorem inp_8998 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8998 := by
  exact input_gate (closedGate5 5 16) (closed_mem 5 16) cl_8998 (by decide) v h
def cl_9000 : CNF.NClause := [(281,true),(287,true),(293,true),(294,true),(300,true),(305,false)]
theorem inp_9000 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9000 := by
  exact input_gate (closedGate5 5 17) (closed_mem 5 17) cl_9000 (by decide) v h
def cl_9006 : CNF.NClause := [(282,true),(286,true),(290,true),(294,true),(303,true),(308,false)]
theorem inp_9006 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9006 := by
  exact input_gate (closedGate5 5 18) (closed_mem 5 18) cl_9006 (by decide) v h
def cl_9015 : CNF.NClause := [(280,true),(288,true),(291,false),(294,true),(302,true),(307,true)]
theorem inp_9015 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9015 := by
  exact input_gate (closedGate5 5 19) (closed_mem 5 19) cl_9015 (by decide) v h
def cl_9040 : CNF.NClause := [(282,true),(284,false),(291,true),(298,true),(300,true),(306,true)]
theorem inp_9040 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9040 := by
  exact input_gate (closedGate5 5 23) (closed_mem 5 23) cl_9040 (by decide) v h
def cl_9053 : CNF.NClause := [(279,false),(280,true),(281,true),(282,true),(283,true),(309,true)]
theorem inp_9053 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9053 := by
  exact input_gate (closedGate5 5 25) (closed_mem 5 25) cl_9053 (by decide) v h
def cl_9058 : CNF.NClause := [(279,true),(288,false),(292,true),(296,true),(300,true),(308,true)]
theorem inp_9058 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9058 := by
  exact input_gate (closedGate5 5 26) (closed_mem 5 26) cl_9058 (by decide) v h
def cl_9069 : CNF.NClause := [(279,true),(287,true),(290,false),(298,true),(301,true),(307,true)]
theorem inp_9069 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9069 := by
  exact input_gate (closedGate5 5 28) (closed_mem 5 28) cl_9069 (by decide) v h
def cl_9072 : CNF.NClause := [(279,true),(285,true),(291,true),(297,true),(303,true),(305,false)]
theorem inp_9072 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9072 := by
  exact input_gate (closedGate5 5 29) (closed_mem 5 29) cl_9072 (by decide) v h
def cl_9073 : CNF.NClause := [(279,true),(285,true),(291,true),(297,true),(303,false),(305,true)]
theorem inp_9073 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9073 := by
  exact input_gate (closedGate5 5 29) (closed_mem 5 29) cl_9073 (by decide) v h
def cl_9075 : CNF.NClause := [(279,true),(285,true),(291,false),(297,true),(303,true),(305,true)]
theorem inp_9075 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9075 := by
  exact input_gate (closedGate5 5 29) (closed_mem 5 29) cl_9075 (by decide) v h
def cl_9272 : CNF.NClause := [(366,true),(367,true),(368,true),(369,false),(370,true),(371,true)]
theorem inp_9272 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9272 := by
  exact input_gate (closedGate5 7 0) (closed_mem 7 0) cl_9272 (by decide) v h
def cl_9279 : CNF.NClause := [(345,true),(350,true),(355,false),(360,true),(365,true),(366,true)]
theorem inp_9279 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9279 := by
  exact input_gate (closedGate5 7 1) (closed_mem 7 1) cl_9279 (by decide) v h
def cl_9305 : CNF.NClause := [(361,false),(362,true),(363,true),(364,true),(365,true),(371,true)]
theorem inp_9305 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9305 := by
  exact input_gate (closedGate5 7 5) (closed_mem 7 5) cl_9305 (by decide) v h
def cl_9311 : CNF.NClause := [(345,false),(349,true),(353,true),(357,true),(361,true),(370,true)]
theorem inp_9311 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9311 := by
  exact input_gate (closedGate5 7 6) (closed_mem 7 6) cl_9311 (by decide) v h
def cl_9322 : CNF.NClause := [(344,true),(347,false),(355,true),(358,true),(361,true),(369,true)]
theorem inp_9322 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9322 := by
  exact input_gate (closedGate5 7 8) (closed_mem 7 8) cl_9322 (by decide) v h
def cl_9328 : CNF.NClause := [(342,true),(348,false),(354,true),(360,true),(361,true),(367,true)]
theorem inp_9328 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9328 := by
  exact input_gate (closedGate5 7 9) (closed_mem 7 9) cl_9328 (by decide) v h
def cl_9340 : CNF.NClause := [(345,true),(348,false),(351,true),(359,true),(362,true),(369,true)]
theorem inp_9340 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9340 := by
  exact input_gate (closedGate5 7 11) (closed_mem 7 11) cl_9340 (by decide) v h
def cl_9359 : CNF.NClause := [(342,false),(349,true),(351,true),(358,true),(365,true),(368,true)]
theorem inp_9359 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9359 := by
  exact input_gate (closedGate5 7 14) (closed_mem 7 14) cl_9359 (by decide) v h
def cl_9362 : CNF.NClause := [(356,true),(357,true),(358,true),(359,false),(360,true),(371,true)]
theorem inp_9362 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9362 := by
  exact input_gate (closedGate5 7 15) (closed_mem 7 15) cl_9362 (by decide) v h
def cl_9384 : CNF.NClause := [(342,true),(350,true),(353,true),(356,true),(364,true),(369,false)]
theorem inp_9384 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9384 := by
  exact input_gate (closedGate5 7 19) (closed_mem 7 19) cl_9384 (by decide) v h
def cl_9393 : CNF.NClause := [(346,true),(347,true),(348,false),(349,true),(350,true),(371,true)]
theorem inp_9393 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9393 := by
  exact input_gate (closedGate5 7 20) (closed_mem 7 20) cl_9393 (by decide) v h
def cl_9411 : CNF.NClause := [(344,true),(346,true),(353,false),(360,true),(362,true),(368,true)]
theorem inp_9411 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9411 := by
  exact input_gate (closedGate5 7 23) (closed_mem 7 23) cl_9411 (by decide) v h
def cl_9417 : CNF.NClause := [(342,true),(346,true),(355,false),(359,true),(363,true),(370,true)]
theorem inp_9417 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9417 := by
  exact input_gate (closedGate5 7 24) (closed_mem 7 24) cl_9417 (by decide) v h
def cl_9436 : CNF.NClause := [(341,true),(348,false),(355,true),(357,true),(364,true),(368,true)]
theorem inp_9436 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9436 := by
  exact input_gate (closedGate5 7 27) (closed_mem 7 27) cl_9436 (by decide) v h
def cl_9438 : CNF.NClause := [(341,true),(349,true),(352,true),(360,true),(363,true),(369,false)]
theorem inp_9438 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9438 := by
  exact input_gate (closedGate5 7 28) (closed_mem 7 28) cl_9438 (by decide) v h
def cl_9457 : CNF.NClause := [(397,true),(398,true),(399,true),(400,true),(401,false),(402,true)]
theorem inp_9457 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9457 := by
  exact input_gate (closedGate5 8 0) (closed_mem 8 0) cl_9457 (by decide) v h
def cl_9484 : CNF.NClause := [(373,true),(378,false),(383,true),(388,true),(393,true),(397,true)]
theorem inp_9484 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9484 := by
  exact input_gate (closedGate5 8 4) (closed_mem 8 4) cl_9484 (by decide) v h
def cl_9487 : CNF.NClause := [(392,true),(393,true),(394,true),(395,true),(396,false),(402,true)]
theorem inp_9487 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9487 := by
  exact input_gate (closedGate5 8 5) (closed_mem 8 5) cl_9487 (by decide) v h
def cl_9496 : CNF.NClause := [(376,true),(380,false),(384,true),(388,true),(392,true),(401,true)]
theorem inp_9496 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9496 := by
  exact input_gate (closedGate5 8 6) (closed_mem 8 6) cl_9496 (by decide) v h
def cl_9511 : CNF.NClause := [(373,true),(379,true),(385,true),(391,true),(392,false),(398,true)]
theorem inp_9511 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9511 := by
  exact input_gate (closedGate5 8 9) (closed_mem 8 9) cl_9511 (by decide) v h
def cl_9524 : CNF.NClause := [(376,true),(379,true),(382,true),(390,false),(393,true),(400,true)]
theorem inp_9524 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9524 := by
  exact input_gate (closedGate5 8 11) (closed_mem 8 11) cl_9524 (by decide) v h
def cl_9551 : CNF.NClause := [(387,false),(388,true),(389,true),(390,true),(391,true),(402,true)]
theorem inp_9551 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9551 := by
  exact input_gate (closedGate5 8 15) (closed_mem 8 15) cl_9551 (by decide) v h
def cl_9556 : CNF.NClause := [(376,true),(378,false),(385,true),(387,true),(394,true),(399,true)]
theorem inp_9556 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9556 := by
  exact input_gate (closedGate5 8 16) (closed_mem 8 16) cl_9556 (by decide) v h
def cl_9567 : CNF.NClause := [(375,true),(379,true),(383,false),(387,true),(396,true),(401,true)]
theorem inp_9567 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9567 := by
  exact input_gate (closedGate5 8 18) (closed_mem 8 18) cl_9567 (by decide) v h
def cl_9572 : CNF.NClause := [(373,true),(381,true),(384,true),(387,false),(395,true),(400,true)]
theorem inp_9572 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9572 := by
  exact input_gate (closedGate5 8 19) (closed_mem 8 19) cl_9572 (by decide) v h
def cl_9575 : CNF.NClause := [(373,false),(381,true),(384,true),(387,true),(395,true),(400,true)]
theorem inp_9575 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9575 := by
  exact input_gate (closedGate5 8 19) (closed_mem 8 19) cl_9575 (by decide) v h
def cl_9578 : CNF.NClause := [(377,true),(378,true),(379,true),(380,false),(381,true),(402,true)]
theorem inp_9578 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9578 := by
  exact input_gate (closedGate5 8 20) (closed_mem 8 20) cl_9578 (by decide) v h
def cl_9591 : CNF.NClause := [(374,true),(377,true),(385,false),(388,true),(396,true),(400,true)]
theorem inp_9591 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9591 := by
  exact input_gate (closedGate5 8 22) (closed_mem 8 22) cl_9591 (by decide) v h
def cl_9596 : CNF.NClause := [(375,true),(377,true),(384,true),(391,false),(393,true),(399,true)]
theorem inp_9596 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9596 := by
  exact input_gate (closedGate5 8 23) (closed_mem 8 23) cl_9596 (by decide) v h
end Percolation.Replay
