import NInputs157
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_9469 : CNF.NClause := [(374,true),(379,true),(384,true),(389,true),(394,false),(397,true)]
theorem inp_9469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9469 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 2) (closed_mem 8 2) cl_9469 (by decide) v hb
def cl_9470 : CNF.NClause := [(374,true),(379,true),(384,true),(389,false),(394,true),(397,true)]
theorem inp_9470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9470 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 2) (closed_mem 8 2) cl_9470 (by decide) v hb
def cl_9471 : CNF.NClause := [(374,true),(379,true),(384,false),(389,true),(394,true),(397,true)]
theorem inp_9471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9471 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 2) (closed_mem 8 2) cl_9471 (by decide) v hb
def cl_9472 : CNF.NClause := [(374,true),(379,false),(384,true),(389,true),(394,true),(397,true)]
theorem inp_9472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9472 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 2) (closed_mem 8 2) cl_9472 (by decide) v hb
def cl_9473 : CNF.NClause := [(374,false),(379,true),(384,true),(389,true),(394,true),(397,true)]
theorem inp_9473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9473 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 2) (closed_mem 8 2) cl_9473 (by decide) v hb
def cl_9478 : CNF.NClause := [(375,true),(380,false),(385,true),(390,true),(395,true),(397,true)]
theorem inp_9478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9478 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 3) (closed_mem 8 3) cl_9478 (by decide) v hb
def cl_9481 : CNF.NClause := [(373,true),(378,true),(383,true),(388,true),(393,false),(397,true)]
theorem inp_9481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9481 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 4) (closed_mem 8 4) cl_9481 (by decide) v hb
def cl_9482 : CNF.NClause := [(373,true),(378,true),(383,true),(388,false),(393,true),(397,true)]
theorem inp_9482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9482 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 4) (closed_mem 8 4) cl_9482 (by decide) v hb
def cl_9483 : CNF.NClause := [(373,true),(378,true),(383,false),(388,true),(393,true),(397,true)]
theorem inp_9483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9483 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 4) (closed_mem 8 4) cl_9483 (by decide) v hb
def cl_9484 : CNF.NClause := [(373,true),(378,false),(383,true),(388,true),(393,true),(397,true)]
theorem inp_9484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9484 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9484 v hb
def cl_9485 : CNF.NClause := [(373,false),(378,true),(383,true),(388,true),(393,true),(397,true)]
theorem inp_9485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9485 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 4) (closed_mem 8 4) cl_9485 (by decide) v hb
def cl_9487 : CNF.NClause := [(392,true),(393,true),(394,true),(395,true),(396,false),(402,true)]
theorem inp_9487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9487 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9487 v hb
def cl_9488 : CNF.NClause := [(392,true),(393,true),(394,true),(395,false),(396,true),(402,true)]
theorem inp_9488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9488 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 5) (closed_mem 8 5) cl_9488 (by decide) v hb
def cl_9489 : CNF.NClause := [(392,true),(393,true),(394,false),(395,true),(396,true),(402,true)]
theorem inp_9489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9489 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 5) (closed_mem 8 5) cl_9489 (by decide) v hb
def cl_9490 : CNF.NClause := [(392,true),(393,false),(394,true),(395,true),(396,true),(402,true)]
theorem inp_9490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9490 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 5) (closed_mem 8 5) cl_9490 (by decide) v hb
def cl_9491 : CNF.NClause := [(392,false),(393,true),(394,true),(395,true),(396,true),(402,true)]
theorem inp_9491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9491 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 5) (closed_mem 8 5) cl_9491 (by decide) v hb
def cl_9496 : CNF.NClause := [(376,true),(380,false),(384,true),(388,true),(392,true),(401,true)]
theorem inp_9496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9496 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9496 v hb
def cl_9499 : CNF.NClause := [(374,true),(381,true),(383,true),(390,true),(392,false),(399,true)]
theorem inp_9499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9499 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 7) (closed_mem 8 7) cl_9499 (by decide) v hb
def cl_9500 : CNF.NClause := [(374,true),(381,true),(383,true),(390,false),(392,true),(399,true)]
theorem inp_9500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9500 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 7) (closed_mem 8 7) cl_9500 (by decide) v hb
def cl_9501 : CNF.NClause := [(374,true),(381,true),(383,false),(390,true),(392,true),(399,true)]
theorem inp_9501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9501 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 7) (closed_mem 8 7) cl_9501 (by decide) v hb
def cl_9502 : CNF.NClause := [(374,true),(381,false),(383,true),(390,true),(392,true),(399,true)]
theorem inp_9502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9502 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 7) (closed_mem 8 7) cl_9502 (by decide) v hb
def cl_9503 : CNF.NClause := [(374,false),(381,true),(383,true),(390,true),(392,true),(399,true)]
theorem inp_9503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9503 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 7) (closed_mem 8 7) cl_9503 (by decide) v hb
def cl_9504 : CNF.NClause := [(375,true),(378,true),(386,true),(389,true),(392,true),(400,false)]
theorem inp_9504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9504 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 8) (closed_mem 8 8) cl_9504 (by decide) v hb
def cl_9506 : CNF.NClause := [(375,true),(378,true),(386,true),(389,false),(392,true),(400,true)]
theorem inp_9506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9506 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 8) (closed_mem 8 8) cl_9506 (by decide) v hb
def cl_9510 : CNF.NClause := [(373,true),(379,true),(385,true),(391,true),(392,true),(398,false)]
theorem inp_9510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9510 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 9) (closed_mem 8 9) cl_9510 (by decide) v hb
def cl_9511 : CNF.NClause := [(373,true),(379,true),(385,true),(391,true),(392,false),(398,true)]
theorem inp_9511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9511 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9511 v hb
def cl_9513 : CNF.NClause := [(373,true),(379,true),(385,false),(391,true),(392,true),(398,true)]
theorem inp_9513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9513 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 9) (closed_mem 8 9) cl_9513 (by decide) v hb
def cl_9517 : CNF.NClause := [(382,true),(383,true),(384,true),(385,true),(386,false),(402,true)]
theorem inp_9517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9517 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 10) (closed_mem 8 10) cl_9517 (by decide) v hb
def cl_9518 : CNF.NClause := [(382,true),(383,true),(384,true),(385,false),(386,true),(402,true)]
theorem inp_9518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9518 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 10) (closed_mem 8 10) cl_9518 (by decide) v hb
def cl_9519 : CNF.NClause := [(382,true),(383,true),(384,false),(385,true),(386,true),(402,true)]
theorem inp_9519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9519 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 10) (closed_mem 8 10) cl_9519 (by decide) v hb
def cl_9520 : CNF.NClause := [(382,true),(383,false),(384,true),(385,true),(386,true),(402,true)]
theorem inp_9520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9520 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 10) (closed_mem 8 10) cl_9520 (by decide) v hb
def cl_9521 : CNF.NClause := [(382,false),(383,true),(384,true),(385,true),(386,true),(402,true)]
theorem inp_9521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9521 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 10) (closed_mem 8 10) cl_9521 (by decide) v hb
def cl_9522 : CNF.NClause := [(376,true),(379,true),(382,true),(390,true),(393,true),(400,false)]
theorem inp_9522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9522 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 11) (closed_mem 8 11) cl_9522 (by decide) v hb
def cl_9523 : CNF.NClause := [(376,true),(379,true),(382,true),(390,true),(393,false),(400,true)]
theorem inp_9523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9523 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 11) (closed_mem 8 11) cl_9523 (by decide) v hb
def cl_9525 : CNF.NClause := [(376,true),(379,true),(382,false),(390,true),(393,true),(400,true)]
theorem inp_9525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9525 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 11) (closed_mem 8 11) cl_9525 (by decide) v hb
def cl_9526 : CNF.NClause := [(376,true),(379,false),(382,true),(390,true),(393,true),(400,true)]
theorem inp_9526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9526 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 11) (closed_mem 8 11) cl_9526 (by decide) v hb
def cl_9527 : CNF.NClause := [(376,false),(379,true),(382,true),(390,true),(393,true),(400,true)]
theorem inp_9527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9527 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 11) (closed_mem 8 11) cl_9527 (by decide) v hb
def cl_9529 : CNF.NClause := [(374,true),(378,true),(382,true),(391,true),(395,false),(401,true)]
theorem inp_9529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9529 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 12) (closed_mem 8 12) cl_9529 (by decide) v hb
def cl_9530 : CNF.NClause := [(374,true),(378,true),(382,true),(391,false),(395,true),(401,true)]
theorem inp_9530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9530 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 12) (closed_mem 8 12) cl_9530 (by decide) v hb
def cl_9535 : CNF.NClause := [(375,true),(381,true),(382,true),(388,true),(394,false),(398,true)]
theorem inp_9535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9535 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 13) (closed_mem 8 13) cl_9535 (by decide) v hb
def cl_9537 : CNF.NClause := [(375,true),(381,true),(382,false),(388,true),(394,true),(398,true)]
theorem inp_9537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9537 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 13) (closed_mem 8 13) cl_9537 (by decide) v hb
def cl_9539 : CNF.NClause := [(375,false),(381,true),(382,true),(388,true),(394,true),(398,true)]
theorem inp_9539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9539 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 13) (closed_mem 8 13) cl_9539 (by decide) v hb
def cl_9544 : CNF.NClause := [(373,true),(380,false),(382,true),(389,true),(396,true),(399,true)]
theorem inp_9544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9544 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 14) (closed_mem 8 14) cl_9544 (by decide) v hb
def cl_9548 : CNF.NClause := [(387,true),(388,true),(389,true),(390,false),(391,true),(402,true)]
theorem inp_9548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9548 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 15) (closed_mem 8 15) cl_9548 (by decide) v hb
def cl_9549 : CNF.NClause := [(387,true),(388,true),(389,false),(390,true),(391,true),(402,true)]
theorem inp_9549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9549 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 15) (closed_mem 8 15) cl_9549 (by decide) v hb
def cl_9550 : CNF.NClause := [(387,true),(388,false),(389,true),(390,true),(391,true),(402,true)]
theorem inp_9550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9550 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 15) (closed_mem 8 15) cl_9550 (by decide) v hb
def cl_9551 : CNF.NClause := [(387,false),(388,true),(389,true),(390,true),(391,true),(402,true)]
theorem inp_9551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9551 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9551 v hb
def cl_9553 : CNF.NClause := [(376,true),(378,true),(385,true),(387,true),(394,false),(399,true)]
theorem inp_9553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9553 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 16) (closed_mem 8 16) cl_9553 (by decide) v hb
def cl_9554 : CNF.NClause := [(376,true),(378,true),(385,true),(387,false),(394,true),(399,true)]
theorem inp_9554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9554 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 16) (closed_mem 8 16) cl_9554 (by decide) v hb
def cl_9556 : CNF.NClause := [(376,true),(378,false),(385,true),(387,true),(394,true),(399,true)]
theorem inp_9556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9556 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9556 v hb
end Percolation.NReplay
