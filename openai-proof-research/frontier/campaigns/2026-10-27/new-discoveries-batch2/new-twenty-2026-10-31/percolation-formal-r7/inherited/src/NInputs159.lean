import NInputs158
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_9562 : CNF.NClause := [(374,true),(380,false),(386,true),(387,true),(393,true),(398,true)]
theorem inp_9562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9562 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 17) (closed_mem 8 17) cl_9562 (by decide) v hb
def cl_9564 : CNF.NClause := [(375,true),(379,true),(383,true),(387,true),(396,true),(401,false)]
theorem inp_9564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9564 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 18) (closed_mem 8 18) cl_9564 (by decide) v hb
def cl_9566 : CNF.NClause := [(375,true),(379,true),(383,true),(387,false),(396,true),(401,true)]
theorem inp_9566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9566 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 18) (closed_mem 8 18) cl_9566 (by decide) v hb
def cl_9568 : CNF.NClause := [(375,true),(379,false),(383,true),(387,true),(396,true),(401,true)]
theorem inp_9568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9568 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 18) (closed_mem 8 18) cl_9568 (by decide) v hb
def cl_9573 : CNF.NClause := [(373,true),(381,true),(384,false),(387,true),(395,true),(400,true)]
theorem inp_9573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9573 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 19) (closed_mem 8 19) cl_9573 (by decide) v hb
def cl_9574 : CNF.NClause := [(373,true),(381,false),(384,true),(387,true),(395,true),(400,true)]
theorem inp_9574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9574 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 19) (closed_mem 8 19) cl_9574 (by decide) v hb
def cl_9578 : CNF.NClause := [(377,true),(378,true),(379,true),(380,false),(381,true),(402,true)]
theorem inp_9578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9578 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9578 v hb
def cl_9583 : CNF.NClause := [(376,true),(377,true),(383,true),(389,true),(395,false),(398,true)]
theorem inp_9583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9583 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 21) (closed_mem 8 21) cl_9583 (by decide) v hb
def cl_9585 : CNF.NClause := [(376,true),(377,true),(383,false),(389,true),(395,true),(398,true)]
theorem inp_9585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9585 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 21) (closed_mem 8 21) cl_9585 (by decide) v hb
def cl_9587 : CNF.NClause := [(376,false),(377,true),(383,true),(389,true),(395,true),(398,true)]
theorem inp_9587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9587 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 21) (closed_mem 8 21) cl_9587 (by decide) v hb
def cl_9589 : CNF.NClause := [(374,true),(377,true),(385,true),(388,true),(396,false),(400,true)]
theorem inp_9589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9589 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 22) (closed_mem 8 22) cl_9589 (by decide) v hb
def cl_9591 : CNF.NClause := [(374,true),(377,true),(385,false),(388,true),(396,true),(400,true)]
theorem inp_9591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9591 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9591 v hb
def cl_9592 : CNF.NClause := [(374,true),(377,false),(385,true),(388,true),(396,true),(400,true)]
theorem inp_9592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9592 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 22) (closed_mem 8 22) cl_9592 (by decide) v hb
def cl_9593 : CNF.NClause := [(374,false),(377,true),(385,true),(388,true),(396,true),(400,true)]
theorem inp_9593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9593 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 22) (closed_mem 8 22) cl_9593 (by decide) v hb
def cl_9594 : CNF.NClause := [(375,true),(377,true),(384,true),(391,true),(393,true),(399,false)]
theorem inp_9594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9594 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 23) (closed_mem 8 23) cl_9594 (by decide) v hb
def cl_9597 : CNF.NClause := [(375,true),(377,true),(384,false),(391,true),(393,true),(399,true)]
theorem inp_9597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9597 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 23) (closed_mem 8 23) cl_9597 (by decide) v hb
def cl_9599 : CNF.NClause := [(375,false),(377,true),(384,true),(391,true),(393,true),(399,true)]
theorem inp_9599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9599 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 23) (closed_mem 8 23) cl_9599 (by decide) v hb
def cl_9603 : CNF.NClause := [(373,true),(377,true),(386,false),(390,true),(394,true),(401,true)]
theorem inp_9603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9603 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 24) (closed_mem 8 24) cl_9603 (by decide) v hb
def cl_9604 : CNF.NClause := [(373,true),(377,false),(386,true),(390,true),(394,true),(401,true)]
theorem inp_9604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9604 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 24) (closed_mem 8 24) cl_9604 (by decide) v hb
def cl_9605 : CNF.NClause := [(373,false),(377,true),(386,true),(390,true),(394,true),(401,true)]
theorem inp_9605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9605 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 24) (closed_mem 8 24) cl_9605 (by decide) v hb
def cl_9607 : CNF.NClause := [(372,true),(373,true),(374,true),(375,true),(376,false),(402,true)]
theorem inp_9607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9607 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 25) (closed_mem 8 25) cl_9607 (by decide) v hb
def cl_9608 : CNF.NClause := [(372,true),(373,true),(374,true),(375,false),(376,true),(402,true)]
theorem inp_9608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9608 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 25) (closed_mem 8 25) cl_9608 (by decide) v hb
def cl_9609 : CNF.NClause := [(372,true),(373,true),(374,false),(375,true),(376,true),(402,true)]
theorem inp_9609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9609 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 25) (closed_mem 8 25) cl_9609 (by decide) v hb
def cl_9610 : CNF.NClause := [(372,true),(373,false),(374,true),(375,true),(376,true),(402,true)]
theorem inp_9610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9610 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 25) (closed_mem 8 25) cl_9610 (by decide) v hb
def cl_9612 : CNF.NClause := [(372,true),(381,true),(385,true),(389,true),(393,true),(401,false)]
theorem inp_9612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9612 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 26) (closed_mem 8 26) cl_9612 (by decide) v hb
def cl_9613 : CNF.NClause := [(372,true),(381,true),(385,true),(389,true),(393,false),(401,true)]
theorem inp_9613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9613 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 26) (closed_mem 8 26) cl_9613 (by decide) v hb
def cl_9614 : CNF.NClause := [(372,true),(381,true),(385,true),(389,false),(393,true),(401,true)]
theorem inp_9614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9614 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 26) (closed_mem 8 26) cl_9614 (by decide) v hb
def cl_9615 : CNF.NClause := [(372,true),(381,true),(385,false),(389,true),(393,true),(401,true)]
theorem inp_9615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9615 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9615 v hb
def cl_9616 : CNF.NClause := [(372,true),(381,false),(385,true),(389,true),(393,true),(401,true)]
theorem inp_9616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9616 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 26) (closed_mem 8 26) cl_9616 (by decide) v hb
def cl_9618 : CNF.NClause := [(372,true),(379,true),(386,true),(388,true),(395,true),(399,false)]
theorem inp_9618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9618 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 27) (closed_mem 8 27) cl_9618 (by decide) v hb
def cl_9619 : CNF.NClause := [(372,true),(379,true),(386,true),(388,true),(395,false),(399,true)]
theorem inp_9619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9619 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 27) (closed_mem 8 27) cl_9619 (by decide) v hb
def cl_9621 : CNF.NClause := [(372,true),(379,true),(386,false),(388,true),(395,true),(399,true)]
theorem inp_9621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9621 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 27) (closed_mem 8 27) cl_9621 (by decide) v hb
def cl_9622 : CNF.NClause := [(372,true),(379,false),(386,true),(388,true),(395,true),(399,true)]
theorem inp_9622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9622 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 27) (closed_mem 8 27) cl_9622 (by decide) v hb
def cl_9628 : CNF.NClause := [(372,true),(380,false),(383,true),(391,true),(394,true),(400,true)]
theorem inp_9628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9628 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 28) (closed_mem 8 28) cl_9628 (by decide) v hb
def cl_9631 : CNF.NClause := [(372,true),(378,true),(384,true),(390,true),(396,false),(398,true)]
theorem inp_9631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9631 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 29) (closed_mem 8 29) cl_9631 (by decide) v hb
def cl_9632 : CNF.NClause := [(372,true),(378,true),(384,true),(390,false),(396,true),(398,true)]
theorem inp_9632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9632 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 29) (closed_mem 8 29) cl_9632 (by decide) v hb
def cl_9633 : CNF.NClause := [(372,true),(378,true),(384,false),(390,true),(396,true),(398,true)]
theorem inp_9633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9633 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 29) (closed_mem 8 29) cl_9633 (by decide) v hb
def cl_9634 : CNF.NClause := [(372,true),(378,false),(384,true),(390,true),(396,true),(398,true)]
theorem inp_9634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9634 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 29) (closed_mem 8 29) cl_9634 (by decide) v hb
def cl_9637 : CNF.NClause := [(372,true),(377,true),(382,true),(387,true),(392,false),(397,true)]
theorem inp_9637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9637 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 30) (closed_mem 8 30) cl_9637 (by decide) v hb
def cl_9638 : CNF.NClause := [(372,true),(377,true),(382,true),(387,false),(392,true),(397,true)]
theorem inp_9638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9638 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 30) (closed_mem 8 30) cl_9638 (by decide) v hb
def cl_9639 : CNF.NClause := [(372,true),(377,true),(382,false),(387,true),(392,true),(397,true)]
theorem inp_9639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9639 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 30) (closed_mem 8 30) cl_9639 (by decide) v hb
def cl_9640 : CNF.NClause := [(372,true),(377,false),(382,true),(387,true),(392,true),(397,true)]
theorem inp_9640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9640 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 8 30) (closed_mem 8 30) cl_9640 (by decide) v hb
def cl_9643 : CNF.NClause := [(428,true),(429,true),(430,true),(431,true),(432,false),(433,true)]
theorem inp_9643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9643 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 0) (closed_mem 9 0) cl_9643 (by decide) v hb
def cl_9644 : CNF.NClause := [(428,true),(429,true),(430,true),(431,false),(432,true),(433,true)]
theorem inp_9644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9644 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 0) (closed_mem 9 0) cl_9644 (by decide) v hb
def cl_9645 : CNF.NClause := [(428,true),(429,true),(430,false),(431,true),(432,true),(433,true)]
theorem inp_9645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9645 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 0) (closed_mem 9 0) cl_9645 (by decide) v hb
def cl_9646 : CNF.NClause := [(428,true),(429,false),(430,true),(431,true),(432,true),(433,true)]
theorem inp_9646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9646 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_9646 v hb
def cl_9652 : CNF.NClause := [(407,true),(412,false),(417,true),(422,true),(427,true),(428,true)]
theorem inp_9652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9652 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 1) (closed_mem 9 1) cl_9652 (by decide) v hb
def cl_9655 : CNF.NClause := [(405,true),(410,true),(415,true),(420,true),(425,false),(428,true)]
theorem inp_9655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9655 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 2) (closed_mem 9 2) cl_9655 (by decide) v hb
def cl_9656 : CNF.NClause := [(405,true),(410,true),(415,true),(420,false),(425,true),(428,true)]
theorem inp_9656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9656 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 2) (closed_mem 9 2) cl_9656 (by decide) v hb
def cl_9657 : CNF.NClause := [(405,true),(410,true),(415,false),(420,true),(425,true),(428,true)]
theorem inp_9657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_9657 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 9 2) (closed_mem 9 2) cl_9657 (by decide) v hb
end Percolation.NReplay
