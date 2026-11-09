import NInputs007
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_612 : CNF.NClause := [(71,true),(1,true),(7,true),(13,false),(19,false),(20,false),(26,true)]
theorem inp_612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_612 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_612 v hb
def cl_613 : CNF.NClause := [(71,true),(1,false),(7,false),(13,true),(19,false),(20,false),(26,true)]
theorem inp_613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_613 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_613 (by decide) v hb
def cl_614 : CNF.NClause := [(71,true),(1,true),(7,false),(13,true),(19,false),(20,false),(26,true)]
theorem inp_614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_614 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_614 (by decide) v hb
def cl_615 : CNF.NClause := [(71,true),(1,false),(7,true),(13,true),(19,false),(20,false),(26,true)]
theorem inp_615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_615 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_615 v hb
def cl_616 : CNF.NClause := [(71,true),(1,true),(7,true),(13,true),(19,false),(20,false),(26,true)]
theorem inp_616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_616 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_616 v hb
def cl_617 : CNF.NClause := [(71,true),(1,false),(7,false),(13,false),(19,true),(20,false),(26,true)]
theorem inp_617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_617 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_617 v hb
def cl_618 : CNF.NClause := [(71,true),(1,true),(7,false),(13,false),(19,true),(20,false),(26,true)]
theorem inp_618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_618 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_618 (by decide) v hb
def cl_619 : CNF.NClause := [(71,true),(1,false),(7,true),(13,false),(19,true),(20,false),(26,true)]
theorem inp_619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_619 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_619 v hb
def cl_620 : CNF.NClause := [(71,true),(1,true),(7,true),(13,false),(19,true),(20,false),(26,true)]
theorem inp_620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_620 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_620 v hb
def cl_621 : CNF.NClause := [(71,true),(1,false),(7,false),(13,true),(19,true),(20,false),(26,true)]
theorem inp_621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_621 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_621 (by decide) v hb
def cl_622 : CNF.NClause := [(71,true),(1,true),(7,false),(13,true),(19,true),(20,false),(26,true)]
theorem inp_622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_622 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_622 (by decide) v hb
def cl_623 : CNF.NClause := [(71,true),(1,false),(7,true),(13,true),(19,true),(20,false),(26,true)]
theorem inp_623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_623 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_623 v hb
def cl_624 : CNF.NClause := [(71,false),(1,true),(7,true),(13,true),(19,true),(20,false),(26,true)]
theorem inp_624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_624 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_624 v hb
def cl_625 : CNF.NClause := [(71,true),(1,false),(7,false),(13,false),(19,false),(20,true),(26,true)]
theorem inp_625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_625 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_625 (by decide) v hb
def cl_626 : CNF.NClause := [(71,true),(1,true),(7,false),(13,false),(19,false),(20,true),(26,true)]
theorem inp_626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_626 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_626 (by decide) v hb
def cl_627 : CNF.NClause := [(71,true),(1,false),(7,true),(13,false),(19,false),(20,true),(26,true)]
theorem inp_627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_627 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_627 v hb
def cl_628 : CNF.NClause := [(71,true),(1,true),(7,true),(13,false),(19,false),(20,true),(26,true)]
theorem inp_628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_628 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_628 v hb
def cl_629 : CNF.NClause := [(71,true),(1,false),(7,false),(13,true),(19,false),(20,true),(26,true)]
theorem inp_629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_629 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_629 (by decide) v hb
def cl_630 : CNF.NClause := [(71,true),(1,true),(7,false),(13,true),(19,false),(20,true),(26,true)]
theorem inp_630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_630 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_630 (by decide) v hb
def cl_631 : CNF.NClause := [(71,true),(1,false),(7,true),(13,true),(19,false),(20,true),(26,true)]
theorem inp_631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_631 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_631 v hb
def cl_632 : CNF.NClause := [(71,false),(1,true),(7,true),(13,true),(19,false),(20,true),(26,true)]
theorem inp_632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_632 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_632 v hb
def cl_633 : CNF.NClause := [(71,true),(1,false),(7,false),(13,false),(19,true),(20,true),(26,true)]
theorem inp_633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_633 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_633 v hb
def cl_634 : CNF.NClause := [(71,true),(1,true),(7,false),(13,false),(19,true),(20,true),(26,true)]
theorem inp_634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_634 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_634 (by decide) v hb
def cl_635 : CNF.NClause := [(71,true),(1,false),(7,true),(13,false),(19,true),(20,true),(26,true)]
theorem inp_635 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_635 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_635 v hb
def cl_636 : CNF.NClause := [(71,false),(1,true),(7,true),(13,false),(19,true),(20,true),(26,true)]
theorem inp_636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_636 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_636 v hb
def cl_637 : CNF.NClause := [(71,true),(1,false),(7,false),(13,true),(19,true),(20,true),(26,true)]
theorem inp_637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_637 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 9) 9) (activationA_mem 9) cl_637 (by decide) v hb
def cl_638 : CNF.NClause := [(71,false),(1,true),(7,false),(13,true),(19,true),(20,true),(26,true)]
theorem inp_638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_638 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_638 v hb
def cl_639 : CNF.NClause := [(71,false),(1,false),(7,true),(13,true),(19,true),(20,true),(26,true)]
theorem inp_639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_639 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_639 v hb
def cl_640 : CNF.NClause := [(71,false),(1,true),(7,true),(13,true),(19,true),(20,true),(26,true)]
theorem inp_640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_640 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_640 v hb
def cl_673 : CNF.NClause := [(72,true),(10,false),(11,false),(12,false),(13,false),(14,false),(30,true)]
theorem inp_673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_673 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_673 v hb
def cl_674 : CNF.NClause := [(72,true),(10,true),(11,false),(12,false),(13,false),(14,false),(30,true)]
theorem inp_674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_674 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_674 v hb
def cl_675 : CNF.NClause := [(72,true),(10,false),(11,true),(12,false),(13,false),(14,false),(30,true)]
theorem inp_675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_675 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_675 (by decide) v hb
def cl_676 : CNF.NClause := [(72,true),(10,true),(11,true),(12,false),(13,false),(14,false),(30,true)]
theorem inp_676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_676 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_676 v hb
def cl_677 : CNF.NClause := [(72,true),(10,false),(11,false),(12,true),(13,false),(14,false),(30,true)]
theorem inp_677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_677 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_677 v hb
def cl_678 : CNF.NClause := [(72,true),(10,true),(11,false),(12,true),(13,false),(14,false),(30,true)]
theorem inp_678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_678 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_678 v hb
def cl_679 : CNF.NClause := [(72,true),(10,false),(11,true),(12,true),(13,false),(14,false),(30,true)]
theorem inp_679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_679 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_679 (by decide) v hb
def cl_680 : CNF.NClause := [(72,true),(10,true),(11,true),(12,true),(13,false),(14,false),(30,true)]
theorem inp_680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_680 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_680 v hb
def cl_681 : CNF.NClause := [(72,true),(10,false),(11,false),(12,false),(13,true),(14,false),(30,true)]
theorem inp_681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_681 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_681 v hb
def cl_682 : CNF.NClause := [(72,true),(10,true),(11,false),(12,false),(13,true),(14,false),(30,true)]
theorem inp_682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_682 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_682 v hb
def cl_683 : CNF.NClause := [(72,true),(10,false),(11,true),(12,false),(13,true),(14,false),(30,true)]
theorem inp_683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_683 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_683 (by decide) v hb
def cl_684 : CNF.NClause := [(72,true),(10,true),(11,true),(12,false),(13,true),(14,false),(30,true)]
theorem inp_684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_684 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_684 v hb
def cl_685 : CNF.NClause := [(72,true),(10,false),(11,false),(12,true),(13,true),(14,false),(30,true)]
theorem inp_685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_685 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_685 v hb
def cl_686 : CNF.NClause := [(72,true),(10,true),(11,false),(12,true),(13,true),(14,false),(30,true)]
theorem inp_686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_686 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_686 v hb
def cl_687 : CNF.NClause := [(72,true),(10,false),(11,true),(12,true),(13,true),(14,false),(30,true)]
theorem inp_687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_687 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_687 (by decide) v hb
def cl_688 : CNF.NClause := [(72,false),(10,true),(11,true),(12,true),(13,true),(14,false),(30,true)]
theorem inp_688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_688 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_688 v hb
def cl_689 : CNF.NClause := [(72,true),(10,false),(11,false),(12,false),(13,false),(14,true),(30,true)]
theorem inp_689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_689 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_689 v hb
def cl_690 : CNF.NClause := [(72,true),(10,true),(11,false),(12,false),(13,false),(14,true),(30,true)]
theorem inp_690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_690 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_690 v hb
def cl_691 : CNF.NClause := [(72,true),(10,false),(11,true),(12,false),(13,false),(14,true),(30,true)]
theorem inp_691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_691 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_691 (by decide) v hb
def cl_692 : CNF.NClause := [(72,true),(10,true),(11,true),(12,false),(13,false),(14,true),(30,true)]
theorem inp_692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_692 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_692 v hb
def cl_693 : CNF.NClause := [(72,true),(10,false),(11,false),(12,true),(13,false),(14,true),(30,true)]
theorem inp_693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_693 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_693 v hb
end Percolation.NReplay
