import Inputs006
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_648 : CNF.NClause := [(72,true),(10,true),(11,true),(12,true),(13,false),(14,false),(30,false)]
theorem inp_648 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_648 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_648 (by decide) v h
def cl_653 : CNF.NClause := [(72,true),(10,false),(11,false),(12,true),(13,true),(14,false),(30,false)]
theorem inp_653 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_653 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_653 (by decide) v h
def cl_657 : CNF.NClause := [(72,true),(10,false),(11,false),(12,false),(13,false),(14,true),(30,false)]
theorem inp_657 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_657 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_657 (by decide) v h
def cl_661 : CNF.NClause := [(72,true),(10,false),(11,false),(12,true),(13,false),(14,true),(30,false)]
theorem inp_661 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_661 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_661 (by decide) v h
def cl_664 : CNF.NClause := [(72,true),(10,true),(11,true),(12,true),(13,false),(14,true),(30,false)]
theorem inp_664 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_664 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_664 (by decide) v h
def cl_669 : CNF.NClause := [(72,true),(10,false),(11,false),(12,true),(13,true),(14,true),(30,false)]
theorem inp_669 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_669 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_669 (by decide) v h
def cl_672 : CNF.NClause := [(72,false),(10,true),(11,true),(12,true),(13,true),(14,true),(30,false)]
theorem inp_672 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_672 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_672 (by decide) v h
def cl_673 : CNF.NClause := [(72,true),(10,false),(11,false),(12,false),(13,false),(14,false),(30,true)]
theorem inp_673 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_673 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_673 (by decide) v h
def cl_674 : CNF.NClause := [(72,true),(10,true),(11,false),(12,false),(13,false),(14,false),(30,true)]
theorem inp_674 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_674 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_674 (by decide) v h
def cl_676 : CNF.NClause := [(72,true),(10,true),(11,true),(12,false),(13,false),(14,false),(30,true)]
theorem inp_676 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_676 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_676 (by decide) v h
def cl_677 : CNF.NClause := [(72,true),(10,false),(11,false),(12,true),(13,false),(14,false),(30,true)]
theorem inp_677 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_677 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_677 (by decide) v h
def cl_678 : CNF.NClause := [(72,true),(10,true),(11,false),(12,true),(13,false),(14,false),(30,true)]
theorem inp_678 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_678 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_678 (by decide) v h
def cl_680 : CNF.NClause := [(72,true),(10,true),(11,true),(12,true),(13,false),(14,false),(30,true)]
theorem inp_680 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_680 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_680 (by decide) v h
def cl_681 : CNF.NClause := [(72,true),(10,false),(11,false),(12,false),(13,true),(14,false),(30,true)]
theorem inp_681 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_681 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_681 (by decide) v h
def cl_682 : CNF.NClause := [(72,true),(10,true),(11,false),(12,false),(13,true),(14,false),(30,true)]
theorem inp_682 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_682 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_682 (by decide) v h
def cl_684 : CNF.NClause := [(72,true),(10,true),(11,true),(12,false),(13,true),(14,false),(30,true)]
theorem inp_684 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_684 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_684 (by decide) v h
def cl_685 : CNF.NClause := [(72,true),(10,false),(11,false),(12,true),(13,true),(14,false),(30,true)]
theorem inp_685 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_685 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_685 (by decide) v h
def cl_686 : CNF.NClause := [(72,true),(10,true),(11,false),(12,true),(13,true),(14,false),(30,true)]
theorem inp_686 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_686 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_686 (by decide) v h
def cl_688 : CNF.NClause := [(72,false),(10,true),(11,true),(12,true),(13,true),(14,false),(30,true)]
theorem inp_688 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_688 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_688 (by decide) v h
def cl_689 : CNF.NClause := [(72,true),(10,false),(11,false),(12,false),(13,false),(14,true),(30,true)]
theorem inp_689 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_689 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_689 (by decide) v h
def cl_690 : CNF.NClause := [(72,true),(10,true),(11,false),(12,false),(13,false),(14,true),(30,true)]
theorem inp_690 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_690 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_690 (by decide) v h
def cl_692 : CNF.NClause := [(72,true),(10,true),(11,true),(12,false),(13,false),(14,true),(30,true)]
theorem inp_692 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_692 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_692 (by decide) v h
def cl_693 : CNF.NClause := [(72,true),(10,false),(11,false),(12,true),(13,false),(14,true),(30,true)]
theorem inp_693 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_693 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_693 (by decide) v h
def cl_696 : CNF.NClause := [(72,false),(10,true),(11,true),(12,true),(13,false),(14,true),(30,true)]
theorem inp_696 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_696 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_696 (by decide) v h
def cl_697 : CNF.NClause := [(72,true),(10,false),(11,false),(12,false),(13,true),(14,true),(30,true)]
theorem inp_697 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_697 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_697 (by decide) v h
def cl_698 : CNF.NClause := [(72,true),(10,true),(11,false),(12,false),(13,true),(14,true),(30,true)]
theorem inp_698 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_698 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_698 (by decide) v h
def cl_700 : CNF.NClause := [(72,false),(10,true),(11,true),(12,false),(13,true),(14,true),(30,true)]
theorem inp_700 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_700 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_700 (by decide) v h
def cl_701 : CNF.NClause := [(72,true),(10,false),(11,false),(12,true),(13,true),(14,true),(30,true)]
theorem inp_701 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_701 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_701 (by decide) v h
def cl_702 : CNF.NClause := [(72,false),(10,true),(11,false),(12,true),(13,true),(14,true),(30,true)]
theorem inp_702 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_702 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_702 (by decide) v h
def cl_703 : CNF.NClause := [(72,false),(10,false),(11,true),(12,true),(13,true),(14,true),(30,true)]
theorem inp_703 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_703 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_703 (by decide) v h
def cl_704 : CNF.NClause := [(72,false),(10,true),(11,true),(12,true),(13,true),(14,true),(30,true)]
theorem inp_704 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_704 := by
  exact input_gate (activationGate5 SatVar.a (.i 10) 10) (activationA_mem 10) cl_704 (by decide) v h
def cl_705 : CNF.NClause := [(73,true),(4,false),(7,false),(10,false),(18,false),(21,false),(28,false)]
theorem inp_705 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_705 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_705 (by decide) v h
def cl_706 : CNF.NClause := [(73,true),(4,true),(7,false),(10,false),(18,false),(21,false),(28,false)]
theorem inp_706 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_706 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_706 (by decide) v h
def cl_707 : CNF.NClause := [(73,true),(4,false),(7,true),(10,false),(18,false),(21,false),(28,false)]
theorem inp_707 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_707 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_707 (by decide) v h
def cl_708 : CNF.NClause := [(73,true),(4,true),(7,true),(10,false),(18,false),(21,false),(28,false)]
theorem inp_708 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_708 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_708 (by decide) v h
def cl_709 : CNF.NClause := [(73,true),(4,false),(7,false),(10,true),(18,false),(21,false),(28,false)]
theorem inp_709 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_709 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_709 (by decide) v h
def cl_710 : CNF.NClause := [(73,true),(4,true),(7,false),(10,true),(18,false),(21,false),(28,false)]
theorem inp_710 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_710 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_710 (by decide) v h
def cl_711 : CNF.NClause := [(73,true),(4,false),(7,true),(10,true),(18,false),(21,false),(28,false)]
theorem inp_711 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_711 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_711 (by decide) v h
def cl_712 : CNF.NClause := [(73,true),(4,true),(7,true),(10,true),(18,false),(21,false),(28,false)]
theorem inp_712 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_712 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_712 (by decide) v h
def cl_713 : CNF.NClause := [(73,true),(4,false),(7,false),(10,false),(18,true),(21,false),(28,false)]
theorem inp_713 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_713 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_713 (by decide) v h
def cl_715 : CNF.NClause := [(73,true),(4,false),(7,true),(10,false),(18,true),(21,false),(28,false)]
theorem inp_715 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_715 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_715 (by decide) v h
def cl_716 : CNF.NClause := [(73,true),(4,true),(7,true),(10,false),(18,true),(21,false),(28,false)]
theorem inp_716 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_716 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_716 (by decide) v h
def cl_719 : CNF.NClause := [(73,true),(4,false),(7,true),(10,true),(18,true),(21,false),(28,false)]
theorem inp_719 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_719 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_719 (by decide) v h
def cl_723 : CNF.NClause := [(73,true),(4,false),(7,true),(10,false),(18,false),(21,true),(28,false)]
theorem inp_723 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_723 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_723 (by decide) v h
def cl_724 : CNF.NClause := [(73,true),(4,true),(7,true),(10,false),(18,false),(21,true),(28,false)]
theorem inp_724 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_724 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_724 (by decide) v h
def cl_727 : CNF.NClause := [(73,true),(4,false),(7,true),(10,true),(18,false),(21,true),(28,false)]
theorem inp_727 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_727 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_727 (by decide) v h
def cl_728 : CNF.NClause := [(73,true),(4,true),(7,true),(10,true),(18,false),(21,true),(28,false)]
theorem inp_728 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_728 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_728 (by decide) v h
def cl_729 : CNF.NClause := [(73,true),(4,false),(7,false),(10,false),(18,true),(21,true),(28,false)]
theorem inp_729 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_729 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_729 (by decide) v h
def cl_731 : CNF.NClause := [(73,true),(4,false),(7,true),(10,false),(18,true),(21,true),(28,false)]
theorem inp_731 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_731 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_731 (by decide) v h
def cl_732 : CNF.NClause := [(73,true),(4,true),(7,true),(10,false),(18,true),(21,true),(28,false)]
theorem inp_732 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_732 := by
  exact input_gate (activationGate5 SatVar.a (.i 11) 11) (activationA_mem 11) cl_732 (by decide) v h
end Percolation.Replay
