import NInputs118
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_6751 : CNF.NClause := [(52,false),(21,false),(66,true),(67,true),(73,true),(79,true),(85,false),(88,true)]
theorem inp_6751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6751 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6751 (by decide) v hb
def cl_6752 : CNF.NClause := [(52,false),(21,true),(66,true),(67,true),(73,true),(79,true),(85,false),(88,true)]
theorem inp_6752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6752 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6752 (by decide) v hb
def cl_6753 : CNF.NClause := [(52,false),(21,false),(66,false),(67,false),(73,false),(79,false),(85,true),(88,true)]
theorem inp_6753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6753 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6753 (by decide) v hb
def cl_6754 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,false),(79,false),(85,true),(88,true)]
theorem inp_6754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6754 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6754 v hb
def cl_6755 : CNF.NClause := [(52,false),(21,false),(66,true),(67,false),(73,false),(79,false),(85,true),(88,true)]
theorem inp_6755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6755 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6755 (by decide) v hb
def cl_6756 : CNF.NClause := [(52,false),(21,true),(66,true),(67,false),(73,false),(79,false),(85,true),(88,true)]
theorem inp_6756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6756 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6756 (by decide) v hb
def cl_6757 : CNF.NClause := [(52,false),(21,false),(66,false),(67,true),(73,false),(79,false),(85,true),(88,true)]
theorem inp_6757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6757 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6757 (by decide) v hb
def cl_6758 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,false),(79,false),(85,true),(88,true)]
theorem inp_6758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6758 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6758 (by decide) v hb
def cl_6759 : CNF.NClause := [(52,false),(21,false),(66,true),(67,true),(73,false),(79,false),(85,true),(88,true)]
theorem inp_6759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6759 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6759 (by decide) v hb
def cl_6760 : CNF.NClause := [(52,false),(21,true),(66,true),(67,true),(73,false),(79,false),(85,true),(88,true)]
theorem inp_6760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6760 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6760 (by decide) v hb
def cl_6761 : CNF.NClause := [(52,false),(21,false),(66,false),(67,false),(73,true),(79,false),(85,true),(88,true)]
theorem inp_6761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6761 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6761 (by decide) v hb
def cl_6762 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,true),(79,false),(85,true),(88,true)]
theorem inp_6762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6762 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6762 (by decide) v hb
def cl_6763 : CNF.NClause := [(52,false),(21,false),(66,true),(67,false),(73,true),(79,false),(85,true),(88,true)]
theorem inp_6763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6763 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6763 (by decide) v hb
def cl_6764 : CNF.NClause := [(52,false),(21,true),(66,true),(67,false),(73,true),(79,false),(85,true),(88,true)]
theorem inp_6764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6764 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6764 (by decide) v hb
def cl_6765 : CNF.NClause := [(52,false),(21,false),(66,false),(67,true),(73,true),(79,false),(85,true),(88,true)]
theorem inp_6765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6765 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6765 (by decide) v hb
def cl_6766 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,true),(79,false),(85,true),(88,true)]
theorem inp_6766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6766 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6766 (by decide) v hb
def cl_6767 : CNF.NClause := [(52,false),(21,false),(66,true),(67,true),(73,true),(79,false),(85,true),(88,true)]
theorem inp_6767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6767 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6767 (by decide) v hb
def cl_6768 : CNF.NClause := [(52,false),(21,true),(66,true),(67,true),(73,true),(79,false),(85,true),(88,true)]
theorem inp_6768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6768 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6768 (by decide) v hb
def cl_6769 : CNF.NClause := [(52,false),(21,false),(66,false),(67,false),(73,false),(79,true),(85,true),(88,true)]
theorem inp_6769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6769 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6769 (by decide) v hb
def cl_6770 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,false),(79,true),(85,true),(88,true)]
theorem inp_6770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6770 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6770 (by decide) v hb
def cl_6771 : CNF.NClause := [(52,false),(21,false),(66,true),(67,false),(73,false),(79,true),(85,true),(88,true)]
theorem inp_6771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6771 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6771 (by decide) v hb
def cl_6772 : CNF.NClause := [(52,false),(21,true),(66,true),(67,false),(73,false),(79,true),(85,true),(88,true)]
theorem inp_6772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6772 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6772 (by decide) v hb
def cl_6774 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,false),(79,true),(85,true),(88,true)]
theorem inp_6774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6774 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6774 (by decide) v hb
def cl_6776 : CNF.NClause := [(52,false),(21,true),(66,true),(67,true),(73,false),(79,true),(85,true),(88,true)]
theorem inp_6776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6776 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6776 (by decide) v hb
def cl_6777 : CNF.NClause := [(52,false),(21,false),(66,false),(67,false),(73,true),(79,true),(85,true),(88,true)]
theorem inp_6777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6777 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6777 (by decide) v hb
def cl_6778 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,true),(79,true),(85,true),(88,true)]
theorem inp_6778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6778 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6778 (by decide) v hb
def cl_6779 : CNF.NClause := [(52,false),(21,false),(66,true),(67,false),(73,true),(79,true),(85,true),(88,true)]
theorem inp_6779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6779 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6779 (by decide) v hb
def cl_6780 : CNF.NClause := [(52,false),(21,true),(66,true),(67,false),(73,true),(79,true),(85,true),(88,true)]
theorem inp_6780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6780 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6780 (by decide) v hb
def cl_6782 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,true),(79,true),(85,true),(88,true)]
theorem inp_6782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6782 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6782 (by decide) v hb
def cl_6784 : CNF.NClause := [(52,false),(21,true),(66,true),(67,true),(73,true),(79,true),(85,true),(88,true)]
theorem inp_6784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6784 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6784 (by decide) v hb
def cl_6785 : CNF.NClause := [(53,true),(22,false),(64,false),(67,false),(75,false),(78,false),(86,false),(90,false)]
theorem inp_6785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6785 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6785 (by decide) v hb
def cl_6786 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,false),(78,false),(86,false),(90,false)]
theorem inp_6786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6786 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6786 v hb
def cl_6787 : CNF.NClause := [(53,false),(22,false),(64,true),(67,false),(75,false),(78,false),(86,false),(90,false)]
theorem inp_6787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6787 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6787 (by decide) v hb
def cl_6788 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(75,false),(78,false),(86,false),(90,false)]
theorem inp_6788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6788 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6788 (by decide) v hb
def cl_6789 : CNF.NClause := [(53,false),(22,false),(64,false),(67,true),(75,false),(78,false),(86,false),(90,false)]
theorem inp_6789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6789 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6789 (by decide) v hb
def cl_6790 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,false),(78,false),(86,false),(90,false)]
theorem inp_6790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6790 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6790 v hb
def cl_6791 : CNF.NClause := [(53,false),(22,false),(64,true),(67,true),(75,false),(78,false),(86,false),(90,false)]
theorem inp_6791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6791 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6791 (by decide) v hb
def cl_6792 : CNF.NClause := [(53,false),(22,true),(64,true),(67,true),(75,false),(78,false),(86,false),(90,false)]
theorem inp_6792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6792 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6792 (by decide) v hb
def cl_6793 : CNF.NClause := [(53,false),(22,false),(64,false),(67,false),(75,true),(78,false),(86,false),(90,false)]
theorem inp_6793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6793 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6793 (by decide) v hb
def cl_6794 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,true),(78,false),(86,false),(90,false)]
theorem inp_6794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6794 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6794 (by decide) v hb
def cl_6795 : CNF.NClause := [(53,false),(22,false),(64,true),(67,false),(75,true),(78,false),(86,false),(90,false)]
theorem inp_6795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6795 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6795 (by decide) v hb
def cl_6796 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(75,true),(78,false),(86,false),(90,false)]
theorem inp_6796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6796 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6796 (by decide) v hb
def cl_6797 : CNF.NClause := [(53,false),(22,false),(64,false),(67,true),(75,true),(78,false),(86,false),(90,false)]
theorem inp_6797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6797 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6797 (by decide) v hb
def cl_6798 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,true),(78,false),(86,false),(90,false)]
theorem inp_6798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6798 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6798 (by decide) v hb
def cl_6799 : CNF.NClause := [(53,false),(22,false),(64,true),(67,true),(75,true),(78,false),(86,false),(90,false)]
theorem inp_6799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6799 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6799 (by decide) v hb
def cl_6800 : CNF.NClause := [(53,false),(22,true),(64,true),(67,true),(75,true),(78,false),(86,false),(90,false)]
theorem inp_6800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6800 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6800 (by decide) v hb
def cl_6801 : CNF.NClause := [(53,false),(22,false),(64,false),(67,false),(75,false),(78,true),(86,false),(90,false)]
theorem inp_6801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6801 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6801 (by decide) v hb
def cl_6802 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,false),(78,true),(86,false),(90,false)]
theorem inp_6802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6802 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_6802 v hb
def cl_6803 : CNF.NClause := [(53,false),(22,false),(64,true),(67,false),(75,false),(78,true),(86,false),(90,false)]
theorem inp_6803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6803 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6803 (by decide) v hb
def cl_6804 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(75,false),(78,true),(86,false),(90,false)]
theorem inp_6804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6804 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6804 (by decide) v hb
end Percolation.NReplay
