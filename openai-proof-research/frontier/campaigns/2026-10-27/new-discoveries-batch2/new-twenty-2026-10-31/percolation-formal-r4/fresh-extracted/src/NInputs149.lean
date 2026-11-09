import NInputs148
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_8725 : CNF.NClause := [(250,true),(255,true),(260,true),(265,true),(270,false),(273,true)]
theorem inp_8725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8725 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 2) (closed_mem 4 2) cl_8725 (by decide) v hb
def cl_8726 : CNF.NClause := [(250,true),(255,true),(260,true),(265,false),(270,true),(273,true)]
theorem inp_8726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8726 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 2) (closed_mem 4 2) cl_8726 (by decide) v hb
def cl_8727 : CNF.NClause := [(250,true),(255,true),(260,false),(265,true),(270,true),(273,true)]
theorem inp_8727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8727 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 2) (closed_mem 4 2) cl_8727 (by decide) v hb
def cl_8728 : CNF.NClause := [(250,true),(255,false),(260,true),(265,true),(270,true),(273,true)]
theorem inp_8728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8728 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 2) (closed_mem 4 2) cl_8728 (by decide) v hb
def cl_8729 : CNF.NClause := [(250,false),(255,true),(260,true),(265,true),(270,true),(273,true)]
theorem inp_8729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8729 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 2) (closed_mem 4 2) cl_8729 (by decide) v hb
def cl_8731 : CNF.NClause := [(251,true),(256,true),(261,true),(266,true),(271,false),(273,true)]
theorem inp_8731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8731 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 3) (closed_mem 4 3) cl_8731 (by decide) v hb
def cl_8733 : CNF.NClause := [(251,true),(256,true),(261,false),(266,true),(271,true),(273,true)]
theorem inp_8733 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8733 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 3) (closed_mem 4 3) cl_8733 (by decide) v hb
def cl_8734 : CNF.NClause := [(251,true),(256,false),(261,true),(266,true),(271,true),(273,true)]
theorem inp_8734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8734 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 3) (closed_mem 4 3) cl_8734 (by decide) v hb
def cl_8735 : CNF.NClause := [(251,false),(256,true),(261,true),(266,true),(271,true),(273,true)]
theorem inp_8735 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8735 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 3) (closed_mem 4 3) cl_8735 (by decide) v hb
def cl_8737 : CNF.NClause := [(249,true),(254,true),(259,true),(264,true),(269,false),(273,true)]
theorem inp_8737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8737 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 4) (closed_mem 4 4) cl_8737 (by decide) v hb
def cl_8738 : CNF.NClause := [(249,true),(254,true),(259,true),(264,false),(269,true),(273,true)]
theorem inp_8738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8738 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 4) (closed_mem 4 4) cl_8738 (by decide) v hb
def cl_8739 : CNF.NClause := [(249,true),(254,true),(259,false),(264,true),(269,true),(273,true)]
theorem inp_8739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8739 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 4) (closed_mem 4 4) cl_8739 (by decide) v hb
def cl_8740 : CNF.NClause := [(249,true),(254,false),(259,true),(264,true),(269,true),(273,true)]
theorem inp_8740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8740 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 4) (closed_mem 4 4) cl_8740 (by decide) v hb
def cl_8741 : CNF.NClause := [(249,false),(254,true),(259,true),(264,true),(269,true),(273,true)]
theorem inp_8741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8741 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 4) (closed_mem 4 4) cl_8741 (by decide) v hb
def cl_8743 : CNF.NClause := [(268,true),(269,true),(270,true),(271,true),(272,false),(278,true)]
theorem inp_8743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8743 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 5) (closed_mem 4 5) cl_8743 (by decide) v hb
def cl_8744 : CNF.NClause := [(268,true),(269,true),(270,true),(271,false),(272,true),(278,true)]
theorem inp_8744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8744 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 5) (closed_mem 4 5) cl_8744 (by decide) v hb
def cl_8746 : CNF.NClause := [(268,true),(269,false),(270,true),(271,true),(272,true),(278,true)]
theorem inp_8746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8746 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 5) (closed_mem 4 5) cl_8746 (by decide) v hb
def cl_8747 : CNF.NClause := [(268,false),(269,true),(270,true),(271,true),(272,true),(278,true)]
theorem inp_8747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8747 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 5) (closed_mem 4 5) cl_8747 (by decide) v hb
def cl_8753 : CNF.NClause := [(252,false),(256,true),(260,true),(264,true),(268,true),(277,true)]
theorem inp_8753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8753 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 6) (closed_mem 4 6) cl_8753 (by decide) v hb
def cl_8754 : CNF.NClause := [(250,true),(257,true),(259,true),(266,true),(268,true),(275,false)]
theorem inp_8754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8754 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 7) (closed_mem 4 7) cl_8754 (by decide) v hb
def cl_8755 : CNF.NClause := [(250,true),(257,true),(259,true),(266,true),(268,false),(275,true)]
theorem inp_8755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8755 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 7) (closed_mem 4 7) cl_8755 (by decide) v hb
def cl_8757 : CNF.NClause := [(250,true),(257,true),(259,false),(266,true),(268,true),(275,true)]
theorem inp_8757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8757 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 7) (closed_mem 4 7) cl_8757 (by decide) v hb
def cl_8758 : CNF.NClause := [(250,true),(257,false),(259,true),(266,true),(268,true),(275,true)]
theorem inp_8758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8758 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 7) (closed_mem 4 7) cl_8758 (by decide) v hb
def cl_8759 : CNF.NClause := [(250,false),(257,true),(259,true),(266,true),(268,true),(275,true)]
theorem inp_8759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8759 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 7) (closed_mem 4 7) cl_8759 (by decide) v hb
def cl_8760 : CNF.NClause := [(251,true),(254,true),(262,true),(265,true),(268,true),(276,false)]
theorem inp_8760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8760 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 8) (closed_mem 4 8) cl_8760 (by decide) v hb
def cl_8763 : CNF.NClause := [(251,true),(254,true),(262,false),(265,true),(268,true),(276,true)]
theorem inp_8763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8763 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 8) (closed_mem 4 8) cl_8763 (by decide) v hb
def cl_8764 : CNF.NClause := [(251,true),(254,false),(262,true),(265,true),(268,true),(276,true)]
theorem inp_8764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8764 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 8) (closed_mem 4 8) cl_8764 (by decide) v hb
def cl_8765 : CNF.NClause := [(251,false),(254,true),(262,true),(265,true),(268,true),(276,true)]
theorem inp_8765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8765 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 8) (closed_mem 4 8) cl_8765 (by decide) v hb
def cl_8767 : CNF.NClause := [(249,true),(255,true),(261,true),(267,true),(268,false),(274,true)]
theorem inp_8767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8767 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 9) (closed_mem 4 9) cl_8767 (by decide) v hb
def cl_8768 : CNF.NClause := [(249,true),(255,true),(261,true),(267,false),(268,true),(274,true)]
theorem inp_8768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8768 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 9) (closed_mem 4 9) cl_8768 (by decide) v hb
def cl_8770 : CNF.NClause := [(249,true),(255,false),(261,true),(267,true),(268,true),(274,true)]
theorem inp_8770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8770 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 9) (closed_mem 4 9) cl_8770 (by decide) v hb
def cl_8771 : CNF.NClause := [(249,false),(255,true),(261,true),(267,true),(268,true),(274,true)]
theorem inp_8771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8771 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 9) (closed_mem 4 9) cl_8771 (by decide) v hb
def cl_8774 : CNF.NClause := [(258,true),(259,true),(260,true),(261,false),(262,true),(278,true)]
theorem inp_8774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8774 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 10) (closed_mem 4 10) cl_8774 (by decide) v hb
def cl_8775 : CNF.NClause := [(258,true),(259,true),(260,false),(261,true),(262,true),(278,true)]
theorem inp_8775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8775 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 10) (closed_mem 4 10) cl_8775 (by decide) v hb
def cl_8776 : CNF.NClause := [(258,true),(259,false),(260,true),(261,true),(262,true),(278,true)]
theorem inp_8776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8776 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 10) (closed_mem 4 10) cl_8776 (by decide) v hb
def cl_8783 : CNF.NClause := [(252,false),(255,true),(258,true),(266,true),(269,true),(276,true)]
theorem inp_8783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8783 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 11) (closed_mem 4 11) cl_8783 (by decide) v hb
def cl_8784 : CNF.NClause := [(250,true),(254,true),(258,true),(267,true),(271,true),(277,false)]
theorem inp_8784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8784 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 12) (closed_mem 4 12) cl_8784 (by decide) v hb
def cl_8786 : CNF.NClause := [(250,true),(254,true),(258,true),(267,false),(271,true),(277,true)]
theorem inp_8786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8786 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 12) (closed_mem 4 12) cl_8786 (by decide) v hb
def cl_8789 : CNF.NClause := [(250,false),(254,true),(258,true),(267,true),(271,true),(277,true)]
theorem inp_8789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8789 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 12) (closed_mem 4 12) cl_8789 (by decide) v hb
def cl_8791 : CNF.NClause := [(251,true),(257,true),(258,true),(264,true),(270,false),(274,true)]
theorem inp_8791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8791 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 13) (closed_mem 4 13) cl_8791 (by decide) v hb
def cl_8793 : CNF.NClause := [(251,true),(257,true),(258,false),(264,true),(270,true),(274,true)]
theorem inp_8793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8793 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 13) (closed_mem 4 13) cl_8793 (by decide) v hb
def cl_8794 : CNF.NClause := [(251,true),(257,false),(258,true),(264,true),(270,true),(274,true)]
theorem inp_8794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8794 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 13) (closed_mem 4 13) cl_8794 (by decide) v hb
def cl_8796 : CNF.NClause := [(249,true),(256,true),(258,true),(265,true),(272,true),(275,false)]
theorem inp_8796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8796 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 14) (closed_mem 4 14) cl_8796 (by decide) v hb
def cl_8797 : CNF.NClause := [(249,true),(256,true),(258,true),(265,true),(272,false),(275,true)]
theorem inp_8797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8797 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 14) (closed_mem 4 14) cl_8797 (by decide) v hb
def cl_8799 : CNF.NClause := [(249,true),(256,true),(258,false),(265,true),(272,true),(275,true)]
theorem inp_8799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8799 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 14) (closed_mem 4 14) cl_8799 (by decide) v hb
def cl_8800 : CNF.NClause := [(249,true),(256,false),(258,true),(265,true),(272,true),(275,true)]
theorem inp_8800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8800 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 14) (closed_mem 4 14) cl_8800 (by decide) v hb
def cl_8803 : CNF.NClause := [(263,true),(264,true),(265,true),(266,true),(267,false),(278,true)]
theorem inp_8803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8803 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 15) (closed_mem 4 15) cl_8803 (by decide) v hb
def cl_8804 : CNF.NClause := [(263,true),(264,true),(265,true),(266,false),(267,true),(278,true)]
theorem inp_8804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8804 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 15) (closed_mem 4 15) cl_8804 (by decide) v hb
def cl_8805 : CNF.NClause := [(263,true),(264,true),(265,false),(266,true),(267,true),(278,true)]
theorem inp_8805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8805 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 15) (closed_mem 4 15) cl_8805 (by decide) v hb
def cl_8806 : CNF.NClause := [(263,true),(264,false),(265,true),(266,true),(267,true),(278,true)]
theorem inp_8806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8806 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 15) (closed_mem 4 15) cl_8806 (by decide) v hb
end Percolation.NReplay
