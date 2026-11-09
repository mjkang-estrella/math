import NInputs147
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_8650 : CNF.NClause := [(222,true),(223,false),(224,true),(225,true),(226,true),(247,true)]
theorem inp_8650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8650 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 20) (closed_mem 3 20) cl_8650 (by decide) v hb
def cl_8651 : CNF.NClause := [(222,false),(223,true),(224,true),(225,true),(226,true),(247,true)]
theorem inp_8651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8651 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 20) (closed_mem 3 20) cl_8651 (by decide) v hb
def cl_8653 : CNF.NClause := [(221,true),(222,true),(228,true),(234,true),(240,false),(243,true)]
theorem inp_8653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8653 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 21) (closed_mem 3 21) cl_8653 (by decide) v hb
def cl_8654 : CNF.NClause := [(221,true),(222,true),(228,true),(234,false),(240,true),(243,true)]
theorem inp_8654 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8654 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 21) (closed_mem 3 21) cl_8654 (by decide) v hb
def cl_8655 : CNF.NClause := [(221,true),(222,true),(228,false),(234,true),(240,true),(243,true)]
theorem inp_8655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8655 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 21) (closed_mem 3 21) cl_8655 (by decide) v hb
def cl_8656 : CNF.NClause := [(221,true),(222,false),(228,true),(234,true),(240,true),(243,true)]
theorem inp_8656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8656 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 21) (closed_mem 3 21) cl_8656 (by decide) v hb
def cl_8657 : CNF.NClause := [(221,false),(222,true),(228,true),(234,true),(240,true),(243,true)]
theorem inp_8657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8657 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 21) (closed_mem 3 21) cl_8657 (by decide) v hb
def cl_8658 : CNF.NClause := [(219,true),(222,true),(230,true),(233,true),(241,true),(245,false)]
theorem inp_8658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8658 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 22) (closed_mem 3 22) cl_8658 (by decide) v hb
def cl_8659 : CNF.NClause := [(219,true),(222,true),(230,true),(233,true),(241,false),(245,true)]
theorem inp_8659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8659 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_8659 v hb
def cl_8660 : CNF.NClause := [(219,true),(222,true),(230,true),(233,false),(241,true),(245,true)]
theorem inp_8660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8660 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 22) (closed_mem 3 22) cl_8660 (by decide) v hb
def cl_8661 : CNF.NClause := [(219,true),(222,true),(230,false),(233,true),(241,true),(245,true)]
theorem inp_8661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8661 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 22) (closed_mem 3 22) cl_8661 (by decide) v hb
def cl_8662 : CNF.NClause := [(219,true),(222,false),(230,true),(233,true),(241,true),(245,true)]
theorem inp_8662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8662 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 22) (closed_mem 3 22) cl_8662 (by decide) v hb
def cl_8663 : CNF.NClause := [(219,false),(222,true),(230,true),(233,true),(241,true),(245,true)]
theorem inp_8663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8663 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 22) (closed_mem 3 22) cl_8663 (by decide) v hb
def cl_8669 : CNF.NClause := [(220,false),(222,true),(229,true),(236,true),(238,true),(244,true)]
theorem inp_8669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8669 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 23) (closed_mem 3 23) cl_8669 (by decide) v hb
def cl_8670 : CNF.NClause := [(218,true),(222,true),(231,true),(235,true),(239,true),(246,false)]
theorem inp_8670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8670 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 24) (closed_mem 3 24) cl_8670 (by decide) v hb
def cl_8671 : CNF.NClause := [(218,true),(222,true),(231,true),(235,true),(239,false),(246,true)]
theorem inp_8671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8671 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_8671 v hb
def cl_8672 : CNF.NClause := [(218,true),(222,true),(231,true),(235,false),(239,true),(246,true)]
theorem inp_8672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8672 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 24) (closed_mem 3 24) cl_8672 (by decide) v hb
def cl_8673 : CNF.NClause := [(218,true),(222,true),(231,false),(235,true),(239,true),(246,true)]
theorem inp_8673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8673 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 24) (closed_mem 3 24) cl_8673 (by decide) v hb
def cl_8674 : CNF.NClause := [(218,true),(222,false),(231,true),(235,true),(239,true),(246,true)]
theorem inp_8674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8674 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 24) (closed_mem 3 24) cl_8674 (by decide) v hb
def cl_8675 : CNF.NClause := [(218,false),(222,true),(231,true),(235,true),(239,true),(246,true)]
theorem inp_8675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8675 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 24) (closed_mem 3 24) cl_8675 (by decide) v hb
def cl_8678 : CNF.NClause := [(217,true),(218,true),(219,true),(220,false),(221,true),(247,true)]
theorem inp_8678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8678 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 25) (closed_mem 3 25) cl_8678 (by decide) v hb
def cl_8682 : CNF.NClause := [(217,true),(226,true),(230,true),(234,true),(238,true),(246,false)]
theorem inp_8682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8682 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 26) (closed_mem 3 26) cl_8682 (by decide) v hb
def cl_8683 : CNF.NClause := [(217,true),(226,true),(230,true),(234,true),(238,false),(246,true)]
theorem inp_8683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8683 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 26) (closed_mem 3 26) cl_8683 (by decide) v hb
def cl_8684 : CNF.NClause := [(217,true),(226,true),(230,true),(234,false),(238,true),(246,true)]
theorem inp_8684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8684 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_8684 v hb
def cl_8685 : CNF.NClause := [(217,true),(226,true),(230,false),(234,true),(238,true),(246,true)]
theorem inp_8685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8685 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_8685 v hb
def cl_8686 : CNF.NClause := [(217,true),(226,false),(230,true),(234,true),(238,true),(246,true)]
theorem inp_8686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8686 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 26) (closed_mem 3 26) cl_8686 (by decide) v hb
def cl_8688 : CNF.NClause := [(217,true),(224,true),(231,true),(233,true),(240,true),(244,false)]
theorem inp_8688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8688 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 27) (closed_mem 3 27) cl_8688 (by decide) v hb
def cl_8689 : CNF.NClause := [(217,true),(224,true),(231,true),(233,true),(240,false),(244,true)]
theorem inp_8689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8689 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 27) (closed_mem 3 27) cl_8689 (by decide) v hb
def cl_8690 : CNF.NClause := [(217,true),(224,true),(231,true),(233,false),(240,true),(244,true)]
theorem inp_8690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8690 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 27) (closed_mem 3 27) cl_8690 (by decide) v hb
def cl_8691 : CNF.NClause := [(217,true),(224,true),(231,false),(233,true),(240,true),(244,true)]
theorem inp_8691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8691 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 27) (closed_mem 3 27) cl_8691 (by decide) v hb
def cl_8692 : CNF.NClause := [(217,true),(224,false),(231,true),(233,true),(240,true),(244,true)]
theorem inp_8692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8692 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 27) (closed_mem 3 27) cl_8692 (by decide) v hb
def cl_8694 : CNF.NClause := [(217,true),(225,true),(228,true),(236,true),(239,true),(245,false)]
theorem inp_8694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8694 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 28) (closed_mem 3 28) cl_8694 (by decide) v hb
def cl_8695 : CNF.NClause := [(217,true),(225,true),(228,true),(236,true),(239,false),(245,true)]
theorem inp_8695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8695 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 28) (closed_mem 3 28) cl_8695 (by decide) v hb
def cl_8696 : CNF.NClause := [(217,true),(225,true),(228,true),(236,false),(239,true),(245,true)]
theorem inp_8696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8696 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 28) (closed_mem 3 28) cl_8696 (by decide) v hb
def cl_8697 : CNF.NClause := [(217,true),(225,true),(228,false),(236,true),(239,true),(245,true)]
theorem inp_8697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8697 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_8697 v hb
def cl_8698 : CNF.NClause := [(217,true),(225,false),(228,true),(236,true),(239,true),(245,true)]
theorem inp_8698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8698 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 28) (closed_mem 3 28) cl_8698 (by decide) v hb
def cl_8700 : CNF.NClause := [(217,true),(223,true),(229,true),(235,true),(241,true),(243,false)]
theorem inp_8700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8700 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 29) (closed_mem 3 29) cl_8700 (by decide) v hb
def cl_8701 : CNF.NClause := [(217,true),(223,true),(229,true),(235,true),(241,false),(243,true)]
theorem inp_8701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8701 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 29) (closed_mem 3 29) cl_8701 (by decide) v hb
def cl_8702 : CNF.NClause := [(217,true),(223,true),(229,true),(235,false),(241,true),(243,true)]
theorem inp_8702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8702 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 29) (closed_mem 3 29) cl_8702 (by decide) v hb
def cl_8703 : CNF.NClause := [(217,true),(223,true),(229,false),(235,true),(241,true),(243,true)]
theorem inp_8703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8703 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 29) (closed_mem 3 29) cl_8703 (by decide) v hb
def cl_8704 : CNF.NClause := [(217,true),(223,false),(229,true),(235,true),(241,true),(243,true)]
theorem inp_8704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8704 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 29) (closed_mem 3 29) cl_8704 (by decide) v hb
def cl_8707 : CNF.NClause := [(217,true),(222,true),(227,true),(232,true),(237,false),(242,true)]
theorem inp_8707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8707 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 30) (closed_mem 3 30) cl_8707 (by decide) v hb
def cl_8708 : CNF.NClause := [(217,true),(222,true),(227,true),(232,false),(237,true),(242,true)]
theorem inp_8708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8708 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 30) (closed_mem 3 30) cl_8708 (by decide) v hb
def cl_8709 : CNF.NClause := [(217,true),(222,true),(227,false),(232,true),(237,true),(242,true)]
theorem inp_8709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8709 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 30) (closed_mem 3 30) cl_8709 (by decide) v hb
def cl_8710 : CNF.NClause := [(217,true),(222,false),(227,true),(232,true),(237,true),(242,true)]
theorem inp_8710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8710 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 30) (closed_mem 3 30) cl_8710 (by decide) v hb
def cl_8713 : CNF.NClause := [(273,true),(274,true),(275,true),(276,true),(277,false),(278,true)]
theorem inp_8713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8713 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 0) (closed_mem 4 0) cl_8713 (by decide) v hb
def cl_8714 : CNF.NClause := [(273,true),(274,true),(275,true),(276,false),(277,true),(278,true)]
theorem inp_8714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8714 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 0) (closed_mem 4 0) cl_8714 (by decide) v hb
def cl_8715 : CNF.NClause := [(273,true),(274,true),(275,false),(276,true),(277,true),(278,true)]
theorem inp_8715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8715 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 0) (closed_mem 4 0) cl_8715 (by decide) v hb
def cl_8716 : CNF.NClause := [(273,true),(274,false),(275,true),(276,true),(277,true),(278,true)]
theorem inp_8716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8716 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 0) (closed_mem 4 0) cl_8716 (by decide) v hb
def cl_8723 : CNF.NClause := [(252,false),(257,true),(262,true),(267,true),(272,true),(273,true)]
theorem inp_8723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8723 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 1) (closed_mem 4 1) cl_8723 (by decide) v hb
end Percolation.NReplay
