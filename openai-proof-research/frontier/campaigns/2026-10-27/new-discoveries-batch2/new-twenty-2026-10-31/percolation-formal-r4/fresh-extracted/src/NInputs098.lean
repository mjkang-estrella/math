import NInputs097
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_5666 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,false),(78,false),(84,true),(88,false)]
theorem inp_5666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5666 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5666 v hb
def cl_5667 : CNF.NClause := [(44,false),(13,false),(65,true),(71,false),(72,false),(78,false),(84,true),(88,false)]
theorem inp_5667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5667 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5667 (by decide) v hb
def cl_5668 : CNF.NClause := [(44,false),(13,true),(65,true),(71,false),(72,false),(78,false),(84,true),(88,false)]
theorem inp_5668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5668 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5668 (by decide) v hb
def cl_5669 : CNF.NClause := [(44,false),(13,false),(65,false),(71,true),(72,false),(78,false),(84,true),(88,false)]
theorem inp_5669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5669 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5669 (by decide) v hb
def cl_5670 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,false),(78,false),(84,true),(88,false)]
theorem inp_5670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5670 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5670 v hb
def cl_5671 : CNF.NClause := [(44,false),(13,false),(65,true),(71,true),(72,false),(78,false),(84,true),(88,false)]
theorem inp_5671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5671 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5671 (by decide) v hb
def cl_5672 : CNF.NClause := [(44,false),(13,true),(65,true),(71,true),(72,false),(78,false),(84,true),(88,false)]
theorem inp_5672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5672 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5672 (by decide) v hb
def cl_5673 : CNF.NClause := [(44,false),(13,false),(65,false),(71,false),(72,true),(78,false),(84,true),(88,false)]
theorem inp_5673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5673 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5673 (by decide) v hb
def cl_5674 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,true),(78,false),(84,true),(88,false)]
theorem inp_5674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5674 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5674 v hb
def cl_5675 : CNF.NClause := [(44,false),(13,false),(65,true),(71,false),(72,true),(78,false),(84,true),(88,false)]
theorem inp_5675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5675 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5675 (by decide) v hb
def cl_5676 : CNF.NClause := [(44,false),(13,true),(65,true),(71,false),(72,true),(78,false),(84,true),(88,false)]
theorem inp_5676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5676 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5676 (by decide) v hb
def cl_5677 : CNF.NClause := [(44,false),(13,false),(65,false),(71,true),(72,true),(78,false),(84,true),(88,false)]
theorem inp_5677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5677 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5677 (by decide) v hb
def cl_5678 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,true),(78,false),(84,true),(88,false)]
theorem inp_5678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5678 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5678 v hb
def cl_5679 : CNF.NClause := [(44,false),(13,false),(65,true),(71,true),(72,true),(78,false),(84,true),(88,false)]
theorem inp_5679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5679 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5679 (by decide) v hb
def cl_5680 : CNF.NClause := [(44,false),(13,true),(65,true),(71,true),(72,true),(78,false),(84,true),(88,false)]
theorem inp_5680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5680 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5680 (by decide) v hb
def cl_5681 : CNF.NClause := [(44,false),(13,false),(65,false),(71,false),(72,false),(78,true),(84,true),(88,false)]
theorem inp_5681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5681 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5681 (by decide) v hb
def cl_5682 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,false),(78,true),(84,true),(88,false)]
theorem inp_5682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5682 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5682 (by decide) v hb
def cl_5683 : CNF.NClause := [(44,false),(13,false),(65,true),(71,false),(72,false),(78,true),(84,true),(88,false)]
theorem inp_5683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5683 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5683 (by decide) v hb
def cl_5684 : CNF.NClause := [(44,false),(13,true),(65,true),(71,false),(72,false),(78,true),(84,true),(88,false)]
theorem inp_5684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5684 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5684 (by decide) v hb
def cl_5685 : CNF.NClause := [(44,false),(13,false),(65,false),(71,true),(72,false),(78,true),(84,true),(88,false)]
theorem inp_5685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5685 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5685 (by decide) v hb
def cl_5686 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,false),(78,true),(84,true),(88,false)]
theorem inp_5686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5686 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5686 (by decide) v hb
def cl_5687 : CNF.NClause := [(44,false),(13,false),(65,true),(71,true),(72,false),(78,true),(84,true),(88,false)]
theorem inp_5687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5687 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5687 (by decide) v hb
def cl_5688 : CNF.NClause := [(44,false),(13,true),(65,true),(71,true),(72,false),(78,true),(84,true),(88,false)]
theorem inp_5688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5688 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5688 (by decide) v hb
def cl_5689 : CNF.NClause := [(44,false),(13,false),(65,false),(71,false),(72,true),(78,true),(84,true),(88,false)]
theorem inp_5689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5689 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5689 (by decide) v hb
def cl_5690 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,true),(78,true),(84,true),(88,false)]
theorem inp_5690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5690 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5690 (by decide) v hb
def cl_5691 : CNF.NClause := [(44,false),(13,false),(65,true),(71,false),(72,true),(78,true),(84,true),(88,false)]
theorem inp_5691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5691 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5691 (by decide) v hb
def cl_5692 : CNF.NClause := [(44,false),(13,true),(65,true),(71,false),(72,true),(78,true),(84,true),(88,false)]
theorem inp_5692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5692 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5692 (by decide) v hb
def cl_5693 : CNF.NClause := [(44,false),(13,false),(65,false),(71,true),(72,true),(78,true),(84,true),(88,false)]
theorem inp_5693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5693 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5693 (by decide) v hb
def cl_5694 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,true),(78,true),(84,true),(88,false)]
theorem inp_5694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5694 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5694 (by decide) v hb
def cl_5695 : CNF.NClause := [(44,false),(13,false),(65,true),(71,true),(72,true),(78,true),(84,true),(88,false)]
theorem inp_5695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5695 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5695 (by decide) v hb
def cl_5696 : CNF.NClause := [(44,false),(13,true),(65,true),(71,true),(72,true),(78,true),(84,true),(88,false)]
theorem inp_5696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5696 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5696 (by decide) v hb
def cl_5697 : CNF.NClause := [(44,false),(13,false),(65,false),(71,false),(72,false),(78,false),(84,false),(88,true)]
theorem inp_5697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5697 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5697 (by decide) v hb
def cl_5698 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,false),(78,false),(84,false),(88,true)]
theorem inp_5698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5698 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5698 v hb
def cl_5699 : CNF.NClause := [(44,false),(13,false),(65,true),(71,false),(72,false),(78,false),(84,false),(88,true)]
theorem inp_5699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5699 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5699 (by decide) v hb
def cl_5700 : CNF.NClause := [(44,false),(13,true),(65,true),(71,false),(72,false),(78,false),(84,false),(88,true)]
theorem inp_5700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5700 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5700 (by decide) v hb
def cl_5701 : CNF.NClause := [(44,false),(13,false),(65,false),(71,true),(72,false),(78,false),(84,false),(88,true)]
theorem inp_5701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5701 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5701 (by decide) v hb
def cl_5702 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,false),(78,false),(84,false),(88,true)]
theorem inp_5702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5702 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_5702 v hb
def cl_5703 : CNF.NClause := [(44,false),(13,false),(65,true),(71,true),(72,false),(78,false),(84,false),(88,true)]
theorem inp_5703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5703 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5703 (by decide) v hb
def cl_5704 : CNF.NClause := [(44,false),(13,true),(65,true),(71,true),(72,false),(78,false),(84,false),(88,true)]
theorem inp_5704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5704 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5704 (by decide) v hb
def cl_5705 : CNF.NClause := [(44,false),(13,false),(65,false),(71,false),(72,true),(78,false),(84,false),(88,true)]
theorem inp_5705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5705 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5705 (by decide) v hb
def cl_5706 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,true),(78,false),(84,false),(88,true)]
theorem inp_5706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5706 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5706 (by decide) v hb
def cl_5707 : CNF.NClause := [(44,false),(13,false),(65,true),(71,false),(72,true),(78,false),(84,false),(88,true)]
theorem inp_5707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5707 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5707 (by decide) v hb
def cl_5708 : CNF.NClause := [(44,false),(13,true),(65,true),(71,false),(72,true),(78,false),(84,false),(88,true)]
theorem inp_5708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5708 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5708 (by decide) v hb
def cl_5709 : CNF.NClause := [(44,false),(13,false),(65,false),(71,true),(72,true),(78,false),(84,false),(88,true)]
theorem inp_5709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5709 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5709 (by decide) v hb
def cl_5710 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,true),(78,false),(84,false),(88,true)]
theorem inp_5710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5710 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5710 (by decide) v hb
def cl_5711 : CNF.NClause := [(44,false),(13,false),(65,true),(71,true),(72,true),(78,false),(84,false),(88,true)]
theorem inp_5711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5711 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5711 (by decide) v hb
def cl_5712 : CNF.NClause := [(44,false),(13,true),(65,true),(71,true),(72,true),(78,false),(84,false),(88,true)]
theorem inp_5712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5712 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5712 (by decide) v hb
def cl_5713 : CNF.NClause := [(44,false),(13,false),(65,false),(71,false),(72,false),(78,true),(84,false),(88,true)]
theorem inp_5713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5713 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5713 (by decide) v hb
def cl_5714 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,false),(78,true),(84,false),(88,true)]
theorem inp_5714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5714 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5714 (by decide) v hb
def cl_5715 : CNF.NClause := [(44,false),(13,false),(65,true),(71,false),(72,false),(78,true),(84,false),(88,true)]
theorem inp_5715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_5715 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) cl_5715 (by decide) v hb
end Percolation.NReplay
