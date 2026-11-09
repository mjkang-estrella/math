import NInputs134
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_7647 : CNF.NClause := [(59,false),(28,false),(62,true),(70,true),(73,true),(81,true),(84,false),(90,true)]
theorem inp_7647 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7647 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7647 (by decide) v hb
def cl_7648 : CNF.NClause := [(59,false),(28,true),(62,true),(70,true),(73,true),(81,true),(84,false),(90,true)]
theorem inp_7648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7648 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7648 (by decide) v hb
def cl_7649 : CNF.NClause := [(59,false),(28,false),(62,false),(70,false),(73,false),(81,false),(84,true),(90,true)]
theorem inp_7649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7649 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7649 (by decide) v hb
def cl_7650 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,false),(81,false),(84,true),(90,true)]
theorem inp_7650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7650 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7650 (by decide) v hb
def cl_7651 : CNF.NClause := [(59,false),(28,false),(62,true),(70,false),(73,false),(81,false),(84,true),(90,true)]
theorem inp_7651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7651 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7651 (by decide) v hb
def cl_7652 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,false),(81,false),(84,true),(90,true)]
theorem inp_7652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7652 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7652 (by decide) v hb
def cl_7653 : CNF.NClause := [(59,false),(28,false),(62,false),(70,true),(73,false),(81,false),(84,true),(90,true)]
theorem inp_7653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7653 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7653 (by decide) v hb
def cl_7654 : CNF.NClause := [(59,false),(28,true),(62,false),(70,true),(73,false),(81,false),(84,true),(90,true)]
theorem inp_7654 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7654 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7654 (by decide) v hb
def cl_7655 : CNF.NClause := [(59,false),(28,false),(62,true),(70,true),(73,false),(81,false),(84,true),(90,true)]
theorem inp_7655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7655 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7655 (by decide) v hb
def cl_7656 : CNF.NClause := [(59,false),(28,true),(62,true),(70,true),(73,false),(81,false),(84,true),(90,true)]
theorem inp_7656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7656 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7656 (by decide) v hb
def cl_7657 : CNF.NClause := [(59,false),(28,false),(62,false),(70,false),(73,true),(81,false),(84,true),(90,true)]
theorem inp_7657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7657 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7657 (by decide) v hb
def cl_7658 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,true),(81,false),(84,true),(90,true)]
theorem inp_7658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7658 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7658 (by decide) v hb
def cl_7659 : CNF.NClause := [(59,false),(28,false),(62,true),(70,false),(73,true),(81,false),(84,true),(90,true)]
theorem inp_7659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7659 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7659 (by decide) v hb
def cl_7660 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,true),(81,false),(84,true),(90,true)]
theorem inp_7660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7660 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7660 (by decide) v hb
def cl_7661 : CNF.NClause := [(59,false),(28,false),(62,false),(70,true),(73,true),(81,false),(84,true),(90,true)]
theorem inp_7661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7661 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7661 (by decide) v hb
def cl_7662 : CNF.NClause := [(59,false),(28,true),(62,false),(70,true),(73,true),(81,false),(84,true),(90,true)]
theorem inp_7662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7662 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7662 (by decide) v hb
def cl_7663 : CNF.NClause := [(59,false),(28,false),(62,true),(70,true),(73,true),(81,false),(84,true),(90,true)]
theorem inp_7663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7663 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7663 (by decide) v hb
def cl_7664 : CNF.NClause := [(59,false),(28,true),(62,true),(70,true),(73,true),(81,false),(84,true),(90,true)]
theorem inp_7664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7664 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7664 (by decide) v hb
def cl_7665 : CNF.NClause := [(59,false),(28,false),(62,false),(70,false),(73,false),(81,true),(84,true),(90,true)]
theorem inp_7665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7665 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7665 (by decide) v hb
def cl_7666 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,false),(81,true),(84,true),(90,true)]
theorem inp_7666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7666 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7666 (by decide) v hb
def cl_7667 : CNF.NClause := [(59,false),(28,false),(62,true),(70,false),(73,false),(81,true),(84,true),(90,true)]
theorem inp_7667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7667 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7667 (by decide) v hb
def cl_7668 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,false),(81,true),(84,true),(90,true)]
theorem inp_7668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7668 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7668 (by decide) v hb
def cl_7669 : CNF.NClause := [(59,false),(28,false),(62,false),(70,true),(73,false),(81,true),(84,true),(90,true)]
theorem inp_7669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7669 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7669 (by decide) v hb
def cl_7670 : CNF.NClause := [(59,false),(28,true),(62,false),(70,true),(73,false),(81,true),(84,true),(90,true)]
theorem inp_7670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7670 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7670 (by decide) v hb
def cl_7671 : CNF.NClause := [(59,false),(28,false),(62,true),(70,true),(73,false),(81,true),(84,true),(90,true)]
theorem inp_7671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7671 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7671 (by decide) v hb
def cl_7672 : CNF.NClause := [(59,false),(28,true),(62,true),(70,true),(73,false),(81,true),(84,true),(90,true)]
theorem inp_7672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7672 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7672 (by decide) v hb
def cl_7673 : CNF.NClause := [(59,false),(28,false),(62,false),(70,false),(73,true),(81,true),(84,true),(90,true)]
theorem inp_7673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7673 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7673 (by decide) v hb
def cl_7674 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,true),(81,true),(84,true),(90,true)]
theorem inp_7674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7674 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7674 (by decide) v hb
def cl_7676 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,true),(81,true),(84,true),(90,true)]
theorem inp_7676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7676 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7676 (by decide) v hb
def cl_7678 : CNF.NClause := [(59,false),(28,true),(62,false),(70,true),(73,true),(81,true),(84,true),(90,true)]
theorem inp_7678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7678 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7678 (by decide) v hb
def cl_7680 : CNF.NClause := [(59,false),(28,true),(62,true),(70,true),(73,true),(81,true),(84,true),(90,true)]
theorem inp_7680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7680 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) cl_7680 (by decide) v hb
def cl_7681 : CNF.NClause := [(60,true),(29,false),(62,false),(68,false),(74,false),(80,false),(86,false),(88,false)]
theorem inp_7681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7681 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7681 (by decide) v hb
def cl_7682 : CNF.NClause := [(60,false),(29,true),(62,false),(68,false),(74,false),(80,false),(86,false),(88,false)]
theorem inp_7682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7682 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7682 (by decide) v hb
def cl_7683 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,false),(80,false),(86,false),(88,false)]
theorem inp_7683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7683 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7683 (by decide) v hb
def cl_7684 : CNF.NClause := [(60,false),(29,true),(62,true),(68,false),(74,false),(80,false),(86,false),(88,false)]
theorem inp_7684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7684 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7684 (by decide) v hb
def cl_7685 : CNF.NClause := [(60,false),(29,false),(62,false),(68,true),(74,false),(80,false),(86,false),(88,false)]
theorem inp_7685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7685 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7685 (by decide) v hb
def cl_7686 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(74,false),(80,false),(86,false),(88,false)]
theorem inp_7686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7686 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7686 (by decide) v hb
def cl_7687 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(74,false),(80,false),(86,false),(88,false)]
theorem inp_7687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7687 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7687 (by decide) v hb
def cl_7688 : CNF.NClause := [(60,false),(29,true),(62,true),(68,true),(74,false),(80,false),(86,false),(88,false)]
theorem inp_7688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7688 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7688 (by decide) v hb
def cl_7689 : CNF.NClause := [(60,false),(29,false),(62,false),(68,false),(74,true),(80,false),(86,false),(88,false)]
theorem inp_7689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7689 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7689 (by decide) v hb
def cl_7690 : CNF.NClause := [(60,false),(29,true),(62,false),(68,false),(74,true),(80,false),(86,false),(88,false)]
theorem inp_7690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7690 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7690 (by decide) v hb
def cl_7691 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,true),(80,false),(86,false),(88,false)]
theorem inp_7691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7691 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7691 (by decide) v hb
def cl_7692 : CNF.NClause := [(60,false),(29,true),(62,true),(68,false),(74,true),(80,false),(86,false),(88,false)]
theorem inp_7692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7692 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7692 (by decide) v hb
def cl_7693 : CNF.NClause := [(60,false),(29,false),(62,false),(68,true),(74,true),(80,false),(86,false),(88,false)]
theorem inp_7693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7693 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7693 (by decide) v hb
def cl_7694 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(74,true),(80,false),(86,false),(88,false)]
theorem inp_7694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7694 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7694 (by decide) v hb
def cl_7695 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(74,true),(80,false),(86,false),(88,false)]
theorem inp_7695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7695 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7695 (by decide) v hb
def cl_7696 : CNF.NClause := [(60,false),(29,true),(62,true),(68,true),(74,true),(80,false),(86,false),(88,false)]
theorem inp_7696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7696 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7696 (by decide) v hb
def cl_7697 : CNF.NClause := [(60,false),(29,false),(62,false),(68,false),(74,false),(80,true),(86,false),(88,false)]
theorem inp_7697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7697 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7697 (by decide) v hb
def cl_7698 : CNF.NClause := [(60,false),(29,true),(62,false),(68,false),(74,false),(80,true),(86,false),(88,false)]
theorem inp_7698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7698 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7698 (by decide) v hb
def cl_7699 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,false),(80,true),(86,false),(88,false)]
theorem inp_7699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7699 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7699 (by decide) v hb
end Percolation.NReplay
