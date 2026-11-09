import NInputs136
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_7751 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(74,false),(80,false),(86,false),(88,true)]
theorem inp_7751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7751 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7751 (by decide) v hb
def cl_7752 : CNF.NClause := [(60,false),(29,true),(62,true),(68,true),(74,false),(80,false),(86,false),(88,true)]
theorem inp_7752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7752 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7752 (by decide) v hb
def cl_7753 : CNF.NClause := [(60,false),(29,false),(62,false),(68,false),(74,true),(80,false),(86,false),(88,true)]
theorem inp_7753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7753 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7753 (by decide) v hb
def cl_7754 : CNF.NClause := [(60,false),(29,true),(62,false),(68,false),(74,true),(80,false),(86,false),(88,true)]
theorem inp_7754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7754 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7754 (by decide) v hb
def cl_7755 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,true),(80,false),(86,false),(88,true)]
theorem inp_7755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7755 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7755 (by decide) v hb
def cl_7756 : CNF.NClause := [(60,false),(29,true),(62,true),(68,false),(74,true),(80,false),(86,false),(88,true)]
theorem inp_7756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7756 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7756 (by decide) v hb
def cl_7757 : CNF.NClause := [(60,false),(29,false),(62,false),(68,true),(74,true),(80,false),(86,false),(88,true)]
theorem inp_7757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7757 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7757 (by decide) v hb
def cl_7758 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(74,true),(80,false),(86,false),(88,true)]
theorem inp_7758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7758 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7758 (by decide) v hb
def cl_7759 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(74,true),(80,false),(86,false),(88,true)]
theorem inp_7759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7759 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7759 (by decide) v hb
def cl_7760 : CNF.NClause := [(60,false),(29,true),(62,true),(68,true),(74,true),(80,false),(86,false),(88,true)]
theorem inp_7760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7760 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7760 (by decide) v hb
def cl_7761 : CNF.NClause := [(60,false),(29,false),(62,false),(68,false),(74,false),(80,true),(86,false),(88,true)]
theorem inp_7761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7761 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7761 (by decide) v hb
def cl_7762 : CNF.NClause := [(60,false),(29,true),(62,false),(68,false),(74,false),(80,true),(86,false),(88,true)]
theorem inp_7762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7762 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7762 (by decide) v hb
def cl_7763 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,false),(80,true),(86,false),(88,true)]
theorem inp_7763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7763 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7763 (by decide) v hb
def cl_7764 : CNF.NClause := [(60,false),(29,true),(62,true),(68,false),(74,false),(80,true),(86,false),(88,true)]
theorem inp_7764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7764 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7764 (by decide) v hb
def cl_7765 : CNF.NClause := [(60,false),(29,false),(62,false),(68,true),(74,false),(80,true),(86,false),(88,true)]
theorem inp_7765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7765 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7765 (by decide) v hb
def cl_7766 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(74,false),(80,true),(86,false),(88,true)]
theorem inp_7766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7766 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7766 (by decide) v hb
def cl_7767 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(74,false),(80,true),(86,false),(88,true)]
theorem inp_7767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7767 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7767 (by decide) v hb
def cl_7768 : CNF.NClause := [(60,false),(29,true),(62,true),(68,true),(74,false),(80,true),(86,false),(88,true)]
theorem inp_7768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7768 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7768 (by decide) v hb
def cl_7769 : CNF.NClause := [(60,false),(29,false),(62,false),(68,false),(74,true),(80,true),(86,false),(88,true)]
theorem inp_7769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7769 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7769 (by decide) v hb
def cl_7770 : CNF.NClause := [(60,false),(29,true),(62,false),(68,false),(74,true),(80,true),(86,false),(88,true)]
theorem inp_7770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7770 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7770 (by decide) v hb
def cl_7771 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,true),(80,true),(86,false),(88,true)]
theorem inp_7771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7771 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7771 (by decide) v hb
def cl_7772 : CNF.NClause := [(60,false),(29,true),(62,true),(68,false),(74,true),(80,true),(86,false),(88,true)]
theorem inp_7772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7772 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7772 (by decide) v hb
def cl_7773 : CNF.NClause := [(60,false),(29,false),(62,false),(68,true),(74,true),(80,true),(86,false),(88,true)]
theorem inp_7773 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7773 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7773 (by decide) v hb
def cl_7774 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(74,true),(80,true),(86,false),(88,true)]
theorem inp_7774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7774 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7774 (by decide) v hb
def cl_7776 : CNF.NClause := [(60,false),(29,true),(62,true),(68,true),(74,true),(80,true),(86,false),(88,true)]
theorem inp_7776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7776 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7776 (by decide) v hb
def cl_7777 : CNF.NClause := [(60,false),(29,false),(62,false),(68,false),(74,false),(80,false),(86,true),(88,true)]
theorem inp_7777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7777 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7777 (by decide) v hb
def cl_7778 : CNF.NClause := [(60,false),(29,true),(62,false),(68,false),(74,false),(80,false),(86,true),(88,true)]
theorem inp_7778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7778 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7778 (by decide) v hb
def cl_7779 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,false),(80,false),(86,true),(88,true)]
theorem inp_7779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7779 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7779 (by decide) v hb
def cl_7780 : CNF.NClause := [(60,false),(29,true),(62,true),(68,false),(74,false),(80,false),(86,true),(88,true)]
theorem inp_7780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7780 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7780 (by decide) v hb
def cl_7781 : CNF.NClause := [(60,false),(29,false),(62,false),(68,true),(74,false),(80,false),(86,true),(88,true)]
theorem inp_7781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7781 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7781 (by decide) v hb
def cl_7782 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(74,false),(80,false),(86,true),(88,true)]
theorem inp_7782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7782 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7782 (by decide) v hb
def cl_7783 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(74,false),(80,false),(86,true),(88,true)]
theorem inp_7783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7783 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7783 (by decide) v hb
def cl_7784 : CNF.NClause := [(60,false),(29,true),(62,true),(68,true),(74,false),(80,false),(86,true),(88,true)]
theorem inp_7784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7784 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7784 (by decide) v hb
def cl_7785 : CNF.NClause := [(60,false),(29,false),(62,false),(68,false),(74,true),(80,false),(86,true),(88,true)]
theorem inp_7785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7785 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7785 (by decide) v hb
def cl_7786 : CNF.NClause := [(60,false),(29,true),(62,false),(68,false),(74,true),(80,false),(86,true),(88,true)]
theorem inp_7786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7786 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7786 (by decide) v hb
def cl_7787 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,true),(80,false),(86,true),(88,true)]
theorem inp_7787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7787 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7787 (by decide) v hb
def cl_7788 : CNF.NClause := [(60,false),(29,true),(62,true),(68,false),(74,true),(80,false),(86,true),(88,true)]
theorem inp_7788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7788 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7788 (by decide) v hb
def cl_7789 : CNF.NClause := [(60,false),(29,false),(62,false),(68,true),(74,true),(80,false),(86,true),(88,true)]
theorem inp_7789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7789 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7789 (by decide) v hb
def cl_7790 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(74,true),(80,false),(86,true),(88,true)]
theorem inp_7790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7790 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7790 (by decide) v hb
def cl_7791 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(74,true),(80,false),(86,true),(88,true)]
theorem inp_7791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7791 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7791 (by decide) v hb
def cl_7792 : CNF.NClause := [(60,false),(29,true),(62,true),(68,true),(74,true),(80,false),(86,true),(88,true)]
theorem inp_7792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7792 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7792 (by decide) v hb
def cl_7793 : CNF.NClause := [(60,false),(29,false),(62,false),(68,false),(74,false),(80,true),(86,true),(88,true)]
theorem inp_7793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7793 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7793 (by decide) v hb
def cl_7794 : CNF.NClause := [(60,false),(29,true),(62,false),(68,false),(74,false),(80,true),(86,true),(88,true)]
theorem inp_7794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7794 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7794 (by decide) v hb
def cl_7795 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,false),(80,true),(86,true),(88,true)]
theorem inp_7795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7795 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7795 (by decide) v hb
def cl_7796 : CNF.NClause := [(60,false),(29,true),(62,true),(68,false),(74,false),(80,true),(86,true),(88,true)]
theorem inp_7796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7796 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7796 (by decide) v hb
def cl_7797 : CNF.NClause := [(60,false),(29,false),(62,false),(68,true),(74,false),(80,true),(86,true),(88,true)]
theorem inp_7797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7797 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7797 (by decide) v hb
def cl_7798 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(74,false),(80,true),(86,true),(88,true)]
theorem inp_7798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7798 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7798 (by decide) v hb
def cl_7799 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(74,false),(80,true),(86,true),(88,true)]
theorem inp_7799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7799 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7799 (by decide) v hb
def cl_7800 : CNF.NClause := [(60,false),(29,true),(62,true),(68,true),(74,false),(80,true),(86,true),(88,true)]
theorem inp_7800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7800 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7800 (by decide) v hb
def cl_7801 : CNF.NClause := [(60,false),(29,false),(62,false),(68,false),(74,true),(80,true),(86,true),(88,true)]
theorem inp_7801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7801 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7801 (by decide) v hb
end Percolation.NReplay
