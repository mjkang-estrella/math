import NInputs135
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_7700 : CNF.NClause := [(60,false),(29,true),(62,true),(68,false),(74,false),(80,true),(86,false),(88,false)]
theorem inp_7700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7700 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7700 (by decide) v hb
def cl_7701 : CNF.NClause := [(60,false),(29,false),(62,false),(68,true),(74,false),(80,true),(86,false),(88,false)]
theorem inp_7701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7701 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7701 (by decide) v hb
def cl_7702 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(74,false),(80,true),(86,false),(88,false)]
theorem inp_7702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7702 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7702 (by decide) v hb
def cl_7703 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(74,false),(80,true),(86,false),(88,false)]
theorem inp_7703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7703 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7703 (by decide) v hb
def cl_7704 : CNF.NClause := [(60,false),(29,true),(62,true),(68,true),(74,false),(80,true),(86,false),(88,false)]
theorem inp_7704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7704 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7704 (by decide) v hb
def cl_7705 : CNF.NClause := [(60,false),(29,false),(62,false),(68,false),(74,true),(80,true),(86,false),(88,false)]
theorem inp_7705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7705 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7705 (by decide) v hb
def cl_7706 : CNF.NClause := [(60,false),(29,true),(62,false),(68,false),(74,true),(80,true),(86,false),(88,false)]
theorem inp_7706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7706 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7706 (by decide) v hb
def cl_7707 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,true),(80,true),(86,false),(88,false)]
theorem inp_7707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7707 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7707 (by decide) v hb
def cl_7708 : CNF.NClause := [(60,false),(29,true),(62,true),(68,false),(74,true),(80,true),(86,false),(88,false)]
theorem inp_7708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7708 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7708 (by decide) v hb
def cl_7710 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(74,true),(80,true),(86,false),(88,false)]
theorem inp_7710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7710 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7710 (by decide) v hb
def cl_7711 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(74,true),(80,true),(86,false),(88,false)]
theorem inp_7711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7711 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7711 (by decide) v hb
def cl_7712 : CNF.NClause := [(60,false),(29,true),(62,true),(68,true),(74,true),(80,true),(86,false),(88,false)]
theorem inp_7712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7712 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7712 (by decide) v hb
def cl_7713 : CNF.NClause := [(60,false),(29,false),(62,false),(68,false),(74,false),(80,false),(86,true),(88,false)]
theorem inp_7713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7713 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7713 (by decide) v hb
def cl_7714 : CNF.NClause := [(60,false),(29,true),(62,false),(68,false),(74,false),(80,false),(86,true),(88,false)]
theorem inp_7714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7714 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7714 (by decide) v hb
def cl_7715 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,false),(80,false),(86,true),(88,false)]
theorem inp_7715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7715 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7715 (by decide) v hb
def cl_7716 : CNF.NClause := [(60,false),(29,true),(62,true),(68,false),(74,false),(80,false),(86,true),(88,false)]
theorem inp_7716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7716 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7716 (by decide) v hb
def cl_7717 : CNF.NClause := [(60,false),(29,false),(62,false),(68,true),(74,false),(80,false),(86,true),(88,false)]
theorem inp_7717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7717 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7717 (by decide) v hb
def cl_7718 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(74,false),(80,false),(86,true),(88,false)]
theorem inp_7718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7718 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7718 (by decide) v hb
def cl_7719 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(74,false),(80,false),(86,true),(88,false)]
theorem inp_7719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7719 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7719 (by decide) v hb
def cl_7720 : CNF.NClause := [(60,false),(29,true),(62,true),(68,true),(74,false),(80,false),(86,true),(88,false)]
theorem inp_7720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7720 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7720 (by decide) v hb
def cl_7721 : CNF.NClause := [(60,false),(29,false),(62,false),(68,false),(74,true),(80,false),(86,true),(88,false)]
theorem inp_7721 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7721 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7721 (by decide) v hb
def cl_7722 : CNF.NClause := [(60,false),(29,true),(62,false),(68,false),(74,true),(80,false),(86,true),(88,false)]
theorem inp_7722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7722 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7722 (by decide) v hb
def cl_7723 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,true),(80,false),(86,true),(88,false)]
theorem inp_7723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7723 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7723 (by decide) v hb
def cl_7724 : CNF.NClause := [(60,false),(29,true),(62,true),(68,false),(74,true),(80,false),(86,true),(88,false)]
theorem inp_7724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7724 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7724 (by decide) v hb
def cl_7725 : CNF.NClause := [(60,false),(29,false),(62,false),(68,true),(74,true),(80,false),(86,true),(88,false)]
theorem inp_7725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7725 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7725 (by decide) v hb
def cl_7726 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(74,true),(80,false),(86,true),(88,false)]
theorem inp_7726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7726 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7726 (by decide) v hb
def cl_7727 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(74,true),(80,false),(86,true),(88,false)]
theorem inp_7727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7727 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7727 (by decide) v hb
def cl_7728 : CNF.NClause := [(60,false),(29,true),(62,true),(68,true),(74,true),(80,false),(86,true),(88,false)]
theorem inp_7728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7728 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7728 (by decide) v hb
def cl_7729 : CNF.NClause := [(60,false),(29,false),(62,false),(68,false),(74,false),(80,true),(86,true),(88,false)]
theorem inp_7729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7729 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7729 (by decide) v hb
def cl_7730 : CNF.NClause := [(60,false),(29,true),(62,false),(68,false),(74,false),(80,true),(86,true),(88,false)]
theorem inp_7730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7730 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7730 (by decide) v hb
def cl_7731 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,false),(80,true),(86,true),(88,false)]
theorem inp_7731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7731 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7731 (by decide) v hb
def cl_7732 : CNF.NClause := [(60,false),(29,true),(62,true),(68,false),(74,false),(80,true),(86,true),(88,false)]
theorem inp_7732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7732 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7732 (by decide) v hb
def cl_7733 : CNF.NClause := [(60,false),(29,false),(62,false),(68,true),(74,false),(80,true),(86,true),(88,false)]
theorem inp_7733 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7733 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7733 (by decide) v hb
def cl_7734 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(74,false),(80,true),(86,true),(88,false)]
theorem inp_7734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7734 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7734 (by decide) v hb
def cl_7735 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(74,false),(80,true),(86,true),(88,false)]
theorem inp_7735 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7735 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7735 (by decide) v hb
def cl_7736 : CNF.NClause := [(60,false),(29,true),(62,true),(68,true),(74,false),(80,true),(86,true),(88,false)]
theorem inp_7736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7736 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7736 (by decide) v hb
def cl_7737 : CNF.NClause := [(60,false),(29,false),(62,false),(68,false),(74,true),(80,true),(86,true),(88,false)]
theorem inp_7737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7737 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7737 (by decide) v hb
def cl_7738 : CNF.NClause := [(60,false),(29,true),(62,false),(68,false),(74,true),(80,true),(86,true),(88,false)]
theorem inp_7738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7738 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7738 (by decide) v hb
def cl_7739 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,true),(80,true),(86,true),(88,false)]
theorem inp_7739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7739 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7739 (by decide) v hb
def cl_7740 : CNF.NClause := [(60,false),(29,true),(62,true),(68,false),(74,true),(80,true),(86,true),(88,false)]
theorem inp_7740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7740 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7740 (by decide) v hb
def cl_7741 : CNF.NClause := [(60,false),(29,false),(62,false),(68,true),(74,true),(80,true),(86,true),(88,false)]
theorem inp_7741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7741 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7741 (by decide) v hb
def cl_7742 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(74,true),(80,true),(86,true),(88,false)]
theorem inp_7742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7742 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7742 (by decide) v hb
def cl_7743 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(74,true),(80,true),(86,true),(88,false)]
theorem inp_7743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7743 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7743 (by decide) v hb
def cl_7744 : CNF.NClause := [(60,false),(29,true),(62,true),(68,true),(74,true),(80,true),(86,true),(88,false)]
theorem inp_7744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7744 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7744 (by decide) v hb
def cl_7745 : CNF.NClause := [(60,false),(29,false),(62,false),(68,false),(74,false),(80,false),(86,false),(88,true)]
theorem inp_7745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7745 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7745 (by decide) v hb
def cl_7746 : CNF.NClause := [(60,false),(29,true),(62,false),(68,false),(74,false),(80,false),(86,false),(88,true)]
theorem inp_7746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7746 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7746 (by decide) v hb
def cl_7747 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,false),(80,false),(86,false),(88,true)]
theorem inp_7747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7747 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7747 (by decide) v hb
def cl_7748 : CNF.NClause := [(60,false),(29,true),(62,true),(68,false),(74,false),(80,false),(86,false),(88,true)]
theorem inp_7748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7748 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7748 (by decide) v hb
def cl_7749 : CNF.NClause := [(60,false),(29,false),(62,false),(68,true),(74,false),(80,false),(86,false),(88,true)]
theorem inp_7749 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7749 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7749 (by decide) v hb
def cl_7750 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(74,false),(80,false),(86,false),(88,true)]
theorem inp_7750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7750 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7750 (by decide) v hb
end Percolation.NReplay
