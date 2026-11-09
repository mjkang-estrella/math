import NInputs078
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_4684 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,true),(85,false),(86,false),(92,true)]
theorem inp_4684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4684 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4684 (by decide) v hb
def cl_4685 : CNF.NClause := [(36,false),(5,false),(82,false),(83,true),(84,true),(85,false),(86,false),(92,true)]
theorem inp_4685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4685 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4685 (by decide) v hb
def cl_4686 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,true),(85,false),(86,false),(92,true)]
theorem inp_4686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4686 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4686 (by decide) v hb
def cl_4687 : CNF.NClause := [(36,false),(5,false),(82,true),(83,true),(84,true),(85,false),(86,false),(92,true)]
theorem inp_4687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4687 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4687 (by decide) v hb
def cl_4688 : CNF.NClause := [(36,false),(5,true),(82,true),(83,true),(84,true),(85,false),(86,false),(92,true)]
theorem inp_4688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4688 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4688 (by decide) v hb
def cl_4689 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(84,false),(85,true),(86,false),(92,true)]
theorem inp_4689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4689 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4689 (by decide) v hb
def cl_4690 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,false),(85,true),(86,false),(92,true)]
theorem inp_4690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4690 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4690 v hb
def cl_4691 : CNF.NClause := [(36,false),(5,false),(82,true),(83,false),(84,false),(85,true),(86,false),(92,true)]
theorem inp_4691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4691 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4691 (by decide) v hb
def cl_4692 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,false),(85,true),(86,false),(92,true)]
theorem inp_4692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4692 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4692 v hb
def cl_4693 : CNF.NClause := [(36,false),(5,false),(82,false),(83,true),(84,false),(85,true),(86,false),(92,true)]
theorem inp_4693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4693 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4693 (by decide) v hb
def cl_4694 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,false),(85,true),(86,false),(92,true)]
theorem inp_4694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4694 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4694 (by decide) v hb
def cl_4695 : CNF.NClause := [(36,false),(5,false),(82,true),(83,true),(84,false),(85,true),(86,false),(92,true)]
theorem inp_4695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4695 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4695 (by decide) v hb
def cl_4696 : CNF.NClause := [(36,false),(5,true),(82,true),(83,true),(84,false),(85,true),(86,false),(92,true)]
theorem inp_4696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4696 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4696 (by decide) v hb
def cl_4697 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(84,true),(85,true),(86,false),(92,true)]
theorem inp_4697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4697 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4697 (by decide) v hb
def cl_4698 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,true),(85,true),(86,false),(92,true)]
theorem inp_4698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4698 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4698 v hb
def cl_4699 : CNF.NClause := [(36,false),(5,false),(82,true),(83,false),(84,true),(85,true),(86,false),(92,true)]
theorem inp_4699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4699 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4699 (by decide) v hb
def cl_4700 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,true),(85,true),(86,false),(92,true)]
theorem inp_4700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4700 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4700 (by decide) v hb
def cl_4701 : CNF.NClause := [(36,false),(5,false),(82,false),(83,true),(84,true),(85,true),(86,false),(92,true)]
theorem inp_4701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4701 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4701 (by decide) v hb
def cl_4702 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,true),(85,true),(86,false),(92,true)]
theorem inp_4702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4702 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4702 (by decide) v hb
def cl_4703 : CNF.NClause := [(36,false),(5,false),(82,true),(83,true),(84,true),(85,true),(86,false),(92,true)]
theorem inp_4703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4703 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4703 (by decide) v hb
def cl_4704 : CNF.NClause := [(36,false),(5,true),(82,true),(83,true),(84,true),(85,true),(86,false),(92,true)]
theorem inp_4704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4704 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4704 (by decide) v hb
def cl_4705 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(84,false),(85,false),(86,true),(92,true)]
theorem inp_4705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4705 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4705 (by decide) v hb
def cl_4706 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,false),(85,false),(86,true),(92,true)]
theorem inp_4706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4706 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4706 (by decide) v hb
def cl_4707 : CNF.NClause := [(36,false),(5,false),(82,true),(83,false),(84,false),(85,false),(86,true),(92,true)]
theorem inp_4707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4707 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4707 (by decide) v hb
def cl_4708 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,false),(85,false),(86,true),(92,true)]
theorem inp_4708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4708 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4708 (by decide) v hb
def cl_4709 : CNF.NClause := [(36,false),(5,false),(82,false),(83,true),(84,false),(85,false),(86,true),(92,true)]
theorem inp_4709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4709 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4709 (by decide) v hb
def cl_4710 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,false),(85,false),(86,true),(92,true)]
theorem inp_4710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4710 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4710 (by decide) v hb
def cl_4711 : CNF.NClause := [(36,false),(5,false),(82,true),(83,true),(84,false),(85,false),(86,true),(92,true)]
theorem inp_4711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4711 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4711 (by decide) v hb
def cl_4712 : CNF.NClause := [(36,false),(5,true),(82,true),(83,true),(84,false),(85,false),(86,true),(92,true)]
theorem inp_4712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4712 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4712 (by decide) v hb
def cl_4713 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(84,true),(85,false),(86,true),(92,true)]
theorem inp_4713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4713 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4713 (by decide) v hb
def cl_4714 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,true),(85,false),(86,true),(92,true)]
theorem inp_4714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4714 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4714 (by decide) v hb
def cl_4715 : CNF.NClause := [(36,false),(5,false),(82,true),(83,false),(84,true),(85,false),(86,true),(92,true)]
theorem inp_4715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4715 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4715 (by decide) v hb
def cl_4716 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,true),(85,false),(86,true),(92,true)]
theorem inp_4716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4716 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4716 (by decide) v hb
def cl_4717 : CNF.NClause := [(36,false),(5,false),(82,false),(83,true),(84,true),(85,false),(86,true),(92,true)]
theorem inp_4717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4717 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4717 (by decide) v hb
def cl_4718 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,true),(85,false),(86,true),(92,true)]
theorem inp_4718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4718 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4718 (by decide) v hb
def cl_4719 : CNF.NClause := [(36,false),(5,false),(82,true),(83,true),(84,true),(85,false),(86,true),(92,true)]
theorem inp_4719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4719 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4719 (by decide) v hb
def cl_4720 : CNF.NClause := [(36,false),(5,true),(82,true),(83,true),(84,true),(85,false),(86,true),(92,true)]
theorem inp_4720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4720 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4720 (by decide) v hb
def cl_4721 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(84,false),(85,true),(86,true),(92,true)]
theorem inp_4721 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4721 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4721 (by decide) v hb
def cl_4722 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,false),(85,true),(86,true),(92,true)]
theorem inp_4722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4722 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4722 (by decide) v hb
def cl_4723 : CNF.NClause := [(36,false),(5,false),(82,true),(83,false),(84,false),(85,true),(86,true),(92,true)]
theorem inp_4723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4723 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4723 (by decide) v hb
def cl_4724 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,false),(85,true),(86,true),(92,true)]
theorem inp_4724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4724 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4724 (by decide) v hb
def cl_4725 : CNF.NClause := [(36,false),(5,false),(82,false),(83,true),(84,false),(85,true),(86,true),(92,true)]
theorem inp_4725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4725 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4725 (by decide) v hb
def cl_4726 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,false),(85,true),(86,true),(92,true)]
theorem inp_4726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4726 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4726 (by decide) v hb
def cl_4727 : CNF.NClause := [(36,false),(5,false),(82,true),(83,true),(84,false),(85,true),(86,true),(92,true)]
theorem inp_4727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4727 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4727 (by decide) v hb
def cl_4728 : CNF.NClause := [(36,false),(5,true),(82,true),(83,true),(84,false),(85,true),(86,true),(92,true)]
theorem inp_4728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4728 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4728 (by decide) v hb
def cl_4729 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(84,true),(85,true),(86,true),(92,true)]
theorem inp_4729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4729 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4729 (by decide) v hb
def cl_4730 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,true),(85,true),(86,true),(92,true)]
theorem inp_4730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4730 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4730 (by decide) v hb
def cl_4731 : CNF.NClause := [(36,false),(5,false),(82,true),(83,false),(84,true),(85,true),(86,true),(92,true)]
theorem inp_4731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4731 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4731 (by decide) v hb
def cl_4732 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,true),(85,true),(86,true),(92,true)]
theorem inp_4732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4732 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4732 (by decide) v hb
def cl_4734 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,true),(85,true),(86,true),(92,true)]
theorem inp_4734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4734 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) cl_4734 (by decide) v hb
end Percolation.NReplay
