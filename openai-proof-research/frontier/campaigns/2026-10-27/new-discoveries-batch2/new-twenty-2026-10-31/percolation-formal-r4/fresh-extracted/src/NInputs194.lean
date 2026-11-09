import NInputs193
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_12686 : CNF.NClause := [(903,true),(906,true),(909,true),(917,false),(920,true),(927,true)]
theorem inp_12686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12686 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 11) (closed_mem 25 11) cl_12686 (by decide) v hb
def cl_12687 : CNF.NClause := [(903,true),(906,true),(909,false),(917,true),(920,true),(927,true)]
theorem inp_12687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12687 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 11) (closed_mem 25 11) cl_12687 (by decide) v hb
def cl_12688 : CNF.NClause := [(903,true),(906,false),(909,true),(917,true),(920,true),(927,true)]
theorem inp_12688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12688 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 11) (closed_mem 25 11) cl_12688 (by decide) v hb
def cl_12689 : CNF.NClause := [(903,false),(906,true),(909,true),(917,true),(920,true),(927,true)]
theorem inp_12689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12689 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 11) (closed_mem 25 11) cl_12689 (by decide) v hb
def cl_12690 : CNF.NClause := [(901,true),(905,true),(909,true),(918,true),(922,true),(928,false)]
theorem inp_12690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12690 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 12) (closed_mem 25 12) cl_12690 (by decide) v hb
def cl_12691 : CNF.NClause := [(901,true),(905,true),(909,true),(918,true),(922,false),(928,true)]
theorem inp_12691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12691 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 12) (closed_mem 25 12) cl_12691 (by decide) v hb
def cl_12692 : CNF.NClause := [(901,true),(905,true),(909,true),(918,false),(922,true),(928,true)]
theorem inp_12692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12692 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 12) (closed_mem 25 12) cl_12692 (by decide) v hb
def cl_12693 : CNF.NClause := [(901,true),(905,true),(909,false),(918,true),(922,true),(928,true)]
theorem inp_12693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12693 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 12) (closed_mem 25 12) cl_12693 (by decide) v hb
def cl_12694 : CNF.NClause := [(901,true),(905,false),(909,true),(918,true),(922,true),(928,true)]
theorem inp_12694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12694 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 12) (closed_mem 25 12) cl_12694 (by decide) v hb
def cl_12695 : CNF.NClause := [(901,false),(905,true),(909,true),(918,true),(922,true),(928,true)]
theorem inp_12695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12695 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 12) (closed_mem 25 12) cl_12695 (by decide) v hb
def cl_12696 : CNF.NClause := [(902,true),(908,true),(909,true),(915,true),(921,true),(925,false)]
theorem inp_12696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12696 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 13) (closed_mem 25 13) cl_12696 (by decide) v hb
def cl_12697 : CNF.NClause := [(902,true),(908,true),(909,true),(915,true),(921,false),(925,true)]
theorem inp_12697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12697 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 13) (closed_mem 25 13) cl_12697 (by decide) v hb
def cl_12698 : CNF.NClause := [(902,true),(908,true),(909,true),(915,false),(921,true),(925,true)]
theorem inp_12698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12698 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 13) (closed_mem 25 13) cl_12698 (by decide) v hb
def cl_12699 : CNF.NClause := [(902,true),(908,true),(909,false),(915,true),(921,true),(925,true)]
theorem inp_12699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12699 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 13) (closed_mem 25 13) cl_12699 (by decide) v hb
def cl_12700 : CNF.NClause := [(902,true),(908,false),(909,true),(915,true),(921,true),(925,true)]
theorem inp_12700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12700 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 13) (closed_mem 25 13) cl_12700 (by decide) v hb
def cl_12701 : CNF.NClause := [(902,false),(908,true),(909,true),(915,true),(921,true),(925,true)]
theorem inp_12701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12701 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 13) (closed_mem 25 13) cl_12701 (by decide) v hb
def cl_12702 : CNF.NClause := [(900,true),(907,true),(909,true),(916,true),(923,true),(926,false)]
theorem inp_12702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12702 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 14) (closed_mem 25 14) cl_12702 (by decide) v hb
def cl_12703 : CNF.NClause := [(900,true),(907,true),(909,true),(916,true),(923,false),(926,true)]
theorem inp_12703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12703 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 14) (closed_mem 25 14) cl_12703 (by decide) v hb
def cl_12704 : CNF.NClause := [(900,true),(907,true),(909,true),(916,false),(923,true),(926,true)]
theorem inp_12704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12704 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 14) (closed_mem 25 14) cl_12704 (by decide) v hb
def cl_12705 : CNF.NClause := [(900,true),(907,true),(909,false),(916,true),(923,true),(926,true)]
theorem inp_12705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12705 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 14) (closed_mem 25 14) cl_12705 (by decide) v hb
def cl_12706 : CNF.NClause := [(900,true),(907,false),(909,true),(916,true),(923,true),(926,true)]
theorem inp_12706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12706 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 14) (closed_mem 25 14) cl_12706 (by decide) v hb
def cl_12707 : CNF.NClause := [(900,false),(907,true),(909,true),(916,true),(923,true),(926,true)]
theorem inp_12707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12707 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 14) (closed_mem 25 14) cl_12707 (by decide) v hb
def cl_12709 : CNF.NClause := [(914,true),(915,true),(916,true),(917,true),(918,false),(929,true)]
theorem inp_12709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12709 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 15) (closed_mem 25 15) cl_12709 (by decide) v hb
def cl_12710 : CNF.NClause := [(914,true),(915,true),(916,true),(917,false),(918,true),(929,true)]
theorem inp_12710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12710 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 15) (closed_mem 25 15) cl_12710 (by decide) v hb
def cl_12711 : CNF.NClause := [(914,true),(915,true),(916,false),(917,true),(918,true),(929,true)]
theorem inp_12711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12711 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 15) (closed_mem 25 15) cl_12711 (by decide) v hb
def cl_12712 : CNF.NClause := [(914,true),(915,false),(916,true),(917,true),(918,true),(929,true)]
theorem inp_12712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12712 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 15) (closed_mem 25 15) cl_12712 (by decide) v hb
def cl_12713 : CNF.NClause := [(914,false),(915,true),(916,true),(917,true),(918,true),(929,true)]
theorem inp_12713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12713 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 15) (closed_mem 25 15) cl_12713 (by decide) v hb
def cl_12714 : CNF.NClause := [(903,true),(905,true),(912,true),(914,true),(921,true),(926,false)]
theorem inp_12714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12714 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 16) (closed_mem 25 16) cl_12714 (by decide) v hb
def cl_12715 : CNF.NClause := [(903,true),(905,true),(912,true),(914,true),(921,false),(926,true)]
theorem inp_12715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12715 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 16) (closed_mem 25 16) cl_12715 (by decide) v hb
def cl_12716 : CNF.NClause := [(903,true),(905,true),(912,true),(914,false),(921,true),(926,true)]
theorem inp_12716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12716 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 16) (closed_mem 25 16) cl_12716 (by decide) v hb
def cl_12717 : CNF.NClause := [(903,true),(905,true),(912,false),(914,true),(921,true),(926,true)]
theorem inp_12717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12717 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 16) (closed_mem 25 16) cl_12717 (by decide) v hb
def cl_12718 : CNF.NClause := [(903,true),(905,false),(912,true),(914,true),(921,true),(926,true)]
theorem inp_12718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12718 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 16) (closed_mem 25 16) cl_12718 (by decide) v hb
def cl_12719 : CNF.NClause := [(903,false),(905,true),(912,true),(914,true),(921,true),(926,true)]
theorem inp_12719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12719 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 16) (closed_mem 25 16) cl_12719 (by decide) v hb
def cl_12720 : CNF.NClause := [(901,true),(907,true),(913,true),(914,true),(920,true),(925,false)]
theorem inp_12720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12720 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 17) (closed_mem 25 17) cl_12720 (by decide) v hb
def cl_12721 : CNF.NClause := [(901,true),(907,true),(913,true),(914,true),(920,false),(925,true)]
theorem inp_12721 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12721 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 17) (closed_mem 25 17) cl_12721 (by decide) v hb
def cl_12722 : CNF.NClause := [(901,true),(907,true),(913,true),(914,false),(920,true),(925,true)]
theorem inp_12722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12722 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 17) (closed_mem 25 17) cl_12722 (by decide) v hb
def cl_12723 : CNF.NClause := [(901,true),(907,true),(913,false),(914,true),(920,true),(925,true)]
theorem inp_12723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12723 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 17) (closed_mem 25 17) cl_12723 (by decide) v hb
def cl_12724 : CNF.NClause := [(901,true),(907,false),(913,true),(914,true),(920,true),(925,true)]
theorem inp_12724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12724 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 17) (closed_mem 25 17) cl_12724 (by decide) v hb
def cl_12725 : CNF.NClause := [(901,false),(907,true),(913,true),(914,true),(920,true),(925,true)]
theorem inp_12725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12725 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 17) (closed_mem 25 17) cl_12725 (by decide) v hb
def cl_12726 : CNF.NClause := [(902,true),(906,true),(910,true),(914,true),(923,true),(928,false)]
theorem inp_12726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12726 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 18) (closed_mem 25 18) cl_12726 (by decide) v hb
def cl_12727 : CNF.NClause := [(902,true),(906,true),(910,true),(914,true),(923,false),(928,true)]
theorem inp_12727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12727 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 18) (closed_mem 25 18) cl_12727 (by decide) v hb
def cl_12728 : CNF.NClause := [(902,true),(906,true),(910,true),(914,false),(923,true),(928,true)]
theorem inp_12728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12728 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 18) (closed_mem 25 18) cl_12728 (by decide) v hb
def cl_12729 : CNF.NClause := [(902,true),(906,true),(910,false),(914,true),(923,true),(928,true)]
theorem inp_12729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12729 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 18) (closed_mem 25 18) cl_12729 (by decide) v hb
def cl_12730 : CNF.NClause := [(902,true),(906,false),(910,true),(914,true),(923,true),(928,true)]
theorem inp_12730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12730 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 18) (closed_mem 25 18) cl_12730 (by decide) v hb
def cl_12731 : CNF.NClause := [(902,false),(906,true),(910,true),(914,true),(923,true),(928,true)]
theorem inp_12731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12731 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 18) (closed_mem 25 18) cl_12731 (by decide) v hb
def cl_12732 : CNF.NClause := [(900,true),(908,true),(911,true),(914,true),(922,true),(927,false)]
theorem inp_12732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12732 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 19) (closed_mem 25 19) cl_12732 (by decide) v hb
def cl_12733 : CNF.NClause := [(900,true),(908,true),(911,true),(914,true),(922,false),(927,true)]
theorem inp_12733 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12733 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 19) (closed_mem 25 19) cl_12733 (by decide) v hb
def cl_12734 : CNF.NClause := [(900,true),(908,true),(911,true),(914,false),(922,true),(927,true)]
theorem inp_12734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12734 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 19) (closed_mem 25 19) cl_12734 (by decide) v hb
def cl_12735 : CNF.NClause := [(900,true),(908,true),(911,false),(914,true),(922,true),(927,true)]
theorem inp_12735 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12735 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 19) (closed_mem 25 19) cl_12735 (by decide) v hb
def cl_12736 : CNF.NClause := [(900,true),(908,false),(911,true),(914,true),(922,true),(927,true)]
theorem inp_12736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12736 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 19) (closed_mem 25 19) cl_12736 (by decide) v hb
end Percolation.NReplay
