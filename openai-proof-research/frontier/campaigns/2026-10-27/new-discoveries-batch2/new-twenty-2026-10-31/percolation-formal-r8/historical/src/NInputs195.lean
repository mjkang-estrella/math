import NInputs194
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_12737 : CNF.NClause := [(900,false),(908,true),(911,true),(914,true),(922,true),(927,true)]
theorem inp_12737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12737 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 19) (closed_mem 25 19) cl_12737 (by decide) v hb
def cl_12739 : CNF.NClause := [(904,true),(905,true),(906,true),(907,true),(908,false),(929,true)]
theorem inp_12739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12739 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 20) (closed_mem 25 20) cl_12739 (by decide) v hb
def cl_12740 : CNF.NClause := [(904,true),(905,true),(906,true),(907,false),(908,true),(929,true)]
theorem inp_12740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12740 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 20) (closed_mem 25 20) cl_12740 (by decide) v hb
def cl_12741 : CNF.NClause := [(904,true),(905,true),(906,false),(907,true),(908,true),(929,true)]
theorem inp_12741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12741 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 20) (closed_mem 25 20) cl_12741 (by decide) v hb
def cl_12742 : CNF.NClause := [(904,true),(905,false),(906,true),(907,true),(908,true),(929,true)]
theorem inp_12742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12742 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 20) (closed_mem 25 20) cl_12742 (by decide) v hb
def cl_12743 : CNF.NClause := [(904,false),(905,true),(906,true),(907,true),(908,true),(929,true)]
theorem inp_12743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12743 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 20) (closed_mem 25 20) cl_12743 (by decide) v hb
def cl_12744 : CNF.NClause := [(903,true),(904,true),(910,true),(916,true),(922,true),(925,false)]
theorem inp_12744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12744 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 21) (closed_mem 25 21) cl_12744 (by decide) v hb
def cl_12745 : CNF.NClause := [(903,true),(904,true),(910,true),(916,true),(922,false),(925,true)]
theorem inp_12745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12745 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 21) (closed_mem 25 21) cl_12745 (by decide) v hb
def cl_12746 : CNF.NClause := [(903,true),(904,true),(910,true),(916,false),(922,true),(925,true)]
theorem inp_12746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12746 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 21) (closed_mem 25 21) cl_12746 (by decide) v hb
def cl_12747 : CNF.NClause := [(903,true),(904,true),(910,false),(916,true),(922,true),(925,true)]
theorem inp_12747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12747 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 21) (closed_mem 25 21) cl_12747 (by decide) v hb
def cl_12748 : CNF.NClause := [(903,true),(904,false),(910,true),(916,true),(922,true),(925,true)]
theorem inp_12748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12748 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 21) (closed_mem 25 21) cl_12748 (by decide) v hb
def cl_12749 : CNF.NClause := [(903,false),(904,true),(910,true),(916,true),(922,true),(925,true)]
theorem inp_12749 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12749 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 21) (closed_mem 25 21) cl_12749 (by decide) v hb
def cl_12750 : CNF.NClause := [(901,true),(904,true),(912,true),(915,true),(923,true),(927,false)]
theorem inp_12750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12750 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 22) (closed_mem 25 22) cl_12750 (by decide) v hb
def cl_12751 : CNF.NClause := [(901,true),(904,true),(912,true),(915,true),(923,false),(927,true)]
theorem inp_12751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12751 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 22) (closed_mem 25 22) cl_12751 (by decide) v hb
def cl_12752 : CNF.NClause := [(901,true),(904,true),(912,true),(915,false),(923,true),(927,true)]
theorem inp_12752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12752 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 22) (closed_mem 25 22) cl_12752 (by decide) v hb
def cl_12753 : CNF.NClause := [(901,true),(904,true),(912,false),(915,true),(923,true),(927,true)]
theorem inp_12753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12753 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 22) (closed_mem 25 22) cl_12753 (by decide) v hb
def cl_12754 : CNF.NClause := [(901,true),(904,false),(912,true),(915,true),(923,true),(927,true)]
theorem inp_12754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12754 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 22) (closed_mem 25 22) cl_12754 (by decide) v hb
def cl_12755 : CNF.NClause := [(901,false),(904,true),(912,true),(915,true),(923,true),(927,true)]
theorem inp_12755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12755 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 22) (closed_mem 25 22) cl_12755 (by decide) v hb
def cl_12756 : CNF.NClause := [(902,true),(904,true),(911,true),(918,true),(920,true),(926,false)]
theorem inp_12756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12756 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 23) (closed_mem 25 23) cl_12756 (by decide) v hb
def cl_12757 : CNF.NClause := [(902,true),(904,true),(911,true),(918,true),(920,false),(926,true)]
theorem inp_12757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12757 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 23) (closed_mem 25 23) cl_12757 (by decide) v hb
def cl_12758 : CNF.NClause := [(902,true),(904,true),(911,true),(918,false),(920,true),(926,true)]
theorem inp_12758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12758 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 23) (closed_mem 25 23) cl_12758 (by decide) v hb
def cl_12759 : CNF.NClause := [(902,true),(904,true),(911,false),(918,true),(920,true),(926,true)]
theorem inp_12759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12759 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 23) (closed_mem 25 23) cl_12759 (by decide) v hb
def cl_12760 : CNF.NClause := [(902,true),(904,false),(911,true),(918,true),(920,true),(926,true)]
theorem inp_12760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12760 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 23) (closed_mem 25 23) cl_12760 (by decide) v hb
def cl_12761 : CNF.NClause := [(902,false),(904,true),(911,true),(918,true),(920,true),(926,true)]
theorem inp_12761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12761 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 23) (closed_mem 25 23) cl_12761 (by decide) v hb
def cl_12762 : CNF.NClause := [(900,true),(904,true),(913,true),(917,true),(921,true),(928,false)]
theorem inp_12762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12762 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 24) (closed_mem 25 24) cl_12762 (by decide) v hb
def cl_12763 : CNF.NClause := [(900,true),(904,true),(913,true),(917,true),(921,false),(928,true)]
theorem inp_12763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12763 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 24) (closed_mem 25 24) cl_12763 (by decide) v hb
def cl_12764 : CNF.NClause := [(900,true),(904,true),(913,true),(917,false),(921,true),(928,true)]
theorem inp_12764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12764 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 24) (closed_mem 25 24) cl_12764 (by decide) v hb
def cl_12765 : CNF.NClause := [(900,true),(904,true),(913,false),(917,true),(921,true),(928,true)]
theorem inp_12765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12765 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 24) (closed_mem 25 24) cl_12765 (by decide) v hb
def cl_12766 : CNF.NClause := [(900,true),(904,false),(913,true),(917,true),(921,true),(928,true)]
theorem inp_12766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12766 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 24) (closed_mem 25 24) cl_12766 (by decide) v hb
def cl_12767 : CNF.NClause := [(900,false),(904,true),(913,true),(917,true),(921,true),(928,true)]
theorem inp_12767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12767 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 24) (closed_mem 25 24) cl_12767 (by decide) v hb
def cl_12769 : CNF.NClause := [(899,true),(900,true),(901,true),(902,true),(903,false),(929,true)]
theorem inp_12769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12769 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 25) (closed_mem 25 25) cl_12769 (by decide) v hb
def cl_12770 : CNF.NClause := [(899,true),(900,true),(901,true),(902,false),(903,true),(929,true)]
theorem inp_12770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12770 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 25) (closed_mem 25 25) cl_12770 (by decide) v hb
def cl_12771 : CNF.NClause := [(899,true),(900,true),(901,false),(902,true),(903,true),(929,true)]
theorem inp_12771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12771 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 25) (closed_mem 25 25) cl_12771 (by decide) v hb
def cl_12772 : CNF.NClause := [(899,true),(900,false),(901,true),(902,true),(903,true),(929,true)]
theorem inp_12772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12772 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 25) (closed_mem 25 25) cl_12772 (by decide) v hb
def cl_12774 : CNF.NClause := [(899,true),(908,true),(912,true),(916,true),(920,true),(928,false)]
theorem inp_12774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12774 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 26) (closed_mem 25 26) cl_12774 (by decide) v hb
def cl_12775 : CNF.NClause := [(899,true),(908,true),(912,true),(916,true),(920,false),(928,true)]
theorem inp_12775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12775 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 26) (closed_mem 25 26) cl_12775 (by decide) v hb
def cl_12776 : CNF.NClause := [(899,true),(908,true),(912,true),(916,false),(920,true),(928,true)]
theorem inp_12776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12776 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 26) (closed_mem 25 26) cl_12776 (by decide) v hb
def cl_12777 : CNF.NClause := [(899,true),(908,true),(912,false),(916,true),(920,true),(928,true)]
theorem inp_12777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12777 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 26) (closed_mem 25 26) cl_12777 (by decide) v hb
def cl_12778 : CNF.NClause := [(899,true),(908,false),(912,true),(916,true),(920,true),(928,true)]
theorem inp_12778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12778 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 26) (closed_mem 25 26) cl_12778 (by decide) v hb
def cl_12780 : CNF.NClause := [(899,true),(906,true),(913,true),(915,true),(922,true),(926,false)]
theorem inp_12780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12780 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 27) (closed_mem 25 27) cl_12780 (by decide) v hb
def cl_12781 : CNF.NClause := [(899,true),(906,true),(913,true),(915,true),(922,false),(926,true)]
theorem inp_12781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12781 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 27) (closed_mem 25 27) cl_12781 (by decide) v hb
def cl_12782 : CNF.NClause := [(899,true),(906,true),(913,true),(915,false),(922,true),(926,true)]
theorem inp_12782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12782 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 27) (closed_mem 25 27) cl_12782 (by decide) v hb
def cl_12783 : CNF.NClause := [(899,true),(906,true),(913,false),(915,true),(922,true),(926,true)]
theorem inp_12783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12783 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 27) (closed_mem 25 27) cl_12783 (by decide) v hb
def cl_12784 : CNF.NClause := [(899,true),(906,false),(913,true),(915,true),(922,true),(926,true)]
theorem inp_12784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12784 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 27) (closed_mem 25 27) cl_12784 (by decide) v hb
def cl_12786 : CNF.NClause := [(899,true),(907,true),(910,true),(918,true),(921,true),(927,false)]
theorem inp_12786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12786 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 28) (closed_mem 25 28) cl_12786 (by decide) v hb
def cl_12787 : CNF.NClause := [(899,true),(907,true),(910,true),(918,true),(921,false),(927,true)]
theorem inp_12787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12787 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 28) (closed_mem 25 28) cl_12787 (by decide) v hb
def cl_12788 : CNF.NClause := [(899,true),(907,true),(910,true),(918,false),(921,true),(927,true)]
theorem inp_12788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12788 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 28) (closed_mem 25 28) cl_12788 (by decide) v hb
def cl_12789 : CNF.NClause := [(899,true),(907,true),(910,false),(918,true),(921,true),(927,true)]
theorem inp_12789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12789 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 28) (closed_mem 25 28) cl_12789 (by decide) v hb
def cl_12790 : CNF.NClause := [(899,true),(907,false),(910,true),(918,true),(921,true),(927,true)]
theorem inp_12790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12790 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 28) (closed_mem 25 28) cl_12790 (by decide) v hb
def cl_12792 : CNF.NClause := [(899,true),(905,true),(911,true),(917,true),(923,true),(925,false)]
theorem inp_12792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12792 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 25 29) (closed_mem 25 29) cl_12792 (by decide) v hb
end Percolation.NReplay
