import NInputs081
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_4839 : CNF.NClause := [(37,false),(6,false),(66,true),(70,true),(74,false),(78,false),(82,true),(91,true)]
theorem inp_4839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4839 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4839 (by decide) v hb
def cl_4840 : CNF.NClause := [(37,false),(6,true),(66,true),(70,true),(74,false),(78,false),(82,true),(91,true)]
theorem inp_4840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4840 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4840 (by decide) v hb
def cl_4841 : CNF.NClause := [(37,false),(6,false),(66,false),(70,false),(74,true),(78,false),(82,true),(91,true)]
theorem inp_4841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4841 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4841 (by decide) v hb
def cl_4842 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,true),(78,false),(82,true),(91,true)]
theorem inp_4842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4842 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4842 (by decide) v hb
def cl_4843 : CNF.NClause := [(37,false),(6,false),(66,true),(70,false),(74,true),(78,false),(82,true),(91,true)]
theorem inp_4843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4843 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4843 (by decide) v hb
def cl_4844 : CNF.NClause := [(37,false),(6,true),(66,true),(70,false),(74,true),(78,false),(82,true),(91,true)]
theorem inp_4844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4844 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4844 (by decide) v hb
def cl_4845 : CNF.NClause := [(37,false),(6,false),(66,false),(70,true),(74,true),(78,false),(82,true),(91,true)]
theorem inp_4845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4845 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4845 (by decide) v hb
def cl_4846 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,true),(78,false),(82,true),(91,true)]
theorem inp_4846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4846 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4846 (by decide) v hb
def cl_4847 : CNF.NClause := [(37,false),(6,false),(66,true),(70,true),(74,true),(78,false),(82,true),(91,true)]
theorem inp_4847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4847 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4847 (by decide) v hb
def cl_4848 : CNF.NClause := [(37,false),(6,true),(66,true),(70,true),(74,true),(78,false),(82,true),(91,true)]
theorem inp_4848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4848 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4848 (by decide) v hb
def cl_4849 : CNF.NClause := [(37,false),(6,false),(66,false),(70,false),(74,false),(78,true),(82,true),(91,true)]
theorem inp_4849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4849 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4849 (by decide) v hb
def cl_4850 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,false),(78,true),(82,true),(91,true)]
theorem inp_4850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4850 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4850 (by decide) v hb
def cl_4851 : CNF.NClause := [(37,false),(6,false),(66,true),(70,false),(74,false),(78,true),(82,true),(91,true)]
theorem inp_4851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4851 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4851 (by decide) v hb
def cl_4852 : CNF.NClause := [(37,false),(6,true),(66,true),(70,false),(74,false),(78,true),(82,true),(91,true)]
theorem inp_4852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4852 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4852 (by decide) v hb
def cl_4853 : CNF.NClause := [(37,false),(6,false),(66,false),(70,true),(74,false),(78,true),(82,true),(91,true)]
theorem inp_4853 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4853 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4853 (by decide) v hb
def cl_4854 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,false),(78,true),(82,true),(91,true)]
theorem inp_4854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4854 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4854 (by decide) v hb
def cl_4855 : CNF.NClause := [(37,false),(6,false),(66,true),(70,true),(74,false),(78,true),(82,true),(91,true)]
theorem inp_4855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4855 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4855 (by decide) v hb
def cl_4856 : CNF.NClause := [(37,false),(6,true),(66,true),(70,true),(74,false),(78,true),(82,true),(91,true)]
theorem inp_4856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4856 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4856 (by decide) v hb
def cl_4857 : CNF.NClause := [(37,false),(6,false),(66,false),(70,false),(74,true),(78,true),(82,true),(91,true)]
theorem inp_4857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4857 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4857 (by decide) v hb
def cl_4858 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,true),(78,true),(82,true),(91,true)]
theorem inp_4858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4858 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4858 (by decide) v hb
def cl_4859 : CNF.NClause := [(37,false),(6,false),(66,true),(70,false),(74,true),(78,true),(82,true),(91,true)]
theorem inp_4859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4859 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4859 (by decide) v hb
def cl_4860 : CNF.NClause := [(37,false),(6,true),(66,true),(70,false),(74,true),(78,true),(82,true),(91,true)]
theorem inp_4860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4860 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4860 (by decide) v hb
def cl_4861 : CNF.NClause := [(37,false),(6,false),(66,false),(70,true),(74,true),(78,true),(82,true),(91,true)]
theorem inp_4861 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4861 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4861 (by decide) v hb
def cl_4862 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,true),(78,true),(82,true),(91,true)]
theorem inp_4862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4862 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4862 (by decide) v hb
def cl_4864 : CNF.NClause := [(37,false),(6,true),(66,true),(70,true),(74,true),(78,true),(82,true),(91,true)]
theorem inp_4864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4864 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) cl_4864 (by decide) v hb
def cl_4865 : CNF.NClause := [(38,true),(7,false),(64,false),(71,false),(73,false),(80,false),(82,false),(89,false)]
theorem inp_4865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4865 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4865 (by decide) v hb
def cl_4866 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,false),(80,false),(82,false),(89,false)]
theorem inp_4866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4866 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4866 (by decide) v hb
def cl_4867 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,false),(80,false),(82,false),(89,false)]
theorem inp_4867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4867 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4867 (by decide) v hb
def cl_4868 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,false),(80,false),(82,false),(89,false)]
theorem inp_4868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4868 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4868 (by decide) v hb
def cl_4869 : CNF.NClause := [(38,false),(7,false),(64,false),(71,true),(73,false),(80,false),(82,false),(89,false)]
theorem inp_4869 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4869 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4869 (by decide) v hb
def cl_4870 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,false),(80,false),(82,false),(89,false)]
theorem inp_4870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4870 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4870 (by decide) v hb
def cl_4871 : CNF.NClause := [(38,false),(7,false),(64,true),(71,true),(73,false),(80,false),(82,false),(89,false)]
theorem inp_4871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4871 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4871 (by decide) v hb
def cl_4872 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,false),(80,false),(82,false),(89,false)]
theorem inp_4872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4872 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4872 (by decide) v hb
def cl_4873 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,true),(80,false),(82,false),(89,false)]
theorem inp_4873 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4873 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4873 (by decide) v hb
def cl_4874 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,true),(80,false),(82,false),(89,false)]
theorem inp_4874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4874 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4874 (by decide) v hb
def cl_4875 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,true),(80,false),(82,false),(89,false)]
theorem inp_4875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4875 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4875 (by decide) v hb
def cl_4876 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,true),(80,false),(82,false),(89,false)]
theorem inp_4876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4876 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4876 (by decide) v hb
def cl_4877 : CNF.NClause := [(38,false),(7,false),(64,false),(71,true),(73,true),(80,false),(82,false),(89,false)]
theorem inp_4877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4877 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4877 (by decide) v hb
def cl_4878 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,true),(80,false),(82,false),(89,false)]
theorem inp_4878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4878 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4878 (by decide) v hb
def cl_4879 : CNF.NClause := [(38,false),(7,false),(64,true),(71,true),(73,true),(80,false),(82,false),(89,false)]
theorem inp_4879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4879 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4879 (by decide) v hb
def cl_4880 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,true),(80,false),(82,false),(89,false)]
theorem inp_4880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4880 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4880 (by decide) v hb
def cl_4881 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,false),(80,true),(82,false),(89,false)]
theorem inp_4881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4881 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4881 (by decide) v hb
def cl_4882 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,false),(80,true),(82,false),(89,false)]
theorem inp_4882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4882 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4882 (by decide) v hb
def cl_4883 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,false),(80,true),(82,false),(89,false)]
theorem inp_4883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4883 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4883 (by decide) v hb
def cl_4884 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,false),(80,true),(82,false),(89,false)]
theorem inp_4884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4884 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4884 (by decide) v hb
def cl_4885 : CNF.NClause := [(38,false),(7,false),(64,false),(71,true),(73,false),(80,true),(82,false),(89,false)]
theorem inp_4885 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4885 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4885 (by decide) v hb
def cl_4886 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,false),(80,true),(82,false),(89,false)]
theorem inp_4886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4886 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4886 (by decide) v hb
def cl_4887 : CNF.NClause := [(38,false),(7,false),(64,true),(71,true),(73,false),(80,true),(82,false),(89,false)]
theorem inp_4887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4887 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4887 (by decide) v hb
def cl_4888 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,false),(80,true),(82,false),(89,false)]
theorem inp_4888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4888 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4888 (by decide) v hb
def cl_4889 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,true),(80,true),(82,false),(89,false)]
theorem inp_4889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4889 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4889 (by decide) v hb
end Percolation.NReplay
