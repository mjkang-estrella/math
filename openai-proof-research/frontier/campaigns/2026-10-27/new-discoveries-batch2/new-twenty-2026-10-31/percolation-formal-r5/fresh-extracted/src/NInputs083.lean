import NInputs082
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_4890 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,true),(80,true),(82,false),(89,false)]
theorem inp_4890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4890 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4890 (by decide) v hb
def cl_4891 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,true),(80,true),(82,false),(89,false)]
theorem inp_4891 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4891 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4891 (by decide) v hb
def cl_4892 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,true),(80,true),(82,false),(89,false)]
theorem inp_4892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4892 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4892 (by decide) v hb
def cl_4893 : CNF.NClause := [(38,false),(7,false),(64,false),(71,true),(73,true),(80,true),(82,false),(89,false)]
theorem inp_4893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4893 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4893 (by decide) v hb
def cl_4894 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,true),(80,true),(82,false),(89,false)]
theorem inp_4894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4894 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4894 (by decide) v hb
def cl_4895 : CNF.NClause := [(38,false),(7,false),(64,true),(71,true),(73,true),(80,true),(82,false),(89,false)]
theorem inp_4895 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4895 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4895 (by decide) v hb
def cl_4896 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,true),(80,true),(82,false),(89,false)]
theorem inp_4896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4896 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4896 (by decide) v hb
def cl_4897 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,false),(80,false),(82,true),(89,false)]
theorem inp_4897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4897 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4897 (by decide) v hb
def cl_4898 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,false),(80,false),(82,true),(89,false)]
theorem inp_4898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4898 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4898 v hb
def cl_4899 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,false),(80,false),(82,true),(89,false)]
theorem inp_4899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4899 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4899 (by decide) v hb
def cl_4900 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,false),(80,false),(82,true),(89,false)]
theorem inp_4900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4900 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4900 (by decide) v hb
def cl_4901 : CNF.NClause := [(38,false),(7,false),(64,false),(71,true),(73,false),(80,false),(82,true),(89,false)]
theorem inp_4901 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4901 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4901 (by decide) v hb
def cl_4902 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,false),(80,false),(82,true),(89,false)]
theorem inp_4902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4902 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4902 v hb
def cl_4903 : CNF.NClause := [(38,false),(7,false),(64,true),(71,true),(73,false),(80,false),(82,true),(89,false)]
theorem inp_4903 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4903 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4903 (by decide) v hb
def cl_4904 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,false),(80,false),(82,true),(89,false)]
theorem inp_4904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4904 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4904 (by decide) v hb
def cl_4905 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,true),(80,false),(82,true),(89,false)]
theorem inp_4905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4905 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4905 (by decide) v hb
def cl_4906 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,true),(80,false),(82,true),(89,false)]
theorem inp_4906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4906 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4906 v hb
def cl_4907 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,true),(80,false),(82,true),(89,false)]
theorem inp_4907 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4907 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4907 (by decide) v hb
def cl_4908 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,true),(80,false),(82,true),(89,false)]
theorem inp_4908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4908 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4908 (by decide) v hb
def cl_4909 : CNF.NClause := [(38,false),(7,false),(64,false),(71,true),(73,true),(80,false),(82,true),(89,false)]
theorem inp_4909 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4909 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4909 (by decide) v hb
def cl_4910 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,true),(80,false),(82,true),(89,false)]
theorem inp_4910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4910 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4910 (by decide) v hb
def cl_4911 : CNF.NClause := [(38,false),(7,false),(64,true),(71,true),(73,true),(80,false),(82,true),(89,false)]
theorem inp_4911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4911 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4911 (by decide) v hb
def cl_4912 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,true),(80,false),(82,true),(89,false)]
theorem inp_4912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4912 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4912 (by decide) v hb
def cl_4913 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,false),(80,true),(82,true),(89,false)]
theorem inp_4913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4913 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4913 (by decide) v hb
def cl_4914 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,false),(80,true),(82,true),(89,false)]
theorem inp_4914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4914 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4914 v hb
def cl_4915 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,false),(80,true),(82,true),(89,false)]
theorem inp_4915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4915 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4915 (by decide) v hb
def cl_4916 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,false),(80,true),(82,true),(89,false)]
theorem inp_4916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4916 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4916 (by decide) v hb
def cl_4917 : CNF.NClause := [(38,false),(7,false),(64,false),(71,true),(73,false),(80,true),(82,true),(89,false)]
theorem inp_4917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4917 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4917 (by decide) v hb
def cl_4918 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,false),(80,true),(82,true),(89,false)]
theorem inp_4918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4918 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4918 (by decide) v hb
def cl_4919 : CNF.NClause := [(38,false),(7,false),(64,true),(71,true),(73,false),(80,true),(82,true),(89,false)]
theorem inp_4919 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4919 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4919 (by decide) v hb
def cl_4920 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,false),(80,true),(82,true),(89,false)]
theorem inp_4920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4920 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4920 (by decide) v hb
def cl_4921 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,true),(80,true),(82,true),(89,false)]
theorem inp_4921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4921 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4921 (by decide) v hb
def cl_4922 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,true),(80,true),(82,true),(89,false)]
theorem inp_4922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4922 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_4922 v hb
def cl_4923 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,true),(80,true),(82,true),(89,false)]
theorem inp_4923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4923 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4923 (by decide) v hb
def cl_4924 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,true),(80,true),(82,true),(89,false)]
theorem inp_4924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4924 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4924 (by decide) v hb
def cl_4925 : CNF.NClause := [(38,false),(7,false),(64,false),(71,true),(73,true),(80,true),(82,true),(89,false)]
theorem inp_4925 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4925 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4925 (by decide) v hb
def cl_4926 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,true),(80,true),(82,true),(89,false)]
theorem inp_4926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4926 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4926 (by decide) v hb
def cl_4927 : CNF.NClause := [(38,false),(7,false),(64,true),(71,true),(73,true),(80,true),(82,true),(89,false)]
theorem inp_4927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4927 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4927 (by decide) v hb
def cl_4928 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,true),(80,true),(82,true),(89,false)]
theorem inp_4928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4928 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4928 (by decide) v hb
def cl_4929 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,false),(80,false),(82,false),(89,true)]
theorem inp_4929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4929 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4929 (by decide) v hb
def cl_4930 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,false),(80,false),(82,false),(89,true)]
theorem inp_4930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4930 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4930 (by decide) v hb
def cl_4931 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,false),(80,false),(82,false),(89,true)]
theorem inp_4931 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4931 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4931 (by decide) v hb
def cl_4932 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,false),(80,false),(82,false),(89,true)]
theorem inp_4932 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4932 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4932 (by decide) v hb
def cl_4933 : CNF.NClause := [(38,false),(7,false),(64,false),(71,true),(73,false),(80,false),(82,false),(89,true)]
theorem inp_4933 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4933 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4933 (by decide) v hb
def cl_4934 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,false),(80,false),(82,false),(89,true)]
theorem inp_4934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4934 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4934 (by decide) v hb
def cl_4935 : CNF.NClause := [(38,false),(7,false),(64,true),(71,true),(73,false),(80,false),(82,false),(89,true)]
theorem inp_4935 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4935 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4935 (by decide) v hb
def cl_4936 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,false),(80,false),(82,false),(89,true)]
theorem inp_4936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4936 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4936 (by decide) v hb
def cl_4937 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,true),(80,false),(82,false),(89,true)]
theorem inp_4937 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4937 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4937 (by decide) v hb
def cl_4938 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,true),(80,false),(82,false),(89,true)]
theorem inp_4938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4938 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4938 (by decide) v hb
def cl_4939 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,true),(80,false),(82,false),(89,true)]
theorem inp_4939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_4939 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) cl_4939 (by decide) v hb
end Percolation.NReplay
