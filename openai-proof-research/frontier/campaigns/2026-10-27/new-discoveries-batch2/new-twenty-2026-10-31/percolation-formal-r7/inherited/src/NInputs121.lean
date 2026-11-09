import NInputs120
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_6855 : CNF.NClause := [(53,false),(22,false),(64,true),(67,true),(75,false),(78,false),(86,false),(90,true)]
theorem inp_6855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6855 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6855 (by decide) v hb
def cl_6856 : CNF.NClause := [(53,false),(22,true),(64,true),(67,true),(75,false),(78,false),(86,false),(90,true)]
theorem inp_6856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6856 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6856 (by decide) v hb
def cl_6857 : CNF.NClause := [(53,false),(22,false),(64,false),(67,false),(75,true),(78,false),(86,false),(90,true)]
theorem inp_6857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6857 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6857 (by decide) v hb
def cl_6858 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,true),(78,false),(86,false),(90,true)]
theorem inp_6858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6858 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6858 (by decide) v hb
def cl_6859 : CNF.NClause := [(53,false),(22,false),(64,true),(67,false),(75,true),(78,false),(86,false),(90,true)]
theorem inp_6859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6859 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6859 (by decide) v hb
def cl_6860 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(75,true),(78,false),(86,false),(90,true)]
theorem inp_6860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6860 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6860 (by decide) v hb
def cl_6861 : CNF.NClause := [(53,false),(22,false),(64,false),(67,true),(75,true),(78,false),(86,false),(90,true)]
theorem inp_6861 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6861 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6861 (by decide) v hb
def cl_6862 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,true),(78,false),(86,false),(90,true)]
theorem inp_6862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6862 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6862 (by decide) v hb
def cl_6863 : CNF.NClause := [(53,false),(22,false),(64,true),(67,true),(75,true),(78,false),(86,false),(90,true)]
theorem inp_6863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6863 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6863 (by decide) v hb
def cl_6864 : CNF.NClause := [(53,false),(22,true),(64,true),(67,true),(75,true),(78,false),(86,false),(90,true)]
theorem inp_6864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6864 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6864 (by decide) v hb
def cl_6865 : CNF.NClause := [(53,false),(22,false),(64,false),(67,false),(75,false),(78,true),(86,false),(90,true)]
theorem inp_6865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6865 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6865 (by decide) v hb
def cl_6866 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,false),(78,true),(86,false),(90,true)]
theorem inp_6866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6866 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6866 (by decide) v hb
def cl_6867 : CNF.NClause := [(53,false),(22,false),(64,true),(67,false),(75,false),(78,true),(86,false),(90,true)]
theorem inp_6867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6867 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6867 (by decide) v hb
def cl_6868 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(75,false),(78,true),(86,false),(90,true)]
theorem inp_6868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6868 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6868 (by decide) v hb
def cl_6869 : CNF.NClause := [(53,false),(22,false),(64,false),(67,true),(75,false),(78,true),(86,false),(90,true)]
theorem inp_6869 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6869 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6869 (by decide) v hb
def cl_6870 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,false),(78,true),(86,false),(90,true)]
theorem inp_6870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6870 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6870 (by decide) v hb
def cl_6871 : CNF.NClause := [(53,false),(22,false),(64,true),(67,true),(75,false),(78,true),(86,false),(90,true)]
theorem inp_6871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6871 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6871 (by decide) v hb
def cl_6872 : CNF.NClause := [(53,false),(22,true),(64,true),(67,true),(75,false),(78,true),(86,false),(90,true)]
theorem inp_6872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6872 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6872 (by decide) v hb
def cl_6873 : CNF.NClause := [(53,false),(22,false),(64,false),(67,false),(75,true),(78,true),(86,false),(90,true)]
theorem inp_6873 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6873 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6873 (by decide) v hb
def cl_6874 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,true),(78,true),(86,false),(90,true)]
theorem inp_6874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6874 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6874 (by decide) v hb
def cl_6875 : CNF.NClause := [(53,false),(22,false),(64,true),(67,false),(75,true),(78,true),(86,false),(90,true)]
theorem inp_6875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6875 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6875 (by decide) v hb
def cl_6876 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(75,true),(78,true),(86,false),(90,true)]
theorem inp_6876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6876 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6876 (by decide) v hb
def cl_6877 : CNF.NClause := [(53,false),(22,false),(64,false),(67,true),(75,true),(78,true),(86,false),(90,true)]
theorem inp_6877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6877 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6877 (by decide) v hb
def cl_6878 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,true),(78,true),(86,false),(90,true)]
theorem inp_6878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6878 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6878 (by decide) v hb
def cl_6879 : CNF.NClause := [(53,false),(22,false),(64,true),(67,true),(75,true),(78,true),(86,false),(90,true)]
theorem inp_6879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6879 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6879 (by decide) v hb
def cl_6880 : CNF.NClause := [(53,false),(22,true),(64,true),(67,true),(75,true),(78,true),(86,false),(90,true)]
theorem inp_6880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6880 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6880 (by decide) v hb
def cl_6881 : CNF.NClause := [(53,false),(22,false),(64,false),(67,false),(75,false),(78,false),(86,true),(90,true)]
theorem inp_6881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6881 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6881 (by decide) v hb
def cl_6882 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,false),(78,false),(86,true),(90,true)]
theorem inp_6882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6882 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6882 (by decide) v hb
def cl_6883 : CNF.NClause := [(53,false),(22,false),(64,true),(67,false),(75,false),(78,false),(86,true),(90,true)]
theorem inp_6883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6883 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6883 (by decide) v hb
def cl_6884 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(75,false),(78,false),(86,true),(90,true)]
theorem inp_6884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6884 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6884 (by decide) v hb
def cl_6885 : CNF.NClause := [(53,false),(22,false),(64,false),(67,true),(75,false),(78,false),(86,true),(90,true)]
theorem inp_6885 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6885 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6885 (by decide) v hb
def cl_6886 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,false),(78,false),(86,true),(90,true)]
theorem inp_6886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6886 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6886 (by decide) v hb
def cl_6887 : CNF.NClause := [(53,false),(22,false),(64,true),(67,true),(75,false),(78,false),(86,true),(90,true)]
theorem inp_6887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6887 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6887 (by decide) v hb
def cl_6888 : CNF.NClause := [(53,false),(22,true),(64,true),(67,true),(75,false),(78,false),(86,true),(90,true)]
theorem inp_6888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6888 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6888 (by decide) v hb
def cl_6889 : CNF.NClause := [(53,false),(22,false),(64,false),(67,false),(75,true),(78,false),(86,true),(90,true)]
theorem inp_6889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6889 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6889 (by decide) v hb
def cl_6890 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,true),(78,false),(86,true),(90,true)]
theorem inp_6890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6890 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6890 (by decide) v hb
def cl_6892 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(75,true),(78,false),(86,true),(90,true)]
theorem inp_6892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6892 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6892 (by decide) v hb
def cl_6893 : CNF.NClause := [(53,false),(22,false),(64,false),(67,true),(75,true),(78,false),(86,true),(90,true)]
theorem inp_6893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6893 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6893 (by decide) v hb
def cl_6894 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,true),(78,false),(86,true),(90,true)]
theorem inp_6894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6894 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6894 (by decide) v hb
def cl_6896 : CNF.NClause := [(53,false),(22,true),(64,true),(67,true),(75,true),(78,false),(86,true),(90,true)]
theorem inp_6896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6896 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6896 (by decide) v hb
def cl_6897 : CNF.NClause := [(53,false),(22,false),(64,false),(67,false),(75,false),(78,true),(86,true),(90,true)]
theorem inp_6897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6897 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6897 (by decide) v hb
def cl_6898 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,false),(78,true),(86,true),(90,true)]
theorem inp_6898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6898 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6898 (by decide) v hb
def cl_6899 : CNF.NClause := [(53,false),(22,false),(64,true),(67,false),(75,false),(78,true),(86,true),(90,true)]
theorem inp_6899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6899 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6899 (by decide) v hb
def cl_6900 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(75,false),(78,true),(86,true),(90,true)]
theorem inp_6900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6900 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6900 (by decide) v hb
def cl_6901 : CNF.NClause := [(53,false),(22,false),(64,false),(67,true),(75,false),(78,true),(86,true),(90,true)]
theorem inp_6901 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6901 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6901 (by decide) v hb
def cl_6902 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,false),(78,true),(86,true),(90,true)]
theorem inp_6902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6902 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6902 (by decide) v hb
def cl_6903 : CNF.NClause := [(53,false),(22,false),(64,true),(67,true),(75,false),(78,true),(86,true),(90,true)]
theorem inp_6903 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6903 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6903 (by decide) v hb
def cl_6904 : CNF.NClause := [(53,false),(22,true),(64,true),(67,true),(75,false),(78,true),(86,true),(90,true)]
theorem inp_6904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6904 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6904 (by decide) v hb
def cl_6905 : CNF.NClause := [(53,false),(22,false),(64,false),(67,false),(75,true),(78,true),(86,true),(90,true)]
theorem inp_6905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6905 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6905 (by decide) v hb
def cl_6906 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,true),(78,true),(86,true),(90,true)]
theorem inp_6906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6906 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6906 (by decide) v hb
end Percolation.NReplay
