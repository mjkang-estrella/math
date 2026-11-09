import NInputs012
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_894 : CNF.NClause := [(75,false),(3,true),(9,false),(10,true),(16,true),(22,true),(26,true)]
theorem inp_894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_894 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_894 (by decide) v hb
def cl_895 : CNF.NClause := [(75,false),(3,false),(9,true),(10,true),(16,true),(22,true),(26,true)]
theorem inp_895 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_895 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_895 (by decide) v hb
def cl_896 : CNF.NClause := [(75,false),(3,true),(9,true),(10,true),(16,true),(22,true),(26,true)]
theorem inp_896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_896 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_896 (by decide) v hb
def cl_897 : CNF.NClause := [(76,true),(1,false),(8,false),(10,false),(17,false),(24,false),(27,false)]
theorem inp_897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_897 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_897 v hb
def cl_898 : CNF.NClause := [(76,true),(1,true),(8,false),(10,false),(17,false),(24,false),(27,false)]
theorem inp_898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_898 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_898 v hb
def cl_899 : CNF.NClause := [(76,true),(1,false),(8,true),(10,false),(17,false),(24,false),(27,false)]
theorem inp_899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_899 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_899 v hb
def cl_900 : CNF.NClause := [(76,true),(1,true),(8,true),(10,false),(17,false),(24,false),(27,false)]
theorem inp_900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_900 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_900 v hb
def cl_901 : CNF.NClause := [(76,true),(1,false),(8,false),(10,true),(17,false),(24,false),(27,false)]
theorem inp_901 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_901 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_901 v hb
def cl_902 : CNF.NClause := [(76,true),(1,true),(8,false),(10,true),(17,false),(24,false),(27,false)]
theorem inp_902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_902 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_902 v hb
def cl_903 : CNF.NClause := [(76,true),(1,false),(8,true),(10,true),(17,false),(24,false),(27,false)]
theorem inp_903 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_903 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_903 v hb
def cl_904 : CNF.NClause := [(76,true),(1,true),(8,true),(10,true),(17,false),(24,false),(27,false)]
theorem inp_904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_904 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_904 v hb
def cl_905 : CNF.NClause := [(76,true),(1,false),(8,false),(10,false),(17,true),(24,false),(27,false)]
theorem inp_905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_905 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_905 v hb
def cl_906 : CNF.NClause := [(76,true),(1,true),(8,false),(10,false),(17,true),(24,false),(27,false)]
theorem inp_906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_906 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_906 (by decide) v hb
def cl_907 : CNF.NClause := [(76,true),(1,false),(8,true),(10,false),(17,true),(24,false),(27,false)]
theorem inp_907 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_907 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_907 v hb
def cl_908 : CNF.NClause := [(76,true),(1,true),(8,true),(10,false),(17,true),(24,false),(27,false)]
theorem inp_908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_908 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_908 v hb
def cl_909 : CNF.NClause := [(76,true),(1,false),(8,false),(10,true),(17,true),(24,false),(27,false)]
theorem inp_909 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_909 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_909 (by decide) v hb
def cl_910 : CNF.NClause := [(76,true),(1,true),(8,false),(10,true),(17,true),(24,false),(27,false)]
theorem inp_910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_910 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_910 (by decide) v hb
def cl_911 : CNF.NClause := [(76,true),(1,false),(8,true),(10,true),(17,true),(24,false),(27,false)]
theorem inp_911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_911 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_911 (by decide) v hb
def cl_912 : CNF.NClause := [(76,true),(1,true),(8,true),(10,true),(17,true),(24,false),(27,false)]
theorem inp_912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_912 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_912 (by decide) v hb
def cl_913 : CNF.NClause := [(76,true),(1,false),(8,false),(10,false),(17,false),(24,true),(27,false)]
theorem inp_913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_913 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_913 (by decide) v hb
def cl_914 : CNF.NClause := [(76,true),(1,true),(8,false),(10,false),(17,false),(24,true),(27,false)]
theorem inp_914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_914 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_914 (by decide) v hb
def cl_915 : CNF.NClause := [(76,true),(1,false),(8,true),(10,false),(17,false),(24,true),(27,false)]
theorem inp_915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_915 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_915 v hb
def cl_916 : CNF.NClause := [(76,true),(1,true),(8,true),(10,false),(17,false),(24,true),(27,false)]
theorem inp_916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_916 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_916 v hb
def cl_917 : CNF.NClause := [(76,true),(1,false),(8,false),(10,true),(17,false),(24,true),(27,false)]
theorem inp_917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_917 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_917 (by decide) v hb
def cl_918 : CNF.NClause := [(76,true),(1,true),(8,false),(10,true),(17,false),(24,true),(27,false)]
theorem inp_918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_918 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_918 (by decide) v hb
def cl_919 : CNF.NClause := [(76,true),(1,false),(8,true),(10,true),(17,false),(24,true),(27,false)]
theorem inp_919 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_919 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_919 (by decide) v hb
def cl_920 : CNF.NClause := [(76,true),(1,true),(8,true),(10,true),(17,false),(24,true),(27,false)]
theorem inp_920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_920 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_920 (by decide) v hb
def cl_921 : CNF.NClause := [(76,true),(1,false),(8,false),(10,false),(17,true),(24,true),(27,false)]
theorem inp_921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_921 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_921 v hb
def cl_922 : CNF.NClause := [(76,true),(1,true),(8,false),(10,false),(17,true),(24,true),(27,false)]
theorem inp_922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_922 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_922 (by decide) v hb
def cl_923 : CNF.NClause := [(76,true),(1,false),(8,true),(10,false),(17,true),(24,true),(27,false)]
theorem inp_923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_923 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_923 v hb
def cl_924 : CNF.NClause := [(76,true),(1,true),(8,true),(10,false),(17,true),(24,true),(27,false)]
theorem inp_924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_924 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_924 v hb
def cl_925 : CNF.NClause := [(76,true),(1,false),(8,false),(10,true),(17,true),(24,true),(27,false)]
theorem inp_925 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_925 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_925 (by decide) v hb
def cl_926 : CNF.NClause := [(76,true),(1,true),(8,false),(10,true),(17,true),(24,true),(27,false)]
theorem inp_926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_926 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_926 (by decide) v hb
def cl_927 : CNF.NClause := [(76,true),(1,false),(8,true),(10,true),(17,true),(24,true),(27,false)]
theorem inp_927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_927 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_927 (by decide) v hb
def cl_928 : CNF.NClause := [(76,false),(1,true),(8,true),(10,true),(17,true),(24,true),(27,false)]
theorem inp_928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_928 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_928 v hb
def cl_929 : CNF.NClause := [(76,true),(1,false),(8,false),(10,false),(17,false),(24,false),(27,true)]
theorem inp_929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_929 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_929 v hb
def cl_930 : CNF.NClause := [(76,true),(1,true),(8,false),(10,false),(17,false),(24,false),(27,true)]
theorem inp_930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_930 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_930 (by decide) v hb
def cl_931 : CNF.NClause := [(76,true),(1,false),(8,true),(10,false),(17,false),(24,false),(27,true)]
theorem inp_931 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_931 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_931 v hb
def cl_932 : CNF.NClause := [(76,true),(1,true),(8,true),(10,false),(17,false),(24,false),(27,true)]
theorem inp_932 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_932 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_932 v hb
def cl_933 : CNF.NClause := [(76,true),(1,false),(8,false),(10,true),(17,false),(24,false),(27,true)]
theorem inp_933 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_933 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_933 (by decide) v hb
def cl_934 : CNF.NClause := [(76,true),(1,true),(8,false),(10,true),(17,false),(24,false),(27,true)]
theorem inp_934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_934 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_934 v hb
def cl_935 : CNF.NClause := [(76,true),(1,false),(8,true),(10,true),(17,false),(24,false),(27,true)]
theorem inp_935 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_935 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_935 v hb
def cl_936 : CNF.NClause := [(76,true),(1,true),(8,true),(10,true),(17,false),(24,false),(27,true)]
theorem inp_936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_936 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_936 v hb
def cl_937 : CNF.NClause := [(76,true),(1,false),(8,false),(10,false),(17,true),(24,false),(27,true)]
theorem inp_937 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_937 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_937 v hb
def cl_938 : CNF.NClause := [(76,true),(1,true),(8,false),(10,false),(17,true),(24,false),(27,true)]
theorem inp_938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_938 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_938 (by decide) v hb
def cl_939 : CNF.NClause := [(76,true),(1,false),(8,true),(10,false),(17,true),(24,false),(27,true)]
theorem inp_939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_939 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_939 v hb
def cl_940 : CNF.NClause := [(76,true),(1,true),(8,true),(10,false),(17,true),(24,false),(27,true)]
theorem inp_940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_940 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_940 v hb
def cl_941 : CNF.NClause := [(76,true),(1,false),(8,false),(10,true),(17,true),(24,false),(27,true)]
theorem inp_941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_941 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_941 v hb
def cl_942 : CNF.NClause := [(76,true),(1,true),(8,false),(10,true),(17,true),(24,false),(27,true)]
theorem inp_942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_942 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_942 v hb
def cl_943 : CNF.NClause := [(76,true),(1,false),(8,true),(10,true),(17,true),(24,false),(27,true)]
theorem inp_943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_943 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_943 (by decide) v hb
end Percolation.NReplay
