import Inputs009
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_883 : CNF.NClause := [(75,true),(3,false),(9,true),(10,false),(16,false),(22,true),(26,true)]
theorem inp_883 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_883 := by
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_883 (by decide) v h
def cl_887 : CNF.NClause := [(75,true),(3,false),(9,true),(10,true),(16,false),(22,true),(26,true)]
theorem inp_887 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_887 := by
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_887 (by decide) v h
def cl_891 : CNF.NClause := [(75,true),(3,false),(9,true),(10,false),(16,true),(22,true),(26,true)]
theorem inp_891 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_891 := by
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_891 (by decide) v h
def cl_897 : CNF.NClause := [(76,true),(1,false),(8,false),(10,false),(17,false),(24,false),(27,false)]
theorem inp_897 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_897 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_897 (by decide) v h
def cl_898 : CNF.NClause := [(76,true),(1,true),(8,false),(10,false),(17,false),(24,false),(27,false)]
theorem inp_898 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_898 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_898 (by decide) v h
def cl_899 : CNF.NClause := [(76,true),(1,false),(8,true),(10,false),(17,false),(24,false),(27,false)]
theorem inp_899 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_899 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_899 (by decide) v h
def cl_900 : CNF.NClause := [(76,true),(1,true),(8,true),(10,false),(17,false),(24,false),(27,false)]
theorem inp_900 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_900 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_900 (by decide) v h
def cl_901 : CNF.NClause := [(76,true),(1,false),(8,false),(10,true),(17,false),(24,false),(27,false)]
theorem inp_901 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_901 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_901 (by decide) v h
def cl_902 : CNF.NClause := [(76,true),(1,true),(8,false),(10,true),(17,false),(24,false),(27,false)]
theorem inp_902 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_902 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_902 (by decide) v h
def cl_903 : CNF.NClause := [(76,true),(1,false),(8,true),(10,true),(17,false),(24,false),(27,false)]
theorem inp_903 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_903 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_903 (by decide) v h
def cl_904 : CNF.NClause := [(76,true),(1,true),(8,true),(10,true),(17,false),(24,false),(27,false)]
theorem inp_904 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_904 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_904 (by decide) v h
def cl_905 : CNF.NClause := [(76,true),(1,false),(8,false),(10,false),(17,true),(24,false),(27,false)]
theorem inp_905 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_905 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_905 (by decide) v h
def cl_907 : CNF.NClause := [(76,true),(1,false),(8,true),(10,false),(17,true),(24,false),(27,false)]
theorem inp_907 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_907 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_907 (by decide) v h
def cl_908 : CNF.NClause := [(76,true),(1,true),(8,true),(10,false),(17,true),(24,false),(27,false)]
theorem inp_908 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_908 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_908 (by decide) v h
def cl_915 : CNF.NClause := [(76,true),(1,false),(8,true),(10,false),(17,false),(24,true),(27,false)]
theorem inp_915 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_915 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_915 (by decide) v h
def cl_916 : CNF.NClause := [(76,true),(1,true),(8,true),(10,false),(17,false),(24,true),(27,false)]
theorem inp_916 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_916 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_916 (by decide) v h
def cl_921 : CNF.NClause := [(76,true),(1,false),(8,false),(10,false),(17,true),(24,true),(27,false)]
theorem inp_921 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_921 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_921 (by decide) v h
def cl_923 : CNF.NClause := [(76,true),(1,false),(8,true),(10,false),(17,true),(24,true),(27,false)]
theorem inp_923 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_923 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_923 (by decide) v h
def cl_924 : CNF.NClause := [(76,true),(1,true),(8,true),(10,false),(17,true),(24,true),(27,false)]
theorem inp_924 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_924 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_924 (by decide) v h
def cl_928 : CNF.NClause := [(76,false),(1,true),(8,true),(10,true),(17,true),(24,true),(27,false)]
theorem inp_928 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_928 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_928 (by decide) v h
def cl_929 : CNF.NClause := [(76,true),(1,false),(8,false),(10,false),(17,false),(24,false),(27,true)]
theorem inp_929 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_929 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_929 (by decide) v h
def cl_931 : CNF.NClause := [(76,true),(1,false),(8,true),(10,false),(17,false),(24,false),(27,true)]
theorem inp_931 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_931 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_931 (by decide) v h
def cl_932 : CNF.NClause := [(76,true),(1,true),(8,true),(10,false),(17,false),(24,false),(27,true)]
theorem inp_932 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_932 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_932 (by decide) v h
def cl_934 : CNF.NClause := [(76,true),(1,true),(8,false),(10,true),(17,false),(24,false),(27,true)]
theorem inp_934 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_934 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_934 (by decide) v h
def cl_935 : CNF.NClause := [(76,true),(1,false),(8,true),(10,true),(17,false),(24,false),(27,true)]
theorem inp_935 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_935 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_935 (by decide) v h
def cl_936 : CNF.NClause := [(76,true),(1,true),(8,true),(10,true),(17,false),(24,false),(27,true)]
theorem inp_936 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_936 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_936 (by decide) v h
def cl_937 : CNF.NClause := [(76,true),(1,false),(8,false),(10,false),(17,true),(24,false),(27,true)]
theorem inp_937 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_937 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_937 (by decide) v h
def cl_939 : CNF.NClause := [(76,true),(1,false),(8,true),(10,false),(17,true),(24,false),(27,true)]
theorem inp_939 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_939 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_939 (by decide) v h
def cl_940 : CNF.NClause := [(76,true),(1,true),(8,true),(10,false),(17,true),(24,false),(27,true)]
theorem inp_940 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_940 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_940 (by decide) v h
def cl_941 : CNF.NClause := [(76,true),(1,false),(8,false),(10,true),(17,true),(24,false),(27,true)]
theorem inp_941 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_941 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_941 (by decide) v h
def cl_942 : CNF.NClause := [(76,true),(1,true),(8,false),(10,true),(17,true),(24,false),(27,true)]
theorem inp_942 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_942 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_942 (by decide) v h
def cl_944 : CNF.NClause := [(76,false),(1,true),(8,true),(10,true),(17,true),(24,false),(27,true)]
theorem inp_944 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_944 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_944 (by decide) v h
def cl_947 : CNF.NClause := [(76,true),(1,false),(8,true),(10,false),(17,false),(24,true),(27,true)]
theorem inp_947 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_947 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_947 (by decide) v h
def cl_948 : CNF.NClause := [(76,true),(1,true),(8,true),(10,false),(17,false),(24,true),(27,true)]
theorem inp_948 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_948 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_948 (by decide) v h
def cl_951 : CNF.NClause := [(76,true),(1,false),(8,true),(10,true),(17,false),(24,true),(27,true)]
theorem inp_951 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_951 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_951 (by decide) v h
def cl_952 : CNF.NClause := [(76,false),(1,true),(8,true),(10,true),(17,false),(24,true),(27,true)]
theorem inp_952 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_952 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_952 (by decide) v h
def cl_953 : CNF.NClause := [(76,true),(1,false),(8,false),(10,false),(17,true),(24,true),(27,true)]
theorem inp_953 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_953 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_953 (by decide) v h
def cl_955 : CNF.NClause := [(76,true),(1,false),(8,true),(10,false),(17,true),(24,true),(27,true)]
theorem inp_955 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_955 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_955 (by decide) v h
def cl_956 : CNF.NClause := [(76,false),(1,true),(8,true),(10,false),(17,true),(24,true),(27,true)]
theorem inp_956 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_956 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_956 (by decide) v h
def cl_957 : CNF.NClause := [(76,true),(1,false),(8,false),(10,true),(17,true),(24,true),(27,true)]
theorem inp_957 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_957 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_957 (by decide) v h
def cl_958 : CNF.NClause := [(76,false),(1,true),(8,false),(10,true),(17,true),(24,true),(27,true)]
theorem inp_958 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_958 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_958 (by decide) v h
def cl_959 : CNF.NClause := [(76,false),(1,false),(8,true),(10,true),(17,true),(24,true),(27,true)]
theorem inp_959 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_959 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_959 (by decide) v h
def cl_960 : CNF.NClause := [(76,false),(1,true),(8,true),(10,true),(17,true),(24,true),(27,true)]
theorem inp_960 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_960 := by
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) cl_960 (by decide) v h
def cl_961 : CNF.NClause := [(77,true),(15,false),(16,false),(17,false),(18,false),(19,false),(30,false)]
theorem inp_961 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_961 := by
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_961 (by decide) v h
def cl_965 : CNF.NClause := [(77,true),(15,false),(16,false),(17,true),(18,false),(19,false),(30,false)]
theorem inp_965 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_965 := by
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_965 (by decide) v h
def cl_973 : CNF.NClause := [(77,true),(15,false),(16,false),(17,true),(18,true),(19,false),(30,false)]
theorem inp_973 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_973 := by
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_973 (by decide) v h
def cl_977 : CNF.NClause := [(77,true),(15,false),(16,false),(17,false),(18,false),(19,true),(30,false)]
theorem inp_977 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_977 := by
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_977 (by decide) v h
def cl_981 : CNF.NClause := [(77,true),(15,false),(16,false),(17,true),(18,false),(19,true),(30,false)]
theorem inp_981 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_981 := by
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_981 (by decide) v h
def cl_989 : CNF.NClause := [(77,true),(15,false),(16,false),(17,true),(18,true),(19,true),(30,false)]
theorem inp_989 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_989 := by
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_989 (by decide) v h
def cl_992 : CNF.NClause := [(77,false),(15,true),(16,true),(17,true),(18,true),(19,true),(30,false)]
theorem inp_992 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_992 := by
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) cl_992 (by decide) v h
end Percolation.Replay
