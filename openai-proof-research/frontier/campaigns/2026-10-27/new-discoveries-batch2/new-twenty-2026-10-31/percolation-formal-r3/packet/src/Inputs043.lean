import Inputs042
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_13722 : CNF.NClause := [(1054,true),(1060,true),(1066,true),(1072,true),(1078,true),(1080,false)]
theorem inp_13722 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13722 := by
  exact input_gate (closedGate5 30 29) (closed_mem 30 29) cl_13722 (by decide) v h
def cl_13729 : CNF.NClause := [(1054,true),(1059,true),(1064,true),(1069,true),(1074,false),(1079,true)]
theorem inp_13729 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13729 := by
  exact input_gate (closedGate5 30 30) (closed_mem 30 30) cl_13729 (by decide) v h
def cl_13740 : CNF.NClause := [(5,true),(284,true)]
theorem inp_13740 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13740 := by
  apply holds_decode v cl_13740
  have he : decodeClause cl_13740 = omitClause5 5 := by decide
  rw [he]
  exact input_omit 5 v h
def cl_13742 : CNF.NClause := [(7,true),(348,true)]
theorem inp_13742 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13742 := by
  apply holds_decode v cl_13742
  have he : decodeClause cl_13742 = omitClause5 7 := by decide
  rw [he]
  exact input_omit 7 v h
def cl_13743 : CNF.NClause := [(8,true),(380,true)]
theorem inp_13743 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13743 := by
  apply holds_decode v cl_13743
  have he : decodeClause cl_13743 = omitClause5 8 := by decide
  rw [he]
  exact input_omit 8 v h
def cl_13744 : CNF.NClause := [(9,true),(412,true)]
theorem inp_13744 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13744 := by
  apply holds_decode v cl_13744
  have he : decodeClause cl_13744 = omitClause5 9 := by decide
  rw [he]
  exact input_omit 9 v h
def cl_13745 : CNF.NClause := [(10,true),(444,true)]
theorem inp_13745 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13745 := by
  apply holds_decode v cl_13745
  have he : decodeClause cl_13745 = omitClause5 10 := by decide
  rw [he]
  exact input_omit 10 v h
def cl_13746 : CNF.NClause := [(11,true),(476,true)]
theorem inp_13746 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13746 := by
  apply holds_decode v cl_13746
  have he : decodeClause cl_13746 = omitClause5 11 := by decide
  rw [he]
  exact input_omit 11 v h
def cl_13754 : CNF.NClause := [(19,true),(732,true)]
theorem inp_13754 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13754 := by
  apply holds_decode v cl_13754
  have he : decodeClause cl_13754 = omitClause5 19 := by decide
  rw [he]
  exact input_omit 19 v h
def cl_13756 : CNF.NClause := [(21,true),(796,true)]
theorem inp_13756 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13756 := by
  apply holds_decode v cl_13756
  have he : decodeClause cl_13756 = omitClause5 21 := by decide
  rw [he]
  exact input_omit 21 v h
def cl_13757 : CNF.NClause := [(22,true),(828,true)]
theorem inp_13757 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13757 := by
  apply holds_decode v cl_13757
  have he : decodeClause cl_13757 = omitClause5 22 := by decide
  rw [he]
  exact input_omit 22 v h
def cl_13763 : CNF.NClause := [(28,true),(1020,true)]
theorem inp_13763 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13763 := by
  apply holds_decode v cl_13763
  have he : decodeClause cl_13763 = omitClause5 28 := by decide
  rw [he]
  exact input_omit 28 v h
def cl_13765 : CNF.NClause := [(30,true),(1084,true)]
theorem inp_13765 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13765 := by
  apply holds_decode v cl_13765
  have he : decodeClause cl_13765 = omitClause5 30 := by decide
  rw [he]
  exact input_omit 30 v h
def cl_13826 : CNF.NClause := [(2,true),(0,true),(186,false)]
theorem inp_13826 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13826 := by
  apply holds_decode v cl_13826
  have he : decodeClause cl_13826 = containClause5 2 0 := by decide
  rw [he]
  exact input_contain 2 0 (by decide) v h
def cl_13830 : CNF.NClause := [(2,true),(5,true),(191,false)]
theorem inp_13830 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13830 := by
  apply holds_decode v cl_13830
  have he : decodeClause cl_13830 = containClause5 2 5 := by decide
  rw [he]
  exact input_contain 2 5 (by decide) v h
def cl_13835 : CNF.NClause := [(2,true),(10,true),(196,false)]
theorem inp_13835 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13835 := by
  apply holds_decode v cl_13835
  have he : decodeClause cl_13835 = containClause5 2 10 := by decide
  rw [he]
  exact input_contain 2 10 (by decide) v h
def cl_13840 : CNF.NClause := [(2,true),(15,true),(201,false)]
theorem inp_13840 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13840 := by
  apply holds_decode v cl_13840
  have he : decodeClause cl_13840 = containClause5 2 15 := by decide
  rw [he]
  exact input_contain 2 15 (by decide) v h
def cl_13845 : CNF.NClause := [(2,true),(20,true),(206,false)]
theorem inp_13845 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13845 := by
  apply holds_decode v cl_13845
  have he : decodeClause cl_13845 = containClause5 2 20 := by decide
  rw [he]
  exact input_contain 2 20 (by decide) v h
def cl_13856 : CNF.NClause := [(3,true),(0,true),(217,false)]
theorem inp_13856 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13856 := by
  apply holds_decode v cl_13856
  have he : decodeClause cl_13856 = containClause5 3 0 := by decide
  rw [he]
  exact input_contain 3 0 (by decide) v h
def cl_13857 : CNF.NClause := [(3,true),(1,true),(218,false)]
theorem inp_13857 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13857 := by
  apply holds_decode v cl_13857
  have he : decodeClause cl_13857 = containClause5 3 1 := by decide
  rw [he]
  exact input_contain 3 1 (by decide) v h
def cl_13858 : CNF.NClause := [(3,true),(2,true),(219,false)]
theorem inp_13858 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13858 := by
  apply holds_decode v cl_13858
  have he : decodeClause cl_13858 = containClause5 3 2 := by decide
  rw [he]
  exact input_contain 3 2 (by decide) v h
def cl_13860 : CNF.NClause := [(3,true),(5,true),(222,false)]
theorem inp_13860 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13860 := by
  apply holds_decode v cl_13860
  have he : decodeClause cl_13860 = containClause5 3 5 := by decide
  rw [he]
  exact input_contain 3 5 (by decide) v h
def cl_13864 : CNF.NClause := [(3,true),(9,true),(226,false)]
theorem inp_13864 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13864 := by
  apply holds_decode v cl_13864
  have he : decodeClause cl_13864 = containClause5 3 9 := by decide
  rw [he]
  exact input_contain 3 9 (by decide) v h
def cl_13868 : CNF.NClause := [(3,true),(13,true),(230,false)]
theorem inp_13868 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13868 := by
  apply holds_decode v cl_13868
  have he : decodeClause cl_13868 = containClause5 3 13 := by decide
  rw [he]
  exact input_contain 3 13 (by decide) v h
def cl_13869 : CNF.NClause := [(3,true),(14,true),(231,false)]
theorem inp_13869 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13869 := by
  apply holds_decode v cl_13869
  have he : decodeClause cl_13869 = containClause5 3 14 := by decide
  rw [he]
  exact input_contain 3 14 (by decide) v h
def cl_13871 : CNF.NClause := [(3,true),(16,true),(233,false)]
theorem inp_13871 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13871 := by
  apply holds_decode v cl_13871
  have he : decodeClause cl_13871 = containClause5 3 16 := by decide
  rw [he]
  exact input_contain 3 16 (by decide) v h
def cl_13873 : CNF.NClause := [(3,true),(18,true),(235,false)]
theorem inp_13873 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13873 := by
  apply holds_decode v cl_13873
  have he : decodeClause cl_13873 = containClause5 3 18 := by decide
  rw [he]
  exact input_contain 3 18 (by decide) v h
def cl_13876 : CNF.NClause := [(3,true),(21,true),(238,false)]
theorem inp_13876 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13876 := by
  apply holds_decode v cl_13876
  have he : decodeClause cl_13876 = containClause5 3 21 := by decide
  rw [he]
  exact input_contain 3 21 (by decide) v h
def cl_13877 : CNF.NClause := [(3,true),(22,true),(239,false)]
theorem inp_13877 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13877 := by
  apply holds_decode v cl_13877
  have he : decodeClause cl_13877 = containClause5 3 22 := by decide
  rw [he]
  exact input_contain 3 22 (by decide) v h
def cl_13883 : CNF.NClause := [(3,true),(28,true),(245,false)]
theorem inp_13883 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13883 := by
  apply holds_decode v cl_13883
  have he : decodeClause cl_13883 = containClause5 3 28 := by decide
  rw [he]
  exact input_contain 3 28 (by decide) v h
def cl_13884 : CNF.NClause := [(3,true),(29,true),(246,false)]
theorem inp_13884 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13884 := by
  apply holds_decode v cl_13884
  have he : decodeClause cl_13884 = containClause5 3 29 := by decide
  rw [he]
  exact input_contain 3 29 (by decide) v h
def cl_13916 : CNF.NClause := [(5,true),(0,true),(279,false)]
theorem inp_13916 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13916 := by
  apply holds_decode v cl_13916
  have he : decodeClause cl_13916 = containClause5 5 0 := by decide
  rw [he]
  exact input_contain 5 0 (by decide) v h
def cl_13917 : CNF.NClause := [(5,true),(1,true),(280,false)]
theorem inp_13917 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13917 := by
  apply holds_decode v cl_13917
  have he : decodeClause cl_13917 = containClause5 5 1 := by decide
  rw [he]
  exact input_contain 5 1 (by decide) v h
def cl_13918 : CNF.NClause := [(5,true),(2,true),(281,false)]
theorem inp_13918 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13918 := by
  apply holds_decode v cl_13918
  have he : decodeClause cl_13918 = containClause5 5 2 := by decide
  rw [he]
  exact input_contain 5 2 (by decide) v h
def cl_13919 : CNF.NClause := [(5,true),(3,true),(282,false)]
theorem inp_13919 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13919 := by
  apply holds_decode v cl_13919
  have he : decodeClause cl_13919 = containClause5 5 3 := by decide
  rw [he]
  exact input_contain 5 3 (by decide) v h
def cl_13921 : CNF.NClause := [(5,true),(6,true),(285,false)]
theorem inp_13921 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13921 := by
  apply holds_decode v cl_13921
  have he : decodeClause cl_13921 = containClause5 5 6 := by decide
  rw [he]
  exact input_contain 5 6 (by decide) v h
def cl_13923 : CNF.NClause := [(5,true),(8,true),(287,false)]
theorem inp_13923 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13923 := by
  apply holds_decode v cl_13923
  have he : decodeClause cl_13923 = containClause5 5 8 := by decide
  rw [he]
  exact input_contain 5 8 (by decide) v h
def cl_13924 : CNF.NClause := [(5,true),(9,true),(288,false)]
theorem inp_13924 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13924 := by
  apply holds_decode v cl_13924
  have he : decodeClause cl_13924 = containClause5 5 9 := by decide
  rw [he]
  exact input_contain 5 9 (by decide) v h
def cl_13925 : CNF.NClause := [(5,true),(10,true),(289,false)]
theorem inp_13925 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13925 := by
  apply holds_decode v cl_13925
  have he : decodeClause cl_13925 = containClause5 5 10 := by decide
  rw [he]
  exact input_contain 5 10 (by decide) v h
def cl_13927 : CNF.NClause := [(5,true),(12,true),(291,false)]
theorem inp_13927 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13927 := by
  apply holds_decode v cl_13927
  have he : decodeClause cl_13927 = containClause5 5 12 := by decide
  rw [he]
  exact input_contain 5 12 (by decide) v h
def cl_13928 : CNF.NClause := [(5,true),(13,true),(292,false)]
theorem inp_13928 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13928 := by
  apply holds_decode v cl_13928
  have he : decodeClause cl_13928 = containClause5 5 13 := by decide
  rw [he]
  exact input_contain 5 13 (by decide) v h
def cl_13930 : CNF.NClause := [(5,true),(15,true),(294,false)]
theorem inp_13930 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13930 := by
  apply holds_decode v cl_13930
  have he : decodeClause cl_13930 = containClause5 5 15 := by decide
  rw [he]
  exact input_contain 5 15 (by decide) v h
def cl_13933 : CNF.NClause := [(5,true),(18,true),(297,false)]
theorem inp_13933 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13933 := by
  apply holds_decode v cl_13933
  have he : decodeClause cl_13933 = containClause5 5 18 := by decide
  rw [he]
  exact input_contain 5 18 (by decide) v h
def cl_13934 : CNF.NClause := [(5,true),(19,true),(298,false)]
theorem inp_13934 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13934 := by
  apply holds_decode v cl_13934
  have he : decodeClause cl_13934 = containClause5 5 19 := by decide
  rw [he]
  exact input_contain 5 19 (by decide) v h
def cl_13936 : CNF.NClause := [(5,true),(21,true),(300,false)]
theorem inp_13936 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13936 := by
  apply holds_decode v cl_13936
  have he : decodeClause cl_13936 = containClause5 5 21 := by decide
  rw [he]
  exact input_contain 5 21 (by decide) v h
def cl_13938 : CNF.NClause := [(5,true),(23,true),(302,false)]
theorem inp_13938 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13938 := by
  apply holds_decode v cl_13938
  have he : decodeClause cl_13938 = containClause5 5 23 := by decide
  rw [he]
  exact input_contain 5 23 (by decide) v h
def cl_13939 : CNF.NClause := [(5,true),(24,true),(303,false)]
theorem inp_13939 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13939 := by
  apply holds_decode v cl_13939
  have he : decodeClause cl_13939 = containClause5 5 24 := by decide
  rw [he]
  exact input_contain 5 24 (by decide) v h
def cl_13940 : CNF.NClause := [(5,true),(25,true),(304,false)]
theorem inp_13940 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13940 := by
  apply holds_decode v cl_13940
  have he : decodeClause cl_13940 = containClause5 5 25 := by decide
  rw [he]
  exact input_contain 5 25 (by decide) v h
def cl_13941 : CNF.NClause := [(5,true),(26,true),(305,false)]
theorem inp_13941 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13941 := by
  apply holds_decode v cl_13941
  have he : decodeClause cl_13941 = containClause5 5 26 := by decide
  rw [he]
  exact input_contain 5 26 (by decide) v h
def cl_13942 : CNF.NClause := [(5,true),(27,true),(306,false)]
theorem inp_13942 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13942 := by
  apply holds_decode v cl_13942
  have he : decodeClause cl_13942 = containClause5 5 27 := by decide
  rw [he]
  exact input_contain 5 27 (by decide) v h
end Percolation.Replay
