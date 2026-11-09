import Inputs043
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_13943 : CNF.NClause := [(5,true),(28,true),(307,false)]
theorem inp_13943 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13943 := by
  apply holds_decode v cl_13943
  have he : decodeClause cl_13943 = containClause5 5 28 := by decide
  rw [he]
  exact input_contain 5 28 (by decide) v h
def cl_13944 : CNF.NClause := [(5,true),(29,true),(308,false)]
theorem inp_13944 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13944 := by
  apply holds_decode v cl_13944
  have he : decodeClause cl_13944 = containClause5 5 29 := by decide
  rw [he]
  exact input_contain 5 29 (by decide) v h
def cl_13976 : CNF.NClause := [(7,true),(0,true),(341,false)]
theorem inp_13976 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13976 := by
  apply holds_decode v cl_13976
  have he : decodeClause cl_13976 = containClause5 7 0 := by decide
  rw [he]
  exact input_contain 7 0 (by decide) v h
def cl_13977 : CNF.NClause := [(7,true),(1,true),(342,false)]
theorem inp_13977 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13977 := by
  apply holds_decode v cl_13977
  have he : decodeClause cl_13977 = containClause5 7 1 := by decide
  rw [he]
  exact input_contain 7 1 (by decide) v h
def cl_13979 : CNF.NClause := [(7,true),(3,true),(344,false)]
theorem inp_13979 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13979 := by
  apply holds_decode v cl_13979
  have he : decodeClause cl_13979 = containClause5 7 3 := by decide
  rw [he]
  exact input_contain 7 3 (by decide) v h
def cl_13980 : CNF.NClause := [(7,true),(4,true),(345,false)]
theorem inp_13980 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13980 := by
  apply holds_decode v cl_13980
  have he : decodeClause cl_13980 = containClause5 7 4 := by decide
  rw [he]
  exact input_contain 7 4 (by decide) v h
def cl_13984 : CNF.NClause := [(7,true),(9,true),(350,false)]
theorem inp_13984 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13984 := by
  apply holds_decode v cl_13984
  have he : decodeClause cl_13984 = containClause5 7 9 := by decide
  rw [he]
  exact input_contain 7 9 (by decide) v h
def cl_13988 : CNF.NClause := [(7,true),(13,true),(354,false)]
theorem inp_13988 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13988 := by
  apply holds_decode v cl_13988
  have he : decodeClause cl_13988 = containClause5 7 13 := by decide
  rw [he]
  exact input_contain 7 13 (by decide) v h
def cl_13990 : CNF.NClause := [(7,true),(15,true),(356,false)]
theorem inp_13990 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13990 := by
  apply holds_decode v cl_13990
  have he : decodeClause cl_13990 = containClause5 7 15 := by decide
  rw [he]
  exact input_contain 7 15 (by decide) v h
def cl_13991 : CNF.NClause := [(7,true),(16,true),(357,false)]
theorem inp_13991 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13991 := by
  apply holds_decode v cl_13991
  have he : decodeClause cl_13991 = containClause5 7 16 := by decide
  rw [he]
  exact input_contain 7 16 (by decide) v h
def cl_13994 : CNF.NClause := [(7,true),(19,true),(360,false)]
theorem inp_13994 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13994 := by
  apply holds_decode v cl_13994
  have he : decodeClause cl_13994 = containClause5 7 19 := by decide
  rw [he]
  exact input_contain 7 19 (by decide) v h
def cl_13995 : CNF.NClause := [(7,true),(20,true),(361,false)]
theorem inp_13995 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13995 := by
  apply holds_decode v cl_13995
  have he : decodeClause cl_13995 = containClause5 7 20 := by decide
  rw [he]
  exact input_contain 7 20 (by decide) v h
def cl_13998 : CNF.NClause := [(7,true),(23,true),(364,false)]
theorem inp_13998 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13998 := by
  apply holds_decode v cl_13998
  have he : decodeClause cl_13998 = containClause5 7 23 := by decide
  rw [he]
  exact input_contain 7 23 (by decide) v h
def cl_13999 : CNF.NClause := [(7,true),(24,true),(365,false)]
theorem inp_13999 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13999 := by
  apply holds_decode v cl_13999
  have he : decodeClause cl_13999 = containClause5 7 24 := by decide
  rw [he]
  exact input_contain 7 24 (by decide) v h
def cl_14000 : CNF.NClause := [(7,true),(25,true),(366,false)]
theorem inp_14000 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14000 := by
  apply holds_decode v cl_14000
  have he : decodeClause cl_14000 = containClause5 7 25 := by decide
  rw [he]
  exact input_contain 7 25 (by decide) v h
def cl_14001 : CNF.NClause := [(7,true),(26,true),(367,false)]
theorem inp_14001 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14001 := by
  apply holds_decode v cl_14001
  have he : decodeClause cl_14001 = containClause5 7 26 := by decide
  rw [he]
  exact input_contain 7 26 (by decide) v h
def cl_14002 : CNF.NClause := [(7,true),(27,true),(368,false)]
theorem inp_14002 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14002 := by
  apply holds_decode v cl_14002
  have he : decodeClause cl_14002 = containClause5 7 27 := by decide
  rw [he]
  exact input_contain 7 27 (by decide) v h
def cl_14004 : CNF.NClause := [(7,true),(29,true),(370,false)]
theorem inp_14004 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14004 := by
  apply holds_decode v cl_14004
  have he : decodeClause cl_14004 = containClause5 7 29 := by decide
  rw [he]
  exact input_contain 7 29 (by decide) v h
def cl_14005 : CNF.NClause := [(7,true),(30,true),(371,false)]
theorem inp_14005 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14005 := by
  apply holds_decode v cl_14005
  have he : decodeClause cl_14005 = containClause5 7 30 := by decide
  rw [he]
  exact input_contain 7 30 (by decide) v h
def cl_14006 : CNF.NClause := [(8,true),(0,true),(372,false)]
theorem inp_14006 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14006 := by
  apply holds_decode v cl_14006
  have he : decodeClause cl_14006 = containClause5 8 0 := by decide
  rw [he]
  exact input_contain 8 0 (by decide) v h
def cl_14008 : CNF.NClause := [(8,true),(2,true),(374,false)]
theorem inp_14008 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14008 := by
  apply holds_decode v cl_14008
  have he : decodeClause cl_14008 = containClause5 8 2 := by decide
  rw [he]
  exact input_contain 8 2 (by decide) v h
def cl_14009 : CNF.NClause := [(8,true),(3,true),(375,false)]
theorem inp_14009 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14009 := by
  apply holds_decode v cl_14009
  have he : decodeClause cl_14009 = containClause5 8 3 := by decide
  rw [he]
  exact input_contain 8 3 (by decide) v h
def cl_14010 : CNF.NClause := [(8,true),(4,true),(376,false)]
theorem inp_14010 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14010 := by
  apply holds_decode v cl_14010
  have he : decodeClause cl_14010 = containClause5 8 4 := by decide
  rw [he]
  exact input_contain 8 4 (by decide) v h
def cl_14011 : CNF.NClause := [(8,true),(5,true),(377,false)]
theorem inp_14011 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14011 := by
  apply holds_decode v cl_14011
  have he : decodeClause cl_14011 = containClause5 8 5 := by decide
  rw [he]
  exact input_contain 8 5 (by decide) v h
def cl_14014 : CNF.NClause := [(8,true),(9,true),(381,false)]
theorem inp_14014 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14014 := by
  apply holds_decode v cl_14014
  have he : decodeClause cl_14014 = containClause5 8 9 := by decide
  rw [he]
  exact input_contain 8 9 (by decide) v h
def cl_14018 : CNF.NClause := [(8,true),(13,true),(385,false)]
theorem inp_14018 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14018 := by
  apply holds_decode v cl_14018
  have he : decodeClause cl_14018 = containClause5 8 13 := by decide
  rw [he]
  exact input_contain 8 13 (by decide) v h
def cl_14021 : CNF.NClause := [(8,true),(16,true),(388,false)]
theorem inp_14021 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14021 := by
  apply holds_decode v cl_14021
  have he : decodeClause cl_14021 = containClause5 8 16 := by decide
  rw [he]
  exact input_contain 8 16 (by decide) v h
def cl_14022 : CNF.NClause := [(8,true),(17,true),(389,false)]
theorem inp_14022 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14022 := by
  apply holds_decode v cl_14022
  have he : decodeClause cl_14022 = containClause5 8 17 := by decide
  rw [he]
  exact input_contain 8 17 (by decide) v h
def cl_14025 : CNF.NClause := [(8,true),(20,true),(392,false)]
theorem inp_14025 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14025 := by
  apply holds_decode v cl_14025
  have he : decodeClause cl_14025 = containClause5 8 20 := by decide
  rw [he]
  exact input_contain 8 20 (by decide) v h
def cl_14026 : CNF.NClause := [(8,true),(21,true),(393,false)]
theorem inp_14026 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14026 := by
  apply holds_decode v cl_14026
  have he : decodeClause cl_14026 = containClause5 8 21 := by decide
  rw [he]
  exact input_contain 8 21 (by decide) v h
def cl_14028 : CNF.NClause := [(8,true),(23,true),(395,false)]
theorem inp_14028 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14028 := by
  apply holds_decode v cl_14028
  have he : decodeClause cl_14028 = containClause5 8 23 := by decide
  rw [he]
  exact input_contain 8 23 (by decide) v h
def cl_14029 : CNF.NClause := [(8,true),(24,true),(396,false)]
theorem inp_14029 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14029 := by
  apply holds_decode v cl_14029
  have he : decodeClause cl_14029 = containClause5 8 24 := by decide
  rw [he]
  exact input_contain 8 24 (by decide) v h
def cl_14030 : CNF.NClause := [(8,true),(25,true),(397,false)]
theorem inp_14030 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14030 := by
  apply holds_decode v cl_14030
  have he : decodeClause cl_14030 = containClause5 8 25 := by decide
  rw [he]
  exact input_contain 8 25 (by decide) v h
def cl_14033 : CNF.NClause := [(8,true),(28,true),(400,false)]
theorem inp_14033 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14033 := by
  apply holds_decode v cl_14033
  have he : decodeClause cl_14033 = containClause5 8 28 := by decide
  rw [he]
  exact input_contain 8 28 (by decide) v h
def cl_14034 : CNF.NClause := [(8,true),(29,true),(401,false)]
theorem inp_14034 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14034 := by
  apply holds_decode v cl_14034
  have he : decodeClause cl_14034 = containClause5 8 29 := by decide
  rw [he]
  exact input_contain 8 29 (by decide) v h
def cl_14039 : CNF.NClause := [(9,true),(3,true),(406,false)]
theorem inp_14039 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14039 := by
  apply holds_decode v cl_14039
  have he : decodeClause cl_14039 = containClause5 9 3 := by decide
  rw [he]
  exact input_contain 9 3 (by decide) v h
def cl_14040 : CNF.NClause := [(9,true),(4,true),(407,false)]
theorem inp_14040 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14040 := by
  apply holds_decode v cl_14040
  have he : decodeClause cl_14040 = containClause5 9 4 := by decide
  rw [he]
  exact input_contain 9 4 (by decide) v h
def cl_14044 : CNF.NClause := [(9,true),(8,true),(411,false)]
theorem inp_14044 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14044 := by
  apply holds_decode v cl_14044
  have he : decodeClause cl_14044 = containClause5 9 8 := by decide
  rw [he]
  exact input_contain 9 8 (by decide) v h
def cl_14047 : CNF.NClause := [(9,true),(12,true),(415,false)]
theorem inp_14047 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14047 := by
  apply holds_decode v cl_14047
  have he : decodeClause cl_14047 = containClause5 9 12 := by decide
  rw [he]
  exact input_contain 9 12 (by decide) v h
def cl_14049 : CNF.NClause := [(9,true),(14,true),(417,false)]
theorem inp_14049 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14049 := by
  apply holds_decode v cl_14049
  have he : decodeClause cl_14049 = containClause5 9 14 := by decide
  rw [he]
  exact input_contain 9 14 (by decide) v h
def cl_14050 : CNF.NClause := [(9,true),(15,true),(418,false)]
theorem inp_14050 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14050 := by
  apply holds_decode v cl_14050
  have he : decodeClause cl_14050 = containClause5 9 15 := by decide
  rw [he]
  exact input_contain 9 15 (by decide) v h
def cl_14051 : CNF.NClause := [(9,true),(16,true),(419,false)]
theorem inp_14051 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14051 := by
  apply holds_decode v cl_14051
  have he : decodeClause cl_14051 = containClause5 9 16 := by decide
  rw [he]
  exact input_contain 9 16 (by decide) v h
def cl_14052 : CNF.NClause := [(9,true),(17,true),(420,false)]
theorem inp_14052 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14052 := by
  apply holds_decode v cl_14052
  have he : decodeClause cl_14052 = containClause5 9 17 := by decide
  rw [he]
  exact input_contain 9 17 (by decide) v h
def cl_14055 : CNF.NClause := [(9,true),(20,true),(423,false)]
theorem inp_14055 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14055 := by
  apply holds_decode v cl_14055
  have he : decodeClause cl_14055 = containClause5 9 20 := by decide
  rw [he]
  exact input_contain 9 20 (by decide) v h
def cl_14056 : CNF.NClause := [(9,true),(21,true),(424,false)]
theorem inp_14056 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14056 := by
  apply holds_decode v cl_14056
  have he : decodeClause cl_14056 = containClause5 9 21 := by decide
  rw [he]
  exact input_contain 9 21 (by decide) v h
def cl_14057 : CNF.NClause := [(9,true),(22,true),(425,false)]
theorem inp_14057 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14057 := by
  apply holds_decode v cl_14057
  have he : decodeClause cl_14057 = containClause5 9 22 := by decide
  rw [he]
  exact input_contain 9 22 (by decide) v h
def cl_14058 : CNF.NClause := [(9,true),(23,true),(426,false)]
theorem inp_14058 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14058 := by
  apply holds_decode v cl_14058
  have he : decodeClause cl_14058 = containClause5 9 23 := by decide
  rw [he]
  exact input_contain 9 23 (by decide) v h
def cl_14059 : CNF.NClause := [(9,true),(24,true),(427,false)]
theorem inp_14059 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14059 := by
  apply holds_decode v cl_14059
  have he : decodeClause cl_14059 = containClause5 9 24 := by decide
  rw [he]
  exact input_contain 9 24 (by decide) v h
def cl_14063 : CNF.NClause := [(9,true),(28,true),(431,false)]
theorem inp_14063 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14063 := by
  apply holds_decode v cl_14063
  have he : decodeClause cl_14063 = containClause5 9 28 := by decide
  rw [he]
  exact input_contain 9 28 (by decide) v h
def cl_14064 : CNF.NClause := [(9,true),(29,true),(432,false)]
theorem inp_14064 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14064 := by
  apply holds_decode v cl_14064
  have he : decodeClause cl_14064 = containClause5 9 29 := by decide
  rw [he]
  exact input_contain 9 29 (by decide) v h
end Percolation.Replay
