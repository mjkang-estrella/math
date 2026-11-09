import NInputs210
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_13955 : CNF.NClause := [(6,true),(10,true),(320,false)]
theorem inp_13955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13955 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13955 = (containClause5 6 10) := by decide
  rw [he]
  exact input_contain 6 10 (by decide) v hb
def cl_13956 : CNF.NClause := [(6,true),(11,true),(321,false)]
theorem inp_13956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13956 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13956 = (containClause5 6 11) := by decide
  rw [he]
  exact input_contain 6 11 (by decide) v hb
def cl_13957 : CNF.NClause := [(6,true),(12,true),(322,false)]
theorem inp_13957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13957 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13957 = (containClause5 6 12) := by decide
  rw [he]
  exact input_contain 6 12 (by decide) v hb
def cl_13958 : CNF.NClause := [(6,true),(13,true),(323,false)]
theorem inp_13958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13958 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13958 = (containClause5 6 13) := by decide
  rw [he]
  exact input_contain 6 13 (by decide) v hb
def cl_13959 : CNF.NClause := [(6,true),(14,true),(324,false)]
theorem inp_13959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13959 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13959 = (containClause5 6 14) := by decide
  rw [he]
  exact input_contain 6 14 (by decide) v hb
def cl_13960 : CNF.NClause := [(6,true),(15,true),(325,false)]
theorem inp_13960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13960 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13960 = (containClause5 6 15) := by decide
  rw [he]
  exact input_contain 6 15 (by decide) v hb
def cl_13961 : CNF.NClause := [(6,true),(16,true),(326,false)]
theorem inp_13961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13961 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13961 = (containClause5 6 16) := by decide
  rw [he]
  exact input_contain 6 16 (by decide) v hb
def cl_13962 : CNF.NClause := [(6,true),(17,true),(327,false)]
theorem inp_13962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13962 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13962 = (containClause5 6 17) := by decide
  rw [he]
  exact input_contain 6 17 (by decide) v hb
def cl_13963 : CNF.NClause := [(6,true),(18,true),(328,false)]
theorem inp_13963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13963 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13963 = (containClause5 6 18) := by decide
  rw [he]
  exact input_contain 6 18 (by decide) v hb
def cl_13964 : CNF.NClause := [(6,true),(19,true),(329,false)]
theorem inp_13964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13964 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13964 = (containClause5 6 19) := by decide
  rw [he]
  exact input_contain 6 19 (by decide) v hb
def cl_13965 : CNF.NClause := [(6,true),(20,true),(330,false)]
theorem inp_13965 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13965 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13965 = (containClause5 6 20) := by decide
  rw [he]
  exact input_contain 6 20 (by decide) v hb
def cl_13966 : CNF.NClause := [(6,true),(21,true),(331,false)]
theorem inp_13966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13966 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13966 = (containClause5 6 21) := by decide
  rw [he]
  exact input_contain 6 21 (by decide) v hb
def cl_13967 : CNF.NClause := [(6,true),(22,true),(332,false)]
theorem inp_13967 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13967 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13967 = (containClause5 6 22) := by decide
  rw [he]
  exact input_contain 6 22 (by decide) v hb
def cl_13968 : CNF.NClause := [(6,true),(23,true),(333,false)]
theorem inp_13968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13968 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13968 = (containClause5 6 23) := by decide
  rw [he]
  exact input_contain 6 23 (by decide) v hb
def cl_13969 : CNF.NClause := [(6,true),(24,true),(334,false)]
theorem inp_13969 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13969 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13969 = (containClause5 6 24) := by decide
  rw [he]
  exact input_contain 6 24 (by decide) v hb
def cl_13970 : CNF.NClause := [(6,true),(25,true),(335,false)]
theorem inp_13970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13970 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13970 = (containClause5 6 25) := by decide
  rw [he]
  exact input_contain 6 25 (by decide) v hb
def cl_13971 : CNF.NClause := [(6,true),(26,true),(336,false)]
theorem inp_13971 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13971 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13971 = (containClause5 6 26) := by decide
  rw [he]
  exact input_contain 6 26 (by decide) v hb
def cl_13972 : CNF.NClause := [(6,true),(27,true),(337,false)]
theorem inp_13972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13972 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13972 = (containClause5 6 27) := by decide
  rw [he]
  exact input_contain 6 27 (by decide) v hb
def cl_13973 : CNF.NClause := [(6,true),(28,true),(338,false)]
theorem inp_13973 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13973 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13973 = (containClause5 6 28) := by decide
  rw [he]
  exact input_contain 6 28 (by decide) v hb
def cl_13974 : CNF.NClause := [(6,true),(29,true),(339,false)]
theorem inp_13974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13974 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13974 = (containClause5 6 29) := by decide
  rw [he]
  exact input_contain 6 29 (by decide) v hb
def cl_13975 : CNF.NClause := [(6,true),(30,true),(340,false)]
theorem inp_13975 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13975 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13975 = (containClause5 6 30) := by decide
  rw [he]
  exact input_contain 6 30 (by decide) v hb
def cl_13976 : CNF.NClause := [(7,true),(0,true),(341,false)]
theorem inp_13976 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13976 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13976 v hb
def cl_13977 : CNF.NClause := [(7,true),(1,true),(342,false)]
theorem inp_13977 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13977 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13977 v hb
def cl_13978 : CNF.NClause := [(7,true),(2,true),(343,false)]
theorem inp_13978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13978 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13978 = (containClause5 7 2) := by decide
  rw [he]
  exact input_contain 7 2 (by decide) v hb
def cl_13979 : CNF.NClause := [(7,true),(3,true),(344,false)]
theorem inp_13979 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13979 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13979 v hb
def cl_13980 : CNF.NClause := [(7,true),(4,true),(345,false)]
theorem inp_13980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13980 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13980 v hb
def cl_13981 : CNF.NClause := [(7,true),(5,true),(346,false)]
theorem inp_13981 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13981 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13981 = (containClause5 7 5) := by decide
  rw [he]
  exact input_contain 7 5 (by decide) v hb
def cl_13982 : CNF.NClause := [(7,true),(6,true),(347,false)]
theorem inp_13982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13982 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13982 = (containClause5 7 6) := by decide
  rw [he]
  exact input_contain 7 6 (by decide) v hb
def cl_13983 : CNF.NClause := [(7,true),(8,true),(349,false)]
theorem inp_13983 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13983 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13983 = (containClause5 7 8) := by decide
  rw [he]
  exact input_contain 7 8 (by decide) v hb
def cl_13984 : CNF.NClause := [(7,true),(9,true),(350,false)]
theorem inp_13984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13984 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13984 v hb
def cl_13985 : CNF.NClause := [(7,true),(10,true),(351,false)]
theorem inp_13985 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13985 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13985 = (containClause5 7 10) := by decide
  rw [he]
  exact input_contain 7 10 (by decide) v hb
def cl_13986 : CNF.NClause := [(7,true),(11,true),(352,false)]
theorem inp_13986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13986 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13986 = (containClause5 7 11) := by decide
  rw [he]
  exact input_contain 7 11 (by decide) v hb
def cl_13987 : CNF.NClause := [(7,true),(12,true),(353,false)]
theorem inp_13987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13987 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13987 = (containClause5 7 12) := by decide
  rw [he]
  exact input_contain 7 12 (by decide) v hb
def cl_13988 : CNF.NClause := [(7,true),(13,true),(354,false)]
theorem inp_13988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13988 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13988 v hb
def cl_13989 : CNF.NClause := [(7,true),(14,true),(355,false)]
theorem inp_13989 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13989 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13989 = (containClause5 7 14) := by decide
  rw [he]
  exact input_contain 7 14 (by decide) v hb
def cl_13990 : CNF.NClause := [(7,true),(15,true),(356,false)]
theorem inp_13990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13990 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13990 v hb
def cl_13991 : CNF.NClause := [(7,true),(16,true),(357,false)]
theorem inp_13991 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13991 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13991 v hb
def cl_13992 : CNF.NClause := [(7,true),(17,true),(358,false)]
theorem inp_13992 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13992 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13992 = (containClause5 7 17) := by decide
  rw [he]
  exact input_contain 7 17 (by decide) v hb
def cl_13993 : CNF.NClause := [(7,true),(18,true),(359,false)]
theorem inp_13993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13993 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13993 = (containClause5 7 18) := by decide
  rw [he]
  exact input_contain 7 18 (by decide) v hb
def cl_13994 : CNF.NClause := [(7,true),(19,true),(360,false)]
theorem inp_13994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13994 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13994 v hb
def cl_13995 : CNF.NClause := [(7,true),(20,true),(361,false)]
theorem inp_13995 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13995 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13995 v hb
def cl_13996 : CNF.NClause := [(7,true),(21,true),(362,false)]
theorem inp_13996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13996 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13996 = (containClause5 7 21) := by decide
  rw [he]
  exact input_contain 7 21 (by decide) v hb
def cl_13997 : CNF.NClause := [(7,true),(22,true),(363,false)]
theorem inp_13997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13997 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13997 = (containClause5 7 22) := by decide
  rw [he]
  exact input_contain 7 22 (by decide) v hb
def cl_13998 : CNF.NClause := [(7,true),(23,true),(364,false)]
theorem inp_13998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13998 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13998 v hb
def cl_13999 : CNF.NClause := [(7,true),(24,true),(365,false)]
theorem inp_13999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13999 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13999 v hb
def cl_14000 : CNF.NClause := [(7,true),(25,true),(366,false)]
theorem inp_14000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14000 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14000 v hb
def cl_14001 : CNF.NClause := [(7,true),(26,true),(367,false)]
theorem inp_14001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14001 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14001 v hb
def cl_14002 : CNF.NClause := [(7,true),(27,true),(368,false)]
theorem inp_14002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14002 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14002 v hb
def cl_14003 : CNF.NClause := [(7,true),(28,true),(369,false)]
theorem inp_14003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14003 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_14003 = (containClause5 7 28) := by decide
  rw [he]
  exact input_contain 7 28 (by decide) v hb
def cl_14004 : CNF.NClause := [(7,true),(29,true),(370,false)]
theorem inp_14004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14004 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_14004 v hb
end Percolation.NReplay
