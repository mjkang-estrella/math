import NInputs208
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_13855 : CNF.NClause := [(2,true),(30,true),(216,false)]
theorem inp_13855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13855 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13855 = (containClause5 2 30) := by decide
  rw [he]
  exact input_contain 2 30 (by decide) v hb
def cl_13856 : CNF.NClause := [(3,true),(0,true),(217,false)]
theorem inp_13856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13856 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13856 v hb
def cl_13857 : CNF.NClause := [(3,true),(1,true),(218,false)]
theorem inp_13857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13857 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13857 v hb
def cl_13858 : CNF.NClause := [(3,true),(2,true),(219,false)]
theorem inp_13858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13858 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13858 v hb
def cl_13859 : CNF.NClause := [(3,true),(4,true),(221,false)]
theorem inp_13859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13859 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13859 = (containClause5 3 4) := by decide
  rw [he]
  exact input_contain 3 4 (by decide) v hb
def cl_13860 : CNF.NClause := [(3,true),(5,true),(222,false)]
theorem inp_13860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13860 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13860 v hb
def cl_13861 : CNF.NClause := [(3,true),(6,true),(223,false)]
theorem inp_13861 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13861 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13861 = (containClause5 3 6) := by decide
  rw [he]
  exact input_contain 3 6 (by decide) v hb
def cl_13862 : CNF.NClause := [(3,true),(7,true),(224,false)]
theorem inp_13862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13862 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13862 = (containClause5 3 7) := by decide
  rw [he]
  exact input_contain 3 7 (by decide) v hb
def cl_13863 : CNF.NClause := [(3,true),(8,true),(225,false)]
theorem inp_13863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13863 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13863 = (containClause5 3 8) := by decide
  rw [he]
  exact input_contain 3 8 (by decide) v hb
def cl_13864 : CNF.NClause := [(3,true),(9,true),(226,false)]
theorem inp_13864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13864 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13864 v hb
def cl_13865 : CNF.NClause := [(3,true),(10,true),(227,false)]
theorem inp_13865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13865 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13865 = (containClause5 3 10) := by decide
  rw [he]
  exact input_contain 3 10 (by decide) v hb
def cl_13866 : CNF.NClause := [(3,true),(11,true),(228,false)]
theorem inp_13866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13866 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13866 = (containClause5 3 11) := by decide
  rw [he]
  exact input_contain 3 11 (by decide) v hb
def cl_13867 : CNF.NClause := [(3,true),(12,true),(229,false)]
theorem inp_13867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13867 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13867 = (containClause5 3 12) := by decide
  rw [he]
  exact input_contain 3 12 (by decide) v hb
def cl_13868 : CNF.NClause := [(3,true),(13,true),(230,false)]
theorem inp_13868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13868 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13868 v hb
def cl_13869 : CNF.NClause := [(3,true),(14,true),(231,false)]
theorem inp_13869 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13869 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13869 v hb
def cl_13870 : CNF.NClause := [(3,true),(15,true),(232,false)]
theorem inp_13870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13870 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13870 = (containClause5 3 15) := by decide
  rw [he]
  exact input_contain 3 15 (by decide) v hb
def cl_13871 : CNF.NClause := [(3,true),(16,true),(233,false)]
theorem inp_13871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13871 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13871 v hb
def cl_13872 : CNF.NClause := [(3,true),(17,true),(234,false)]
theorem inp_13872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13872 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13872 = (containClause5 3 17) := by decide
  rw [he]
  exact input_contain 3 17 (by decide) v hb
def cl_13873 : CNF.NClause := [(3,true),(18,true),(235,false)]
theorem inp_13873 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13873 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13873 v hb
def cl_13874 : CNF.NClause := [(3,true),(19,true),(236,false)]
theorem inp_13874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13874 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13874 = (containClause5 3 19) := by decide
  rw [he]
  exact input_contain 3 19 (by decide) v hb
def cl_13875 : CNF.NClause := [(3,true),(20,true),(237,false)]
theorem inp_13875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13875 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13875 = (containClause5 3 20) := by decide
  rw [he]
  exact input_contain 3 20 (by decide) v hb
def cl_13876 : CNF.NClause := [(3,true),(21,true),(238,false)]
theorem inp_13876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13876 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13876 v hb
def cl_13877 : CNF.NClause := [(3,true),(22,true),(239,false)]
theorem inp_13877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13877 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13877 v hb
def cl_13878 : CNF.NClause := [(3,true),(23,true),(240,false)]
theorem inp_13878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13878 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13878 = (containClause5 3 23) := by decide
  rw [he]
  exact input_contain 3 23 (by decide) v hb
def cl_13879 : CNF.NClause := [(3,true),(24,true),(241,false)]
theorem inp_13879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13879 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13879 = (containClause5 3 24) := by decide
  rw [he]
  exact input_contain 3 24 (by decide) v hb
def cl_13880 : CNF.NClause := [(3,true),(25,true),(242,false)]
theorem inp_13880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13880 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13880 = (containClause5 3 25) := by decide
  rw [he]
  exact input_contain 3 25 (by decide) v hb
def cl_13881 : CNF.NClause := [(3,true),(26,true),(243,false)]
theorem inp_13881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13881 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13881 = (containClause5 3 26) := by decide
  rw [he]
  exact input_contain 3 26 (by decide) v hb
def cl_13882 : CNF.NClause := [(3,true),(27,true),(244,false)]
theorem inp_13882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13882 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13882 = (containClause5 3 27) := by decide
  rw [he]
  exact input_contain 3 27 (by decide) v hb
def cl_13883 : CNF.NClause := [(3,true),(28,true),(245,false)]
theorem inp_13883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13883 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13883 v hb
def cl_13884 : CNF.NClause := [(3,true),(29,true),(246,false)]
theorem inp_13884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13884 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13884 v hb
def cl_13885 : CNF.NClause := [(3,true),(30,true),(247,false)]
theorem inp_13885 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13885 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13885 = (containClause5 3 30) := by decide
  rw [he]
  exact input_contain 3 30 (by decide) v hb
def cl_13886 : CNF.NClause := [(4,true),(0,true),(248,false)]
theorem inp_13886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13886 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13886 = (containClause5 4 0) := by decide
  rw [he]
  exact input_contain 4 0 (by decide) v hb
def cl_13887 : CNF.NClause := [(4,true),(1,true),(249,false)]
theorem inp_13887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13887 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13887 = (containClause5 4 1) := by decide
  rw [he]
  exact input_contain 4 1 (by decide) v hb
def cl_13888 : CNF.NClause := [(4,true),(2,true),(250,false)]
theorem inp_13888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13888 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13888 = (containClause5 4 2) := by decide
  rw [he]
  exact input_contain 4 2 (by decide) v hb
def cl_13889 : CNF.NClause := [(4,true),(3,true),(251,false)]
theorem inp_13889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13889 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13889 = (containClause5 4 3) := by decide
  rw [he]
  exact input_contain 4 3 (by decide) v hb
def cl_13890 : CNF.NClause := [(4,true),(5,true),(253,false)]
theorem inp_13890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13890 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13890 = (containClause5 4 5) := by decide
  rw [he]
  exact input_contain 4 5 (by decide) v hb
def cl_13891 : CNF.NClause := [(4,true),(6,true),(254,false)]
theorem inp_13891 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13891 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13891 = (containClause5 4 6) := by decide
  rw [he]
  exact input_contain 4 6 (by decide) v hb
def cl_13892 : CNF.NClause := [(4,true),(7,true),(255,false)]
theorem inp_13892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13892 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13892 = (containClause5 4 7) := by decide
  rw [he]
  exact input_contain 4 7 (by decide) v hb
def cl_13893 : CNF.NClause := [(4,true),(8,true),(256,false)]
theorem inp_13893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13893 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13893 = (containClause5 4 8) := by decide
  rw [he]
  exact input_contain 4 8 (by decide) v hb
def cl_13894 : CNF.NClause := [(4,true),(9,true),(257,false)]
theorem inp_13894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13894 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13894 = (containClause5 4 9) := by decide
  rw [he]
  exact input_contain 4 9 (by decide) v hb
def cl_13895 : CNF.NClause := [(4,true),(10,true),(258,false)]
theorem inp_13895 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13895 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13895 = (containClause5 4 10) := by decide
  rw [he]
  exact input_contain 4 10 (by decide) v hb
def cl_13896 : CNF.NClause := [(4,true),(11,true),(259,false)]
theorem inp_13896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13896 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13896 = (containClause5 4 11) := by decide
  rw [he]
  exact input_contain 4 11 (by decide) v hb
def cl_13897 : CNF.NClause := [(4,true),(12,true),(260,false)]
theorem inp_13897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13897 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13897 = (containClause5 4 12) := by decide
  rw [he]
  exact input_contain 4 12 (by decide) v hb
def cl_13898 : CNF.NClause := [(4,true),(13,true),(261,false)]
theorem inp_13898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13898 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13898 = (containClause5 4 13) := by decide
  rw [he]
  exact input_contain 4 13 (by decide) v hb
def cl_13899 : CNF.NClause := [(4,true),(14,true),(262,false)]
theorem inp_13899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13899 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13899 = (containClause5 4 14) := by decide
  rw [he]
  exact input_contain 4 14 (by decide) v hb
def cl_13900 : CNF.NClause := [(4,true),(15,true),(263,false)]
theorem inp_13900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13900 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13900 = (containClause5 4 15) := by decide
  rw [he]
  exact input_contain 4 15 (by decide) v hb
def cl_13901 : CNF.NClause := [(4,true),(16,true),(264,false)]
theorem inp_13901 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13901 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13901 = (containClause5 4 16) := by decide
  rw [he]
  exact input_contain 4 16 (by decide) v hb
def cl_13902 : CNF.NClause := [(4,true),(17,true),(265,false)]
theorem inp_13902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13902 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13902 = (containClause5 4 17) := by decide
  rw [he]
  exact input_contain 4 17 (by decide) v hb
def cl_13903 : CNF.NClause := [(4,true),(18,true),(266,false)]
theorem inp_13903 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13903 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13903 = (containClause5 4 18) := by decide
  rw [he]
  exact input_contain 4 18 (by decide) v hb
def cl_13904 : CNF.NClause := [(4,true),(19,true),(267,false)]
theorem inp_13904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13904 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13904 = (containClause5 4 19) := by decide
  rw [he]
  exact input_contain 4 19 (by decide) v hb
end Percolation.NReplay
