import NInputs209
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_13905 : CNF.NClause := [(4,true),(20,true),(268,false)]
theorem inp_13905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13905 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13905 = (containClause5 4 20) := by decide
  rw [he]
  exact input_contain 4 20 (by decide) v hb
def cl_13906 : CNF.NClause := [(4,true),(21,true),(269,false)]
theorem inp_13906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13906 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13906 = (containClause5 4 21) := by decide
  rw [he]
  exact input_contain 4 21 (by decide) v hb
def cl_13907 : CNF.NClause := [(4,true),(22,true),(270,false)]
theorem inp_13907 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13907 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13907 = (containClause5 4 22) := by decide
  rw [he]
  exact input_contain 4 22 (by decide) v hb
def cl_13908 : CNF.NClause := [(4,true),(23,true),(271,false)]
theorem inp_13908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13908 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13908 = (containClause5 4 23) := by decide
  rw [he]
  exact input_contain 4 23 (by decide) v hb
def cl_13909 : CNF.NClause := [(4,true),(24,true),(272,false)]
theorem inp_13909 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13909 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13909 = (containClause5 4 24) := by decide
  rw [he]
  exact input_contain 4 24 (by decide) v hb
def cl_13910 : CNF.NClause := [(4,true),(25,true),(273,false)]
theorem inp_13910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13910 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13910 = (containClause5 4 25) := by decide
  rw [he]
  exact input_contain 4 25 (by decide) v hb
def cl_13911 : CNF.NClause := [(4,true),(26,true),(274,false)]
theorem inp_13911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13911 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13911 = (containClause5 4 26) := by decide
  rw [he]
  exact input_contain 4 26 (by decide) v hb
def cl_13912 : CNF.NClause := [(4,true),(27,true),(275,false)]
theorem inp_13912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13912 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13912 = (containClause5 4 27) := by decide
  rw [he]
  exact input_contain 4 27 (by decide) v hb
def cl_13913 : CNF.NClause := [(4,true),(28,true),(276,false)]
theorem inp_13913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13913 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13913 = (containClause5 4 28) := by decide
  rw [he]
  exact input_contain 4 28 (by decide) v hb
def cl_13914 : CNF.NClause := [(4,true),(29,true),(277,false)]
theorem inp_13914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13914 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13914 = (containClause5 4 29) := by decide
  rw [he]
  exact input_contain 4 29 (by decide) v hb
def cl_13915 : CNF.NClause := [(4,true),(30,true),(278,false)]
theorem inp_13915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13915 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13915 = (containClause5 4 30) := by decide
  rw [he]
  exact input_contain 4 30 (by decide) v hb
def cl_13916 : CNF.NClause := [(5,true),(0,true),(279,false)]
theorem inp_13916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13916 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13916 v hb
def cl_13917 : CNF.NClause := [(5,true),(1,true),(280,false)]
theorem inp_13917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13917 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13917 v hb
def cl_13918 : CNF.NClause := [(5,true),(2,true),(281,false)]
theorem inp_13918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13918 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13918 v hb
def cl_13919 : CNF.NClause := [(5,true),(3,true),(282,false)]
theorem inp_13919 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13919 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13919 v hb
def cl_13920 : CNF.NClause := [(5,true),(4,true),(283,false)]
theorem inp_13920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13920 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13920 = (containClause5 5 4) := by decide
  rw [he]
  exact input_contain 5 4 (by decide) v hb
def cl_13921 : CNF.NClause := [(5,true),(6,true),(285,false)]
theorem inp_13921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13921 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13921 v hb
def cl_13922 : CNF.NClause := [(5,true),(7,true),(286,false)]
theorem inp_13922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13922 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13922 = (containClause5 5 7) := by decide
  rw [he]
  exact input_contain 5 7 (by decide) v hb
def cl_13923 : CNF.NClause := [(5,true),(8,true),(287,false)]
theorem inp_13923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13923 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13923 v hb
def cl_13924 : CNF.NClause := [(5,true),(9,true),(288,false)]
theorem inp_13924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13924 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13924 v hb
def cl_13925 : CNF.NClause := [(5,true),(10,true),(289,false)]
theorem inp_13925 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13925 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13925 v hb
def cl_13926 : CNF.NClause := [(5,true),(11,true),(290,false)]
theorem inp_13926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13926 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13926 = (containClause5 5 11) := by decide
  rw [he]
  exact input_contain 5 11 (by decide) v hb
def cl_13927 : CNF.NClause := [(5,true),(12,true),(291,false)]
theorem inp_13927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13927 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13927 v hb
def cl_13928 : CNF.NClause := [(5,true),(13,true),(292,false)]
theorem inp_13928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13928 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13928 v hb
def cl_13929 : CNF.NClause := [(5,true),(14,true),(293,false)]
theorem inp_13929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13929 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13929 = (containClause5 5 14) := by decide
  rw [he]
  exact input_contain 5 14 (by decide) v hb
def cl_13930 : CNF.NClause := [(5,true),(15,true),(294,false)]
theorem inp_13930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13930 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13930 v hb
def cl_13931 : CNF.NClause := [(5,true),(16,true),(295,false)]
theorem inp_13931 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13931 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13931 = (containClause5 5 16) := by decide
  rw [he]
  exact input_contain 5 16 (by decide) v hb
def cl_13932 : CNF.NClause := [(5,true),(17,true),(296,false)]
theorem inp_13932 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13932 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13932 = (containClause5 5 17) := by decide
  rw [he]
  exact input_contain 5 17 (by decide) v hb
def cl_13933 : CNF.NClause := [(5,true),(18,true),(297,false)]
theorem inp_13933 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13933 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13933 v hb
def cl_13934 : CNF.NClause := [(5,true),(19,true),(298,false)]
theorem inp_13934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13934 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13934 v hb
def cl_13935 : CNF.NClause := [(5,true),(20,true),(299,false)]
theorem inp_13935 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13935 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13935 = (containClause5 5 20) := by decide
  rw [he]
  exact input_contain 5 20 (by decide) v hb
def cl_13936 : CNF.NClause := [(5,true),(21,true),(300,false)]
theorem inp_13936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13936 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13936 v hb
def cl_13937 : CNF.NClause := [(5,true),(22,true),(301,false)]
theorem inp_13937 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13937 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13937 = (containClause5 5 22) := by decide
  rw [he]
  exact input_contain 5 22 (by decide) v hb
def cl_13938 : CNF.NClause := [(5,true),(23,true),(302,false)]
theorem inp_13938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13938 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13938 v hb
def cl_13939 : CNF.NClause := [(5,true),(24,true),(303,false)]
theorem inp_13939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13939 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13939 v hb
def cl_13940 : CNF.NClause := [(5,true),(25,true),(304,false)]
theorem inp_13940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13940 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13940 v hb
def cl_13941 : CNF.NClause := [(5,true),(26,true),(305,false)]
theorem inp_13941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13941 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13941 v hb
def cl_13942 : CNF.NClause := [(5,true),(27,true),(306,false)]
theorem inp_13942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13942 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13942 v hb
def cl_13943 : CNF.NClause := [(5,true),(28,true),(307,false)]
theorem inp_13943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13943 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13943 v hb
def cl_13944 : CNF.NClause := [(5,true),(29,true),(308,false)]
theorem inp_13944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13944 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13944 v hb
def cl_13945 : CNF.NClause := [(5,true),(30,true),(309,false)]
theorem inp_13945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13945 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13945 = (containClause5 5 30) := by decide
  rw [he]
  exact input_contain 5 30 (by decide) v hb
def cl_13946 : CNF.NClause := [(6,true),(0,true),(310,false)]
theorem inp_13946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13946 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13946 = (containClause5 6 0) := by decide
  rw [he]
  exact input_contain 6 0 (by decide) v hb
def cl_13947 : CNF.NClause := [(6,true),(1,true),(311,false)]
theorem inp_13947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13947 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13947 = (containClause5 6 1) := by decide
  rw [he]
  exact input_contain 6 1 (by decide) v hb
def cl_13948 : CNF.NClause := [(6,true),(2,true),(312,false)]
theorem inp_13948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13948 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13948 = (containClause5 6 2) := by decide
  rw [he]
  exact input_contain 6 2 (by decide) v hb
def cl_13949 : CNF.NClause := [(6,true),(3,true),(313,false)]
theorem inp_13949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13949 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13949 = (containClause5 6 3) := by decide
  rw [he]
  exact input_contain 6 3 (by decide) v hb
def cl_13950 : CNF.NClause := [(6,true),(4,true),(314,false)]
theorem inp_13950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13950 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13950 = (containClause5 6 4) := by decide
  rw [he]
  exact input_contain 6 4 (by decide) v hb
def cl_13951 : CNF.NClause := [(6,true),(5,true),(315,false)]
theorem inp_13951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13951 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13951 = (containClause5 6 5) := by decide
  rw [he]
  exact input_contain 6 5 (by decide) v hb
def cl_13952 : CNF.NClause := [(6,true),(7,true),(317,false)]
theorem inp_13952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13952 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13952 = (containClause5 6 7) := by decide
  rw [he]
  exact input_contain 6 7 (by decide) v hb
def cl_13953 : CNF.NClause := [(6,true),(8,true),(318,false)]
theorem inp_13953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13953 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13953 = (containClause5 6 8) := by decide
  rw [he]
  exact input_contain 6 8 (by decide) v hb
def cl_13954 : CNF.NClause := [(6,true),(9,true),(319,false)]
theorem inp_13954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13954 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13954 = (containClause5 6 9) := by decide
  rw [he]
  exact input_contain 6 9 (by decide) v hb
end Percolation.NReplay
