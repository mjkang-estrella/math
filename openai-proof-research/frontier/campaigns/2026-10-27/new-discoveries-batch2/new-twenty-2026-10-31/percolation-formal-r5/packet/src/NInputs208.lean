import NInputs207
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_13805 : CNF.NClause := [(1,true),(10,true),(165,false)]
theorem inp_13805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13805 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13805 = (containClause5 1 10) := by decide
  rw [he]
  exact input_contain 1 10 (by decide) v hb
def cl_13806 : CNF.NClause := [(1,true),(11,true),(166,false)]
theorem inp_13806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13806 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13806 = (containClause5 1 11) := by decide
  rw [he]
  exact input_contain 1 11 (by decide) v hb
def cl_13807 : CNF.NClause := [(1,true),(12,true),(167,false)]
theorem inp_13807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13807 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13807 = (containClause5 1 12) := by decide
  rw [he]
  exact input_contain 1 12 (by decide) v hb
def cl_13808 : CNF.NClause := [(1,true),(13,true),(168,false)]
theorem inp_13808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13808 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13808 = (containClause5 1 13) := by decide
  rw [he]
  exact input_contain 1 13 (by decide) v hb
def cl_13809 : CNF.NClause := [(1,true),(14,true),(169,false)]
theorem inp_13809 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13809 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13809 = (containClause5 1 14) := by decide
  rw [he]
  exact input_contain 1 14 (by decide) v hb
def cl_13810 : CNF.NClause := [(1,true),(15,true),(170,false)]
theorem inp_13810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13810 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13810 = (containClause5 1 15) := by decide
  rw [he]
  exact input_contain 1 15 (by decide) v hb
def cl_13811 : CNF.NClause := [(1,true),(16,true),(171,false)]
theorem inp_13811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13811 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13811 = (containClause5 1 16) := by decide
  rw [he]
  exact input_contain 1 16 (by decide) v hb
def cl_13812 : CNF.NClause := [(1,true),(17,true),(172,false)]
theorem inp_13812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13812 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13812 = (containClause5 1 17) := by decide
  rw [he]
  exact input_contain 1 17 (by decide) v hb
def cl_13813 : CNF.NClause := [(1,true),(18,true),(173,false)]
theorem inp_13813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13813 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13813 = (containClause5 1 18) := by decide
  rw [he]
  exact input_contain 1 18 (by decide) v hb
def cl_13814 : CNF.NClause := [(1,true),(19,true),(174,false)]
theorem inp_13814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13814 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13814 = (containClause5 1 19) := by decide
  rw [he]
  exact input_contain 1 19 (by decide) v hb
def cl_13815 : CNF.NClause := [(1,true),(20,true),(175,false)]
theorem inp_13815 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13815 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13815 = (containClause5 1 20) := by decide
  rw [he]
  exact input_contain 1 20 (by decide) v hb
def cl_13816 : CNF.NClause := [(1,true),(21,true),(176,false)]
theorem inp_13816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13816 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13816 = (containClause5 1 21) := by decide
  rw [he]
  exact input_contain 1 21 (by decide) v hb
def cl_13817 : CNF.NClause := [(1,true),(22,true),(177,false)]
theorem inp_13817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13817 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13817 = (containClause5 1 22) := by decide
  rw [he]
  exact input_contain 1 22 (by decide) v hb
def cl_13818 : CNF.NClause := [(1,true),(23,true),(178,false)]
theorem inp_13818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13818 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13818 = (containClause5 1 23) := by decide
  rw [he]
  exact input_contain 1 23 (by decide) v hb
def cl_13819 : CNF.NClause := [(1,true),(24,true),(179,false)]
theorem inp_13819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13819 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13819 = (containClause5 1 24) := by decide
  rw [he]
  exact input_contain 1 24 (by decide) v hb
def cl_13820 : CNF.NClause := [(1,true),(25,true),(180,false)]
theorem inp_13820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13820 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13820 = (containClause5 1 25) := by decide
  rw [he]
  exact input_contain 1 25 (by decide) v hb
def cl_13821 : CNF.NClause := [(1,true),(26,true),(181,false)]
theorem inp_13821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13821 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13821 = (containClause5 1 26) := by decide
  rw [he]
  exact input_contain 1 26 (by decide) v hb
def cl_13822 : CNF.NClause := [(1,true),(27,true),(182,false)]
theorem inp_13822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13822 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13822 = (containClause5 1 27) := by decide
  rw [he]
  exact input_contain 1 27 (by decide) v hb
def cl_13823 : CNF.NClause := [(1,true),(28,true),(183,false)]
theorem inp_13823 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13823 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13823 = (containClause5 1 28) := by decide
  rw [he]
  exact input_contain 1 28 (by decide) v hb
def cl_13824 : CNF.NClause := [(1,true),(29,true),(184,false)]
theorem inp_13824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13824 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13824 = (containClause5 1 29) := by decide
  rw [he]
  exact input_contain 1 29 (by decide) v hb
def cl_13825 : CNF.NClause := [(1,true),(30,true),(185,false)]
theorem inp_13825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13825 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13825 = (containClause5 1 30) := by decide
  rw [he]
  exact input_contain 1 30 (by decide) v hb
def cl_13826 : CNF.NClause := [(2,true),(0,true),(186,false)]
theorem inp_13826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13826 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13826 v hb
def cl_13827 : CNF.NClause := [(2,true),(1,true),(187,false)]
theorem inp_13827 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13827 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13827 = (containClause5 2 1) := by decide
  rw [he]
  exact input_contain 2 1 (by decide) v hb
def cl_13828 : CNF.NClause := [(2,true),(3,true),(189,false)]
theorem inp_13828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13828 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13828 = (containClause5 2 3) := by decide
  rw [he]
  exact input_contain 2 3 (by decide) v hb
def cl_13829 : CNF.NClause := [(2,true),(4,true),(190,false)]
theorem inp_13829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13829 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13829 = (containClause5 2 4) := by decide
  rw [he]
  exact input_contain 2 4 (by decide) v hb
def cl_13830 : CNF.NClause := [(2,true),(5,true),(191,false)]
theorem inp_13830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13830 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13830 v hb
def cl_13831 : CNF.NClause := [(2,true),(6,true),(192,false)]
theorem inp_13831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13831 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13831 = (containClause5 2 6) := by decide
  rw [he]
  exact input_contain 2 6 (by decide) v hb
def cl_13832 : CNF.NClause := [(2,true),(7,true),(193,false)]
theorem inp_13832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13832 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13832 = (containClause5 2 7) := by decide
  rw [he]
  exact input_contain 2 7 (by decide) v hb
def cl_13833 : CNF.NClause := [(2,true),(8,true),(194,false)]
theorem inp_13833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13833 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13833 = (containClause5 2 8) := by decide
  rw [he]
  exact input_contain 2 8 (by decide) v hb
def cl_13834 : CNF.NClause := [(2,true),(9,true),(195,false)]
theorem inp_13834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13834 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13834 = (containClause5 2 9) := by decide
  rw [he]
  exact input_contain 2 9 (by decide) v hb
def cl_13835 : CNF.NClause := [(2,true),(10,true),(196,false)]
theorem inp_13835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13835 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13835 v hb
def cl_13836 : CNF.NClause := [(2,true),(11,true),(197,false)]
theorem inp_13836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13836 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13836 = (containClause5 2 11) := by decide
  rw [he]
  exact input_contain 2 11 (by decide) v hb
def cl_13837 : CNF.NClause := [(2,true),(12,true),(198,false)]
theorem inp_13837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13837 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13837 = (containClause5 2 12) := by decide
  rw [he]
  exact input_contain 2 12 (by decide) v hb
def cl_13838 : CNF.NClause := [(2,true),(13,true),(199,false)]
theorem inp_13838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13838 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13838 = (containClause5 2 13) := by decide
  rw [he]
  exact input_contain 2 13 (by decide) v hb
def cl_13839 : CNF.NClause := [(2,true),(14,true),(200,false)]
theorem inp_13839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13839 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13839 = (containClause5 2 14) := by decide
  rw [he]
  exact input_contain 2 14 (by decide) v hb
def cl_13840 : CNF.NClause := [(2,true),(15,true),(201,false)]
theorem inp_13840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13840 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13840 v hb
def cl_13841 : CNF.NClause := [(2,true),(16,true),(202,false)]
theorem inp_13841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13841 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13841 = (containClause5 2 16) := by decide
  rw [he]
  exact input_contain 2 16 (by decide) v hb
def cl_13842 : CNF.NClause := [(2,true),(17,true),(203,false)]
theorem inp_13842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13842 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13842 = (containClause5 2 17) := by decide
  rw [he]
  exact input_contain 2 17 (by decide) v hb
def cl_13843 : CNF.NClause := [(2,true),(18,true),(204,false)]
theorem inp_13843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13843 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13843 = (containClause5 2 18) := by decide
  rw [he]
  exact input_contain 2 18 (by decide) v hb
def cl_13844 : CNF.NClause := [(2,true),(19,true),(205,false)]
theorem inp_13844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13844 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13844 = (containClause5 2 19) := by decide
  rw [he]
  exact input_contain 2 19 (by decide) v hb
def cl_13845 : CNF.NClause := [(2,true),(20,true),(206,false)]
theorem inp_13845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13845 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13845 v hb
def cl_13846 : CNF.NClause := [(2,true),(21,true),(207,false)]
theorem inp_13846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13846 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13846 = (containClause5 2 21) := by decide
  rw [he]
  exact input_contain 2 21 (by decide) v hb
def cl_13847 : CNF.NClause := [(2,true),(22,true),(208,false)]
theorem inp_13847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13847 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13847 = (containClause5 2 22) := by decide
  rw [he]
  exact input_contain 2 22 (by decide) v hb
def cl_13848 : CNF.NClause := [(2,true),(23,true),(209,false)]
theorem inp_13848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13848 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13848 = (containClause5 2 23) := by decide
  rw [he]
  exact input_contain 2 23 (by decide) v hb
def cl_13849 : CNF.NClause := [(2,true),(24,true),(210,false)]
theorem inp_13849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13849 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13849 = (containClause5 2 24) := by decide
  rw [he]
  exact input_contain 2 24 (by decide) v hb
def cl_13850 : CNF.NClause := [(2,true),(25,true),(211,false)]
theorem inp_13850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13850 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13850 = (containClause5 2 25) := by decide
  rw [he]
  exact input_contain 2 25 (by decide) v hb
def cl_13851 : CNF.NClause := [(2,true),(26,true),(212,false)]
theorem inp_13851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13851 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13851 = (containClause5 2 26) := by decide
  rw [he]
  exact input_contain 2 26 (by decide) v hb
def cl_13852 : CNF.NClause := [(2,true),(27,true),(213,false)]
theorem inp_13852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13852 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13852 = (containClause5 2 27) := by decide
  rw [he]
  exact input_contain 2 27 (by decide) v hb
def cl_13853 : CNF.NClause := [(2,true),(28,true),(214,false)]
theorem inp_13853 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13853 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13853 = (containClause5 2 28) := by decide
  rw [he]
  exact input_contain 2 28 (by decide) v hb
def cl_13854 : CNF.NClause := [(2,true),(29,true),(215,false)]
theorem inp_13854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13854 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13854 = (containClause5 2 29) := by decide
  rw [he]
  exact input_contain 2 29 (by decide) v hb
end Percolation.NReplay
