import NInputs206
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_13755 : CNF.NClause := [(20,true),(764,true)]
theorem inp_13755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13755 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13755 = (omitClause5 20) := by decide
  rw [he]
  exact input_omit 20 v hb
def cl_13756 : CNF.NClause := [(21,true),(796,true)]
theorem inp_13756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13756 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13756 v hb
def cl_13757 : CNF.NClause := [(22,true),(828,true)]
theorem inp_13757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13757 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13757 v hb
def cl_13758 : CNF.NClause := [(23,true),(860,true)]
theorem inp_13758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13758 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13758 = (omitClause5 23) := by decide
  rw [he]
  exact input_omit 23 v hb
def cl_13759 : CNF.NClause := [(24,true),(892,true)]
theorem inp_13759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13759 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13759 = (omitClause5 24) := by decide
  rw [he]
  exact input_omit 24 v hb
def cl_13760 : CNF.NClause := [(25,true),(924,true)]
theorem inp_13760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13760 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13760 = (omitClause5 25) := by decide
  rw [he]
  exact input_omit 25 v hb
def cl_13761 : CNF.NClause := [(26,true),(956,true)]
theorem inp_13761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13761 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13761 = (omitClause5 26) := by decide
  rw [he]
  exact input_omit 26 v hb
def cl_13762 : CNF.NClause := [(27,true),(988,true)]
theorem inp_13762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13762 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13762 = (omitClause5 27) := by decide
  rw [he]
  exact input_omit 27 v hb
def cl_13763 : CNF.NClause := [(28,true),(1020,true)]
theorem inp_13763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13763 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13763 v hb
def cl_13764 : CNF.NClause := [(29,true),(1052,true)]
theorem inp_13764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13764 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13764 = (omitClause5 29) := by decide
  rw [he]
  exact input_omit 29 v hb
def cl_13765 : CNF.NClause := [(30,true),(1084,true)]
theorem inp_13765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13765 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_13765 v hb
def cl_13766 : CNF.NClause := [(0,true),(1,true),(125,false)]
theorem inp_13766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13766 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13766 = (containClause5 0 1) := by decide
  rw [he]
  exact input_contain 0 1 (by decide) v hb
def cl_13767 : CNF.NClause := [(0,true),(2,true),(126,false)]
theorem inp_13767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13767 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13767 = (containClause5 0 2) := by decide
  rw [he]
  exact input_contain 0 2 (by decide) v hb
def cl_13768 : CNF.NClause := [(0,true),(3,true),(127,false)]
theorem inp_13768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13768 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13768 = (containClause5 0 3) := by decide
  rw [he]
  exact input_contain 0 3 (by decide) v hb
def cl_13769 : CNF.NClause := [(0,true),(4,true),(128,false)]
theorem inp_13769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13769 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13769 = (containClause5 0 4) := by decide
  rw [he]
  exact input_contain 0 4 (by decide) v hb
def cl_13770 : CNF.NClause := [(0,true),(5,true),(129,false)]
theorem inp_13770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13770 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13770 = (containClause5 0 5) := by decide
  rw [he]
  exact input_contain 0 5 (by decide) v hb
def cl_13771 : CNF.NClause := [(0,true),(6,true),(130,false)]
theorem inp_13771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13771 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13771 = (containClause5 0 6) := by decide
  rw [he]
  exact input_contain 0 6 (by decide) v hb
def cl_13772 : CNF.NClause := [(0,true),(7,true),(131,false)]
theorem inp_13772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13772 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13772 = (containClause5 0 7) := by decide
  rw [he]
  exact input_contain 0 7 (by decide) v hb
def cl_13773 : CNF.NClause := [(0,true),(8,true),(132,false)]
theorem inp_13773 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13773 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13773 = (containClause5 0 8) := by decide
  rw [he]
  exact input_contain 0 8 (by decide) v hb
def cl_13774 : CNF.NClause := [(0,true),(9,true),(133,false)]
theorem inp_13774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13774 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13774 = (containClause5 0 9) := by decide
  rw [he]
  exact input_contain 0 9 (by decide) v hb
def cl_13775 : CNF.NClause := [(0,true),(10,true),(134,false)]
theorem inp_13775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13775 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13775 = (containClause5 0 10) := by decide
  rw [he]
  exact input_contain 0 10 (by decide) v hb
def cl_13776 : CNF.NClause := [(0,true),(11,true),(135,false)]
theorem inp_13776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13776 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13776 = (containClause5 0 11) := by decide
  rw [he]
  exact input_contain 0 11 (by decide) v hb
def cl_13777 : CNF.NClause := [(0,true),(12,true),(136,false)]
theorem inp_13777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13777 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13777 = (containClause5 0 12) := by decide
  rw [he]
  exact input_contain 0 12 (by decide) v hb
def cl_13778 : CNF.NClause := [(0,true),(13,true),(137,false)]
theorem inp_13778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13778 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13778 = (containClause5 0 13) := by decide
  rw [he]
  exact input_contain 0 13 (by decide) v hb
def cl_13779 : CNF.NClause := [(0,true),(14,true),(138,false)]
theorem inp_13779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13779 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13779 = (containClause5 0 14) := by decide
  rw [he]
  exact input_contain 0 14 (by decide) v hb
def cl_13780 : CNF.NClause := [(0,true),(15,true),(139,false)]
theorem inp_13780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13780 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13780 = (containClause5 0 15) := by decide
  rw [he]
  exact input_contain 0 15 (by decide) v hb
def cl_13781 : CNF.NClause := [(0,true),(16,true),(140,false)]
theorem inp_13781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13781 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13781 = (containClause5 0 16) := by decide
  rw [he]
  exact input_contain 0 16 (by decide) v hb
def cl_13782 : CNF.NClause := [(0,true),(17,true),(141,false)]
theorem inp_13782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13782 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13782 = (containClause5 0 17) := by decide
  rw [he]
  exact input_contain 0 17 (by decide) v hb
def cl_13783 : CNF.NClause := [(0,true),(18,true),(142,false)]
theorem inp_13783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13783 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13783 = (containClause5 0 18) := by decide
  rw [he]
  exact input_contain 0 18 (by decide) v hb
def cl_13784 : CNF.NClause := [(0,true),(19,true),(143,false)]
theorem inp_13784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13784 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13784 = (containClause5 0 19) := by decide
  rw [he]
  exact input_contain 0 19 (by decide) v hb
def cl_13785 : CNF.NClause := [(0,true),(20,true),(144,false)]
theorem inp_13785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13785 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13785 = (containClause5 0 20) := by decide
  rw [he]
  exact input_contain 0 20 (by decide) v hb
def cl_13786 : CNF.NClause := [(0,true),(21,true),(145,false)]
theorem inp_13786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13786 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13786 = (containClause5 0 21) := by decide
  rw [he]
  exact input_contain 0 21 (by decide) v hb
def cl_13787 : CNF.NClause := [(0,true),(22,true),(146,false)]
theorem inp_13787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13787 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13787 = (containClause5 0 22) := by decide
  rw [he]
  exact input_contain 0 22 (by decide) v hb
def cl_13788 : CNF.NClause := [(0,true),(23,true),(147,false)]
theorem inp_13788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13788 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13788 = (containClause5 0 23) := by decide
  rw [he]
  exact input_contain 0 23 (by decide) v hb
def cl_13789 : CNF.NClause := [(0,true),(24,true),(148,false)]
theorem inp_13789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13789 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13789 = (containClause5 0 24) := by decide
  rw [he]
  exact input_contain 0 24 (by decide) v hb
def cl_13790 : CNF.NClause := [(0,true),(25,true),(149,false)]
theorem inp_13790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13790 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13790 = (containClause5 0 25) := by decide
  rw [he]
  exact input_contain 0 25 (by decide) v hb
def cl_13791 : CNF.NClause := [(0,true),(26,true),(150,false)]
theorem inp_13791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13791 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13791 = (containClause5 0 26) := by decide
  rw [he]
  exact input_contain 0 26 (by decide) v hb
def cl_13792 : CNF.NClause := [(0,true),(27,true),(151,false)]
theorem inp_13792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13792 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13792 = (containClause5 0 27) := by decide
  rw [he]
  exact input_contain 0 27 (by decide) v hb
def cl_13793 : CNF.NClause := [(0,true),(28,true),(152,false)]
theorem inp_13793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13793 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13793 = (containClause5 0 28) := by decide
  rw [he]
  exact input_contain 0 28 (by decide) v hb
def cl_13794 : CNF.NClause := [(0,true),(29,true),(153,false)]
theorem inp_13794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13794 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13794 = (containClause5 0 29) := by decide
  rw [he]
  exact input_contain 0 29 (by decide) v hb
def cl_13795 : CNF.NClause := [(0,true),(30,true),(154,false)]
theorem inp_13795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13795 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13795 = (containClause5 0 30) := by decide
  rw [he]
  exact input_contain 0 30 (by decide) v hb
def cl_13796 : CNF.NClause := [(1,true),(0,true),(155,false)]
theorem inp_13796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13796 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13796 = (containClause5 1 0) := by decide
  rw [he]
  exact input_contain 1 0 (by decide) v hb
def cl_13797 : CNF.NClause := [(1,true),(2,true),(157,false)]
theorem inp_13797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13797 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13797 = (containClause5 1 2) := by decide
  rw [he]
  exact input_contain 1 2 (by decide) v hb
def cl_13798 : CNF.NClause := [(1,true),(3,true),(158,false)]
theorem inp_13798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13798 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13798 = (containClause5 1 3) := by decide
  rw [he]
  exact input_contain 1 3 (by decide) v hb
def cl_13799 : CNF.NClause := [(1,true),(4,true),(159,false)]
theorem inp_13799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13799 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13799 = (containClause5 1 4) := by decide
  rw [he]
  exact input_contain 1 4 (by decide) v hb
def cl_13800 : CNF.NClause := [(1,true),(5,true),(160,false)]
theorem inp_13800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13800 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13800 = (containClause5 1 5) := by decide
  rw [he]
  exact input_contain 1 5 (by decide) v hb
def cl_13801 : CNF.NClause := [(1,true),(6,true),(161,false)]
theorem inp_13801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13801 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13801 = (containClause5 1 6) := by decide
  rw [he]
  exact input_contain 1 6 (by decide) v hb
def cl_13802 : CNF.NClause := [(1,true),(7,true),(162,false)]
theorem inp_13802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13802 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13802 = (containClause5 1 7) := by decide
  rw [he]
  exact input_contain 1 7 (by decide) v hb
def cl_13803 : CNF.NClause := [(1,true),(8,true),(163,false)]
theorem inp_13803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13803 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13803 = (containClause5 1 8) := by decide
  rw [he]
  exact input_contain 1 8 (by decide) v hb
def cl_13804 : CNF.NClause := [(1,true),(9,true),(164,false)]
theorem inp_13804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_13804 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause cl_13804 = (containClause5 1 9) := by decide
  rw [he]
  exact input_contain 1 9 (by decide) v hb
end Percolation.NReplay
