import NInputs184
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_11863 : CNF.NClause := [(744,true),(750,true),(756,true),(762,true),(768,false),(770,true)]
theorem inp_11863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11863 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 29) (closed_mem 20 29) cl_11863 (by decide) v hb
def cl_11864 : CNF.NClause := [(744,true),(750,true),(756,true),(762,false),(768,true),(770,true)]
theorem inp_11864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11864 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 29) (closed_mem 20 29) cl_11864 (by decide) v hb
def cl_11865 : CNF.NClause := [(744,true),(750,true),(756,false),(762,true),(768,true),(770,true)]
theorem inp_11865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11865 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 29) (closed_mem 20 29) cl_11865 (by decide) v hb
def cl_11866 : CNF.NClause := [(744,true),(750,false),(756,true),(762,true),(768,true),(770,true)]
theorem inp_11866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11866 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 29) (closed_mem 20 29) cl_11866 (by decide) v hb
def cl_11869 : CNF.NClause := [(744,true),(749,true),(754,true),(759,true),(764,false),(769,true)]
theorem inp_11869 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11869 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 20 30) (closed_mem 20 30) cl_11869 (by decide) v hb
def cl_11875 : CNF.NClause := [(800,true),(801,true),(802,true),(803,true),(804,false),(805,true)]
theorem inp_11875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11875 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 0) (closed_mem 21 0) cl_11875 (by decide) v hb
def cl_11876 : CNF.NClause := [(800,true),(801,true),(802,true),(803,false),(804,true),(805,true)]
theorem inp_11876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11876 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 0) (closed_mem 21 0) cl_11876 (by decide) v hb
def cl_11877 : CNF.NClause := [(800,true),(801,true),(802,false),(803,true),(804,true),(805,true)]
theorem inp_11877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11877 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 0) (closed_mem 21 0) cl_11877 (by decide) v hb
def cl_11878 : CNF.NClause := [(800,true),(801,false),(802,true),(803,true),(804,true),(805,true)]
theorem inp_11878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11878 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 0) (closed_mem 21 0) cl_11878 (by decide) v hb
def cl_11881 : CNF.NClause := [(779,true),(784,true),(789,true),(794,true),(799,false),(800,true)]
theorem inp_11881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11881 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 1) (closed_mem 21 1) cl_11881 (by decide) v hb
def cl_11882 : CNF.NClause := [(779,true),(784,true),(789,true),(794,false),(799,true),(800,true)]
theorem inp_11882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11882 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 1) (closed_mem 21 1) cl_11882 (by decide) v hb
def cl_11883 : CNF.NClause := [(779,true),(784,true),(789,false),(794,true),(799,true),(800,true)]
theorem inp_11883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11883 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 1) (closed_mem 21 1) cl_11883 (by decide) v hb
def cl_11884 : CNF.NClause := [(779,true),(784,false),(789,true),(794,true),(799,true),(800,true)]
theorem inp_11884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11884 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 1) (closed_mem 21 1) cl_11884 (by decide) v hb
def cl_11885 : CNF.NClause := [(779,false),(784,true),(789,true),(794,true),(799,true),(800,true)]
theorem inp_11885 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11885 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 1) (closed_mem 21 1) cl_11885 (by decide) v hb
def cl_11887 : CNF.NClause := [(777,true),(782,true),(787,true),(792,true),(797,false),(800,true)]
theorem inp_11887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11887 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 2) (closed_mem 21 2) cl_11887 (by decide) v hb
def cl_11888 : CNF.NClause := [(777,true),(782,true),(787,true),(792,false),(797,true),(800,true)]
theorem inp_11888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11888 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 2) (closed_mem 21 2) cl_11888 (by decide) v hb
def cl_11890 : CNF.NClause := [(777,true),(782,false),(787,true),(792,true),(797,true),(800,true)]
theorem inp_11890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11890 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 2) (closed_mem 21 2) cl_11890 (by decide) v hb
def cl_11891 : CNF.NClause := [(777,false),(782,true),(787,true),(792,true),(797,true),(800,true)]
theorem inp_11891 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11891 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 2) (closed_mem 21 2) cl_11891 (by decide) v hb
def cl_11893 : CNF.NClause := [(778,true),(783,true),(788,true),(793,true),(798,false),(800,true)]
theorem inp_11893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11893 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 3) (closed_mem 21 3) cl_11893 (by decide) v hb
def cl_11896 : CNF.NClause := [(778,true),(783,false),(788,true),(793,true),(798,true),(800,true)]
theorem inp_11896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11896 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 3) (closed_mem 21 3) cl_11896 (by decide) v hb
def cl_11899 : CNF.NClause := [(776,true),(781,true),(786,true),(791,true),(796,false),(800,true)]
theorem inp_11899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11899 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_11899 v hb
def cl_11908 : CNF.NClause := [(795,true),(796,false),(797,true),(798,true),(799,true),(805,true)]
theorem inp_11908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11908 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 5) (closed_mem 21 5) cl_11908 (by decide) v hb
def cl_11911 : CNF.NClause := [(779,true),(783,true),(787,true),(791,true),(795,false),(804,true)]
theorem inp_11911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11911 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 6) (closed_mem 21 6) cl_11911 (by decide) v hb
def cl_11915 : CNF.NClause := [(779,false),(783,true),(787,true),(791,true),(795,true),(804,true)]
theorem inp_11915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11915 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 6) (closed_mem 21 6) cl_11915 (by decide) v hb
def cl_11916 : CNF.NClause := [(777,true),(784,true),(786,true),(793,true),(795,true),(802,false)]
theorem inp_11916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11916 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 7) (closed_mem 21 7) cl_11916 (by decide) v hb
def cl_11917 : CNF.NClause := [(777,true),(784,true),(786,true),(793,true),(795,false),(802,true)]
theorem inp_11917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11917 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 7) (closed_mem 21 7) cl_11917 (by decide) v hb
def cl_11918 : CNF.NClause := [(777,true),(784,true),(786,true),(793,false),(795,true),(802,true)]
theorem inp_11918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11918 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 7) (closed_mem 21 7) cl_11918 (by decide) v hb
def cl_11919 : CNF.NClause := [(777,true),(784,true),(786,false),(793,true),(795,true),(802,true)]
theorem inp_11919 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11919 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 7) (closed_mem 21 7) cl_11919 (by decide) v hb
def cl_11921 : CNF.NClause := [(777,false),(784,true),(786,true),(793,true),(795,true),(802,true)]
theorem inp_11921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11921 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 7) (closed_mem 21 7) cl_11921 (by decide) v hb
def cl_11922 : CNF.NClause := [(778,true),(781,true),(789,true),(792,true),(795,true),(803,false)]
theorem inp_11922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11922 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 8) (closed_mem 21 8) cl_11922 (by decide) v hb
def cl_11923 : CNF.NClause := [(778,true),(781,true),(789,true),(792,true),(795,false),(803,true)]
theorem inp_11923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11923 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 8) (closed_mem 21 8) cl_11923 (by decide) v hb
def cl_11924 : CNF.NClause := [(778,true),(781,true),(789,true),(792,false),(795,true),(803,true)]
theorem inp_11924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11924 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 8) (closed_mem 21 8) cl_11924 (by decide) v hb
def cl_11925 : CNF.NClause := [(778,true),(781,true),(789,false),(792,true),(795,true),(803,true)]
theorem inp_11925 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11925 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 8) (closed_mem 21 8) cl_11925 (by decide) v hb
def cl_11926 : CNF.NClause := [(778,true),(781,false),(789,true),(792,true),(795,true),(803,true)]
theorem inp_11926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11926 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 8) (closed_mem 21 8) cl_11926 (by decide) v hb
def cl_11927 : CNF.NClause := [(778,false),(781,true),(789,true),(792,true),(795,true),(803,true)]
theorem inp_11927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11927 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 8) (closed_mem 21 8) cl_11927 (by decide) v hb
def cl_11928 : CNF.NClause := [(776,true),(782,true),(788,true),(794,true),(795,true),(801,false)]
theorem inp_11928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11928 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 9) (closed_mem 21 9) cl_11928 (by decide) v hb
def cl_11929 : CNF.NClause := [(776,true),(782,true),(788,true),(794,true),(795,false),(801,true)]
theorem inp_11929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11929 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 9) (closed_mem 21 9) cl_11929 (by decide) v hb
def cl_11930 : CNF.NClause := [(776,true),(782,true),(788,true),(794,false),(795,true),(801,true)]
theorem inp_11930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11930 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 9) (closed_mem 21 9) cl_11930 (by decide) v hb
def cl_11931 : CNF.NClause := [(776,true),(782,true),(788,false),(794,true),(795,true),(801,true)]
theorem inp_11931 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11931 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 9) (closed_mem 21 9) cl_11931 (by decide) v hb
def cl_11933 : CNF.NClause := [(776,false),(782,true),(788,true),(794,true),(795,true),(801,true)]
theorem inp_11933 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11933 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 9) (closed_mem 21 9) cl_11933 (by decide) v hb
def cl_11935 : CNF.NClause := [(785,true),(786,true),(787,true),(788,true),(789,false),(805,true)]
theorem inp_11935 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11935 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 10) (closed_mem 21 10) cl_11935 (by decide) v hb
def cl_11936 : CNF.NClause := [(785,true),(786,true),(787,true),(788,false),(789,true),(805,true)]
theorem inp_11936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11936 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 10) (closed_mem 21 10) cl_11936 (by decide) v hb
def cl_11937 : CNF.NClause := [(785,true),(786,true),(787,false),(788,true),(789,true),(805,true)]
theorem inp_11937 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11937 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 10) (closed_mem 21 10) cl_11937 (by decide) v hb
def cl_11938 : CNF.NClause := [(785,true),(786,false),(787,true),(788,true),(789,true),(805,true)]
theorem inp_11938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11938 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 10) (closed_mem 21 10) cl_11938 (by decide) v hb
def cl_11941 : CNF.NClause := [(779,true),(782,true),(785,true),(793,true),(796,false),(803,true)]
theorem inp_11941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11941 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 11) (closed_mem 21 11) cl_11941 (by decide) v hb
def cl_11946 : CNF.NClause := [(777,true),(781,true),(785,true),(794,true),(798,true),(804,false)]
theorem inp_11946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11946 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 12) (closed_mem 21 12) cl_11946 (by decide) v hb
def cl_11947 : CNF.NClause := [(777,true),(781,true),(785,true),(794,true),(798,false),(804,true)]
theorem inp_11947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11947 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 12) (closed_mem 21 12) cl_11947 (by decide) v hb
def cl_11949 : CNF.NClause := [(777,true),(781,true),(785,false),(794,true),(798,true),(804,true)]
theorem inp_11949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11949 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 12) (closed_mem 21 12) cl_11949 (by decide) v hb
def cl_11950 : CNF.NClause := [(777,true),(781,false),(785,true),(794,true),(798,true),(804,true)]
theorem inp_11950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11950 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 12) (closed_mem 21 12) cl_11950 (by decide) v hb
def cl_11953 : CNF.NClause := [(778,true),(784,true),(785,true),(791,true),(797,false),(801,true)]
theorem inp_11953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_11953 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 21 13) (closed_mem 21 13) cl_11953 (by decide) v hb
end Percolation.NReplay
