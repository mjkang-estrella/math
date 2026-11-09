import NInputs138
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_7896 : CNF.NClause := [(61,false),(30,true),(62,true),(67,true),(72,false),(77,true),(82,false),(87,true)]
theorem inp_7896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7896 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7896 (by decide) v hb
def cl_7898 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,true),(77,true),(82,false),(87,true)]
theorem inp_7898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7898 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7898 (by decide) v hb
def cl_7900 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,true),(77,true),(82,false),(87,true)]
theorem inp_7900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7900 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7900 (by decide) v hb
def cl_7902 : CNF.NClause := [(61,false),(30,true),(62,false),(67,true),(72,true),(77,true),(82,false),(87,true)]
theorem inp_7902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7902 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7902 (by decide) v hb
def cl_7904 : CNF.NClause := [(61,false),(30,true),(62,true),(67,true),(72,true),(77,true),(82,false),(87,true)]
theorem inp_7904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7904 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7904 (by decide) v hb
def cl_7906 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,false),(77,false),(82,true),(87,true)]
theorem inp_7906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7906 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7906 (by decide) v hb
def cl_7908 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,false),(77,false),(82,true),(87,true)]
theorem inp_7908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7908 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7908 (by decide) v hb
def cl_7910 : CNF.NClause := [(61,false),(30,true),(62,false),(67,true),(72,false),(77,false),(82,true),(87,true)]
theorem inp_7910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7910 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7910 (by decide) v hb
def cl_7912 : CNF.NClause := [(61,false),(30,true),(62,true),(67,true),(72,false),(77,false),(82,true),(87,true)]
theorem inp_7912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7912 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7912 (by decide) v hb
def cl_7914 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,true),(77,false),(82,true),(87,true)]
theorem inp_7914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7914 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7914 (by decide) v hb
def cl_7916 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,true),(77,false),(82,true),(87,true)]
theorem inp_7916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7916 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7916 (by decide) v hb
def cl_7918 : CNF.NClause := [(61,false),(30,true),(62,false),(67,true),(72,true),(77,false),(82,true),(87,true)]
theorem inp_7918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7918 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7918 (by decide) v hb
def cl_7920 : CNF.NClause := [(61,false),(30,true),(62,true),(67,true),(72,true),(77,false),(82,true),(87,true)]
theorem inp_7920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7920 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7920 (by decide) v hb
def cl_7922 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,false),(77,true),(82,true),(87,true)]
theorem inp_7922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7922 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7922 (by decide) v hb
def cl_7924 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,false),(77,true),(82,true),(87,true)]
theorem inp_7924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7924 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7924 (by decide) v hb
def cl_7926 : CNF.NClause := [(61,false),(30,true),(62,false),(67,true),(72,false),(77,true),(82,true),(87,true)]
theorem inp_7926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7926 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7926 (by decide) v hb
def cl_7928 : CNF.NClause := [(61,false),(30,true),(62,true),(67,true),(72,false),(77,true),(82,true),(87,true)]
theorem inp_7928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7928 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7928 (by decide) v hb
def cl_7930 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,true),(77,true),(82,true),(87,true)]
theorem inp_7930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7930 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7930 (by decide) v hb
def cl_7932 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,true),(77,true),(82,true),(87,true)]
theorem inp_7932 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7932 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7932 (by decide) v hb
def cl_7934 : CNF.NClause := [(61,false),(30,true),(62,false),(67,true),(72,true),(77,true),(82,true),(87,true)]
theorem inp_7934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7934 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7934 (by decide) v hb
def cl_7936 : CNF.NClause := [(61,false),(30,true),(62,true),(67,true),(72,true),(77,true),(82,true),(87,true)]
theorem inp_7936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7936 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7936 (by decide) v hb
def cl_7938 : CNF.NClause := [(32,false),(97,false),(102,false),(107,false),(112,false),(117,false),(118,false)]
theorem inp_7938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7938 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 1) (final_mem 1) cl_7938 (by decide) v hb
def cl_7939 : CNF.NClause := [(33,false),(95,false),(100,false),(105,false),(110,false),(115,false),(118,false)]
theorem inp_7939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7939 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 2) (final_mem 2) cl_7939 (by decide) v hb
def cl_7940 : CNF.NClause := [(34,false),(96,false),(101,false),(106,false),(111,false),(116,false),(118,false)]
theorem inp_7940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7940 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 3) (final_mem 3) cl_7940 (by decide) v hb
def cl_7941 : CNF.NClause := [(35,false),(94,false),(99,false),(104,false),(109,false),(114,false),(118,false)]
theorem inp_7941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7941 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 4) (final_mem 4) cl_7941 (by decide) v hb
def cl_7942 : CNF.NClause := [(36,false),(113,false),(114,false),(115,false),(116,false),(117,false),(123,false)]
theorem inp_7942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7942 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 5) (final_mem 5) cl_7942 (by decide) v hb
def cl_7943 : CNF.NClause := [(37,false),(97,false),(101,false),(105,false),(109,false),(113,false),(122,false)]
theorem inp_7943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7943 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 6) (final_mem 6) cl_7943 (by decide) v hb
def cl_7944 : CNF.NClause := [(38,false),(95,false),(102,false),(104,false),(111,false),(113,false),(120,false)]
theorem inp_7944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7944 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 7) (final_mem 7) cl_7944 (by decide) v hb
def cl_7945 : CNF.NClause := [(39,false),(96,false),(99,false),(107,false),(110,false),(113,false),(121,false)]
theorem inp_7945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7945 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 8) (final_mem 8) cl_7945 (by decide) v hb
def cl_7946 : CNF.NClause := [(40,false),(94,false),(100,false),(106,false),(112,false),(113,false),(119,false)]
theorem inp_7946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7946 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 9) (final_mem 9) cl_7946 (by decide) v hb
def cl_7947 : CNF.NClause := [(41,false),(103,false),(104,false),(105,false),(106,false),(107,false),(123,false)]
theorem inp_7947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7947 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 10) (final_mem 10) cl_7947 (by decide) v hb
def cl_7948 : CNF.NClause := [(42,false),(97,false),(100,false),(103,false),(111,false),(114,false),(121,false)]
theorem inp_7948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7948 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 11) (final_mem 11) cl_7948 (by decide) v hb
def cl_7949 : CNF.NClause := [(43,false),(95,false),(99,false),(103,false),(112,false),(116,false),(122,false)]
theorem inp_7949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7949 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 12) (final_mem 12) cl_7949 (by decide) v hb
def cl_7950 : CNF.NClause := [(44,false),(96,false),(102,false),(103,false),(109,false),(115,false),(119,false)]
theorem inp_7950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7950 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 13) (final_mem 13) cl_7950 (by decide) v hb
def cl_7951 : CNF.NClause := [(45,false),(94,false),(101,false),(103,false),(110,false),(117,false),(120,false)]
theorem inp_7951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7951 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 14) (final_mem 14) cl_7951 (by decide) v hb
def cl_7952 : CNF.NClause := [(46,false),(108,false),(109,false),(110,false),(111,false),(112,false),(123,false)]
theorem inp_7952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7952 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 15) (final_mem 15) cl_7952 (by decide) v hb
def cl_7953 : CNF.NClause := [(47,false),(97,false),(99,false),(106,false),(108,false),(115,false),(120,false)]
theorem inp_7953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7953 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 16) (final_mem 16) cl_7953 (by decide) v hb
def cl_7954 : CNF.NClause := [(48,false),(95,false),(101,false),(107,false),(108,false),(114,false),(119,false)]
theorem inp_7954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7954 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 17) (final_mem 17) cl_7954 (by decide) v hb
def cl_7955 : CNF.NClause := [(49,false),(96,false),(100,false),(104,false),(108,false),(117,false),(122,false)]
theorem inp_7955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7955 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 18) (final_mem 18) cl_7955 (by decide) v hb
def cl_7956 : CNF.NClause := [(50,false),(94,false),(102,false),(105,false),(108,false),(116,false),(121,false)]
theorem inp_7956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7956 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 19) (final_mem 19) cl_7956 (by decide) v hb
def cl_7957 : CNF.NClause := [(51,false),(98,false),(99,false),(100,false),(101,false),(102,false),(123,false)]
theorem inp_7957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7957 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 20) (final_mem 20) cl_7957 (by decide) v hb
def cl_7958 : CNF.NClause := [(52,false),(97,false),(98,false),(104,false),(110,false),(116,false),(119,false)]
theorem inp_7958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7958 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 21) (final_mem 21) cl_7958 (by decide) v hb
def cl_7959 : CNF.NClause := [(53,false),(95,false),(98,false),(106,false),(109,false),(117,false),(121,false)]
theorem inp_7959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7959 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 22) (final_mem 22) cl_7959 (by decide) v hb
def cl_7960 : CNF.NClause := [(54,false),(96,false),(98,false),(105,false),(112,false),(114,false),(120,false)]
theorem inp_7960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7960 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 23) (final_mem 23) cl_7960 (by decide) v hb
def cl_7961 : CNF.NClause := [(55,false),(94,false),(98,false),(107,false),(111,false),(115,false),(122,false)]
theorem inp_7961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7961 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 24) (final_mem 24) cl_7961 (by decide) v hb
def cl_7963 : CNF.NClause := [(57,false),(93,false),(102,false),(106,false),(110,false),(114,false),(122,false)]
theorem inp_7963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7963 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 26) (final_mem 26) cl_7963 (by decide) v hb
def cl_7964 : CNF.NClause := [(58,false),(93,false),(100,false),(107,false),(109,false),(116,false),(120,false)]
theorem inp_7964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7964 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 27) (final_mem 27) cl_7964 (by decide) v hb
def cl_7965 : CNF.NClause := [(59,false),(93,false),(101,false),(104,false),(112,false),(115,false),(121,false)]
theorem inp_7965 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7965 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 28) (final_mem 28) cl_7965 (by decide) v hb
def cl_7966 : CNF.NClause := [(60,false),(93,false),(99,false),(105,false),(111,false),(117,false),(119,false)]
theorem inp_7966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7966 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (finalGate5 29) (final_mem 29) cl_7966 (by decide) v hb
def cl_7969 : CNF.NClause := [(149,true),(150,true),(151,true),(152,true),(153,false),(154,true)]
theorem inp_7969 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7969 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 0 0) (closed_mem 0 0) cl_7969 (by decide) v hb
end Percolation.NReplay
