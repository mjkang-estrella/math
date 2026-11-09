import NInputs173
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_10842 : CNF.NClause := [(590,true),(597,true),(599,true),(606,true),(613,true),(616,false)]
theorem inp_10842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10842 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 14) (closed_mem 15 14) cl_10842 (by decide) v hb
def cl_10843 : CNF.NClause := [(590,true),(597,true),(599,true),(606,true),(613,false),(616,true)]
theorem inp_10843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10843 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 14) (closed_mem 15 14) cl_10843 (by decide) v hb
def cl_10844 : CNF.NClause := [(590,true),(597,true),(599,true),(606,false),(613,true),(616,true)]
theorem inp_10844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10844 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 14) (closed_mem 15 14) cl_10844 (by decide) v hb
def cl_10845 : CNF.NClause := [(590,true),(597,true),(599,false),(606,true),(613,true),(616,true)]
theorem inp_10845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10845 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 14) (closed_mem 15 14) cl_10845 (by decide) v hb
def cl_10853 : CNF.NClause := [(604,false),(605,true),(606,true),(607,true),(608,true),(619,true)]
theorem inp_10853 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10853 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 15) (closed_mem 15 15) cl_10853 (by decide) v hb
def cl_10856 : CNF.NClause := [(593,true),(595,true),(602,true),(604,false),(611,true),(616,true)]
theorem inp_10856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10856 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 16) (closed_mem 15 16) cl_10856 (by decide) v hb
def cl_10862 : CNF.NClause := [(591,true),(597,true),(603,true),(604,false),(610,true),(615,true)]
theorem inp_10862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10862 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 17) (closed_mem 15 17) cl_10862 (by decide) v hb
def cl_10868 : CNF.NClause := [(592,true),(596,true),(600,true),(604,false),(613,true),(618,true)]
theorem inp_10868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10868 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 18) (closed_mem 15 18) cl_10868 (by decide) v hb
def cl_10874 : CNF.NClause := [(590,true),(598,true),(601,true),(604,false),(612,true),(617,true)]
theorem inp_10874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10874 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 19) (closed_mem 15 19) cl_10874 (by decide) v hb
def cl_10880 : CNF.NClause := [(594,true),(595,true),(596,true),(597,false),(598,true),(619,true)]
theorem inp_10880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10880 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 20) (closed_mem 15 20) cl_10880 (by decide) v hb
def cl_10881 : CNF.NClause := [(594,true),(595,true),(596,false),(597,true),(598,true),(619,true)]
theorem inp_10881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10881 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 20) (closed_mem 15 20) cl_10881 (by decide) v hb
def cl_10883 : CNF.NClause := [(594,false),(595,true),(596,true),(597,true),(598,true),(619,true)]
theorem inp_10883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10883 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 20) (closed_mem 15 20) cl_10883 (by decide) v hb
def cl_10885 : CNF.NClause := [(593,true),(594,true),(600,true),(606,true),(612,false),(615,true)]
theorem inp_10885 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10885 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 21) (closed_mem 15 21) cl_10885 (by decide) v hb
def cl_10887 : CNF.NClause := [(593,true),(594,true),(600,false),(606,true),(612,true),(615,true)]
theorem inp_10887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10887 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 21) (closed_mem 15 21) cl_10887 (by decide) v hb
def cl_10890 : CNF.NClause := [(591,true),(594,true),(602,true),(605,true),(613,true),(617,false)]
theorem inp_10890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10890 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 22) (closed_mem 15 22) cl_10890 (by decide) v hb
def cl_10895 : CNF.NClause := [(591,false),(594,true),(602,true),(605,true),(613,true),(617,true)]
theorem inp_10895 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10895 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 22) (closed_mem 15 22) cl_10895 (by decide) v hb
def cl_10896 : CNF.NClause := [(592,true),(594,true),(601,true),(608,true),(610,true),(616,false)]
theorem inp_10896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10896 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 23) (closed_mem 15 23) cl_10896 (by decide) v hb
def cl_10897 : CNF.NClause := [(592,true),(594,true),(601,true),(608,true),(610,false),(616,true)]
theorem inp_10897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10897 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 23) (closed_mem 15 23) cl_10897 (by decide) v hb
def cl_10898 : CNF.NClause := [(592,true),(594,true),(601,true),(608,false),(610,true),(616,true)]
theorem inp_10898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10898 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 23) (closed_mem 15 23) cl_10898 (by decide) v hb
def cl_10900 : CNF.NClause := [(592,true),(594,false),(601,true),(608,true),(610,true),(616,true)]
theorem inp_10900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10900 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 23) (closed_mem 15 23) cl_10900 (by decide) v hb
def cl_10902 : CNF.NClause := [(590,true),(594,true),(603,true),(607,true),(611,true),(618,false)]
theorem inp_10902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10902 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 24) (closed_mem 15 24) cl_10902 (by decide) v hb
def cl_10907 : CNF.NClause := [(590,false),(594,true),(603,true),(607,true),(611,true),(618,true)]
theorem inp_10907 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10907 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 24) (closed_mem 15 24) cl_10907 (by decide) v hb
def cl_10909 : CNF.NClause := [(589,true),(590,true),(591,true),(592,true),(593,false),(619,true)]
theorem inp_10909 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10909 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 25) (closed_mem 15 25) cl_10909 (by decide) v hb
def cl_10910 : CNF.NClause := [(589,true),(590,true),(591,true),(592,false),(593,true),(619,true)]
theorem inp_10910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10910 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 25) (closed_mem 15 25) cl_10910 (by decide) v hb
def cl_10911 : CNF.NClause := [(589,true),(590,true),(591,false),(592,true),(593,true),(619,true)]
theorem inp_10911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10911 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 25) (closed_mem 15 25) cl_10911 (by decide) v hb
def cl_10912 : CNF.NClause := [(589,true),(590,false),(591,true),(592,true),(593,true),(619,true)]
theorem inp_10912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10912 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 25) (closed_mem 15 25) cl_10912 (by decide) v hb
def cl_10914 : CNF.NClause := [(589,true),(598,true),(602,true),(606,true),(610,true),(618,false)]
theorem inp_10914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10914 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 26) (closed_mem 15 26) cl_10914 (by decide) v hb
def cl_10915 : CNF.NClause := [(589,true),(598,true),(602,true),(606,true),(610,false),(618,true)]
theorem inp_10915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10915 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 26) (closed_mem 15 26) cl_10915 (by decide) v hb
def cl_10916 : CNF.NClause := [(589,true),(598,true),(602,true),(606,false),(610,true),(618,true)]
theorem inp_10916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10916 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 26) (closed_mem 15 26) cl_10916 (by decide) v hb
def cl_10917 : CNF.NClause := [(589,true),(598,true),(602,false),(606,true),(610,true),(618,true)]
theorem inp_10917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10917 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 26) (closed_mem 15 26) cl_10917 (by decide) v hb
def cl_10918 : CNF.NClause := [(589,true),(598,false),(602,true),(606,true),(610,true),(618,true)]
theorem inp_10918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10918 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 26) (closed_mem 15 26) cl_10918 (by decide) v hb
def cl_10920 : CNF.NClause := [(589,true),(596,true),(603,true),(605,true),(612,true),(616,false)]
theorem inp_10920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10920 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 27) (closed_mem 15 27) cl_10920 (by decide) v hb
def cl_10921 : CNF.NClause := [(589,true),(596,true),(603,true),(605,true),(612,false),(616,true)]
theorem inp_10921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10921 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 27) (closed_mem 15 27) cl_10921 (by decide) v hb
def cl_10924 : CNF.NClause := [(589,true),(596,false),(603,true),(605,true),(612,true),(616,true)]
theorem inp_10924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10924 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 27) (closed_mem 15 27) cl_10924 (by decide) v hb
def cl_10927 : CNF.NClause := [(589,true),(597,true),(600,true),(608,true),(611,false),(617,true)]
theorem inp_10927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10927 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 28) (closed_mem 15 28) cl_10927 (by decide) v hb
def cl_10928 : CNF.NClause := [(589,true),(597,true),(600,true),(608,false),(611,true),(617,true)]
theorem inp_10928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10928 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 28) (closed_mem 15 28) cl_10928 (by decide) v hb
def cl_10930 : CNF.NClause := [(589,true),(597,false),(600,true),(608,true),(611,true),(617,true)]
theorem inp_10930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10930 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 28) (closed_mem 15 28) cl_10930 (by decide) v hb
def cl_10932 : CNF.NClause := [(589,true),(595,true),(601,true),(607,true),(613,true),(615,false)]
theorem inp_10932 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10932 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 29) (closed_mem 15 29) cl_10932 (by decide) v hb
def cl_10933 : CNF.NClause := [(589,true),(595,true),(601,true),(607,true),(613,false),(615,true)]
theorem inp_10933 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10933 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 29) (closed_mem 15 29) cl_10933 (by decide) v hb
def cl_10934 : CNF.NClause := [(589,true),(595,true),(601,true),(607,false),(613,true),(615,true)]
theorem inp_10934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10934 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 29) (closed_mem 15 29) cl_10934 (by decide) v hb
def cl_10935 : CNF.NClause := [(589,true),(595,true),(601,false),(607,true),(613,true),(615,true)]
theorem inp_10935 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10935 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 29) (closed_mem 15 29) cl_10935 (by decide) v hb
def cl_10936 : CNF.NClause := [(589,true),(595,false),(601,true),(607,true),(613,true),(615,true)]
theorem inp_10936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10936 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 29) (closed_mem 15 29) cl_10936 (by decide) v hb
def cl_10940 : CNF.NClause := [(589,true),(594,true),(599,true),(604,false),(609,true),(614,true)]
theorem inp_10940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10940 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 15 30) (closed_mem 15 30) cl_10940 (by decide) v hb
def cl_10945 : CNF.NClause := [(645,true),(646,true),(647,true),(648,true),(649,false),(650,true)]
theorem inp_10945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10945 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 0) (closed_mem 16 0) cl_10945 (by decide) v hb
def cl_10946 : CNF.NClause := [(645,true),(646,true),(647,true),(648,false),(649,true),(650,true)]
theorem inp_10946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10946 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 0) (closed_mem 16 0) cl_10946 (by decide) v hb
def cl_10947 : CNF.NClause := [(645,true),(646,true),(647,false),(648,true),(649,true),(650,true)]
theorem inp_10947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10947 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 0) (closed_mem 16 0) cl_10947 (by decide) v hb
def cl_10948 : CNF.NClause := [(645,true),(646,false),(647,true),(648,true),(649,true),(650,true)]
theorem inp_10948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10948 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 0) (closed_mem 16 0) cl_10948 (by decide) v hb
def cl_10951 : CNF.NClause := [(624,true),(629,true),(634,true),(639,true),(644,false),(645,true)]
theorem inp_10951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10951 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 1) (closed_mem 16 1) cl_10951 (by decide) v hb
def cl_10952 : CNF.NClause := [(624,true),(629,true),(634,true),(639,false),(644,true),(645,true)]
theorem inp_10952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10952 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 1) (closed_mem 16 1) cl_10952 (by decide) v hb
def cl_10953 : CNF.NClause := [(624,true),(629,true),(634,false),(639,true),(644,true),(645,true)]
theorem inp_10953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10953 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 16 1) (closed_mem 16 1) cl_10953 (by decide) v hb
end Percolation.NReplay
