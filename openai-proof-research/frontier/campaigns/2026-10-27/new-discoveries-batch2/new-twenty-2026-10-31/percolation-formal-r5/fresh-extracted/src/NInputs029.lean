import NInputs028
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_1990 : CNF.NClause := [(93,true),(56,true),(57,false),(58,true),(59,false),(60,false),(61,false)]
theorem inp_1990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1990 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_1990 (by decide) v hb
def cl_1991 : CNF.NClause := [(93,true),(56,false),(57,true),(58,true),(59,false),(60,false),(61,false)]
theorem inp_1991 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1991 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_1991 (by decide) v hb
def cl_1992 : CNF.NClause := [(93,true),(56,true),(57,true),(58,true),(59,false),(60,false),(61,false)]
theorem inp_1992 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1992 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_1992 (by decide) v hb
def cl_1993 : CNF.NClause := [(93,true),(56,false),(57,false),(58,false),(59,true),(60,false),(61,false)]
theorem inp_1993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1993 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_1993 (by decide) v hb
def cl_1994 : CNF.NClause := [(93,true),(56,true),(57,false),(58,false),(59,true),(60,false),(61,false)]
theorem inp_1994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1994 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_1994 (by decide) v hb
def cl_1995 : CNF.NClause := [(93,true),(56,false),(57,true),(58,false),(59,true),(60,false),(61,false)]
theorem inp_1995 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1995 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_1995 (by decide) v hb
def cl_1996 : CNF.NClause := [(93,true),(56,true),(57,true),(58,false),(59,true),(60,false),(61,false)]
theorem inp_1996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1996 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_1996 (by decide) v hb
def cl_1997 : CNF.NClause := [(93,true),(56,false),(57,false),(58,true),(59,true),(60,false),(61,false)]
theorem inp_1997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1997 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_1997 (by decide) v hb
def cl_1998 : CNF.NClause := [(93,true),(56,true),(57,false),(58,true),(59,true),(60,false),(61,false)]
theorem inp_1998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1998 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_1998 (by decide) v hb
def cl_1999 : CNF.NClause := [(93,true),(56,false),(57,true),(58,true),(59,true),(60,false),(61,false)]
theorem inp_1999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1999 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_1999 (by decide) v hb
def cl_2000 : CNF.NClause := [(93,true),(56,true),(57,true),(58,true),(59,true),(60,false),(61,false)]
theorem inp_2000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2000 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2000 (by decide) v hb
def cl_2001 : CNF.NClause := [(93,true),(56,false),(57,false),(58,false),(59,false),(60,true),(61,false)]
theorem inp_2001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2001 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2001 (by decide) v hb
def cl_2002 : CNF.NClause := [(93,true),(56,true),(57,false),(58,false),(59,false),(60,true),(61,false)]
theorem inp_2002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2002 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2002 (by decide) v hb
def cl_2004 : CNF.NClause := [(93,true),(56,true),(57,true),(58,false),(59,false),(60,true),(61,false)]
theorem inp_2004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2004 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2004 (by decide) v hb
def cl_2005 : CNF.NClause := [(93,true),(56,false),(57,false),(58,true),(59,false),(60,true),(61,false)]
theorem inp_2005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2005 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2005 (by decide) v hb
def cl_2006 : CNF.NClause := [(93,true),(56,true),(57,false),(58,true),(59,false),(60,true),(61,false)]
theorem inp_2006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2006 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2006 (by decide) v hb
def cl_2009 : CNF.NClause := [(93,true),(56,false),(57,false),(58,false),(59,true),(60,true),(61,false)]
theorem inp_2009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2009 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2009 (by decide) v hb
def cl_2010 : CNF.NClause := [(93,true),(56,true),(57,false),(58,false),(59,true),(60,true),(61,false)]
theorem inp_2010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2010 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2010 (by decide) v hb
def cl_2013 : CNF.NClause := [(93,true),(56,false),(57,false),(58,true),(59,true),(60,true),(61,false)]
theorem inp_2013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2013 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2013 (by decide) v hb
def cl_2014 : CNF.NClause := [(93,true),(56,true),(57,false),(58,true),(59,true),(60,true),(61,false)]
theorem inp_2014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2014 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2014 (by decide) v hb
def cl_2016 : CNF.NClause := [(93,false),(56,true),(57,true),(58,true),(59,true),(60,true),(61,false)]
theorem inp_2016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2016 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2016 (by decide) v hb
def cl_2017 : CNF.NClause := [(93,true),(56,false),(57,false),(58,false),(59,false),(60,false),(61,true)]
theorem inp_2017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2017 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2017 (by decide) v hb
def cl_2018 : CNF.NClause := [(93,true),(56,true),(57,false),(58,false),(59,false),(60,false),(61,true)]
theorem inp_2018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2018 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2018 (by decide) v hb
def cl_2019 : CNF.NClause := [(93,true),(56,false),(57,true),(58,false),(59,false),(60,false),(61,true)]
theorem inp_2019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2019 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2019 (by decide) v hb
def cl_2020 : CNF.NClause := [(93,true),(56,true),(57,true),(58,false),(59,false),(60,false),(61,true)]
theorem inp_2020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2020 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2020 (by decide) v hb
def cl_2021 : CNF.NClause := [(93,true),(56,false),(57,false),(58,true),(59,false),(60,false),(61,true)]
theorem inp_2021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2021 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2021 (by decide) v hb
def cl_2022 : CNF.NClause := [(93,true),(56,true),(57,false),(58,true),(59,false),(60,false),(61,true)]
theorem inp_2022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2022 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2022 (by decide) v hb
def cl_2023 : CNF.NClause := [(93,true),(56,false),(57,true),(58,true),(59,false),(60,false),(61,true)]
theorem inp_2023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2023 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2023 (by decide) v hb
def cl_2024 : CNF.NClause := [(93,true),(56,true),(57,true),(58,true),(59,false),(60,false),(61,true)]
theorem inp_2024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2024 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2024 (by decide) v hb
def cl_2025 : CNF.NClause := [(93,true),(56,false),(57,false),(58,false),(59,true),(60,false),(61,true)]
theorem inp_2025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2025 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2025 (by decide) v hb
def cl_2026 : CNF.NClause := [(93,true),(56,true),(57,false),(58,false),(59,true),(60,false),(61,true)]
theorem inp_2026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2026 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2026 (by decide) v hb
def cl_2027 : CNF.NClause := [(93,true),(56,false),(57,true),(58,false),(59,true),(60,false),(61,true)]
theorem inp_2027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2027 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2027 v hb
def cl_2028 : CNF.NClause := [(93,true),(56,true),(57,true),(58,false),(59,true),(60,false),(61,true)]
theorem inp_2028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2028 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2028 (by decide) v hb
def cl_2029 : CNF.NClause := [(93,true),(56,false),(57,false),(58,true),(59,true),(60,false),(61,true)]
theorem inp_2029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2029 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2029 v hb
def cl_2030 : CNF.NClause := [(93,true),(56,true),(57,false),(58,true),(59,true),(60,false),(61,true)]
theorem inp_2030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2030 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2030 (by decide) v hb
def cl_2032 : CNF.NClause := [(93,false),(56,true),(57,true),(58,true),(59,true),(60,false),(61,true)]
theorem inp_2032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2032 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2032 (by decide) v hb
def cl_2033 : CNF.NClause := [(93,true),(56,false),(57,false),(58,false),(59,false),(60,true),(61,true)]
theorem inp_2033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2033 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2033 (by decide) v hb
def cl_2034 : CNF.NClause := [(93,true),(56,true),(57,false),(58,false),(59,false),(60,true),(61,true)]
theorem inp_2034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2034 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2034 (by decide) v hb
def cl_2036 : CNF.NClause := [(93,true),(56,true),(57,true),(58,false),(59,false),(60,true),(61,true)]
theorem inp_2036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2036 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2036 (by decide) v hb
def cl_2037 : CNF.NClause := [(93,true),(56,false),(57,false),(58,true),(59,false),(60,true),(61,true)]
theorem inp_2037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2037 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2037 (by decide) v hb
def cl_2038 : CNF.NClause := [(93,true),(56,true),(57,false),(58,true),(59,false),(60,true),(61,true)]
theorem inp_2038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2038 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2038 (by decide) v hb
def cl_2040 : CNF.NClause := [(93,false),(56,true),(57,true),(58,true),(59,false),(60,true),(61,true)]
theorem inp_2040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2040 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2040 (by decide) v hb
def cl_2041 : CNF.NClause := [(93,true),(56,false),(57,false),(58,false),(59,true),(60,true),(61,true)]
theorem inp_2041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2041 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2041 (by decide) v hb
def cl_2042 : CNF.NClause := [(93,true),(56,true),(57,false),(58,false),(59,true),(60,true),(61,true)]
theorem inp_2042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2042 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2042 (by decide) v hb
def cl_2044 : CNF.NClause := [(93,false),(56,true),(57,true),(58,false),(59,true),(60,true),(61,true)]
theorem inp_2044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2044 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2044 (by decide) v hb
def cl_2046 : CNF.NClause := [(93,false),(56,true),(57,false),(58,true),(59,true),(60,true),(61,true)]
theorem inp_2046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2046 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2046 (by decide) v hb
def cl_2048 : CNF.NClause := [(93,false),(56,true),(57,true),(58,true),(59,true),(60,true),(61,true)]
theorem inp_2048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2048 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) cl_2048 (by decide) v hb
def cl_2049 : CNF.NClause := [(94,true),(35,false),(40,false),(45,false),(50,false),(55,false),(56,false)]
theorem inp_2049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2049 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2049 v hb
def cl_2050 : CNF.NClause := [(94,true),(35,true),(40,false),(45,false),(50,false),(55,false),(56,false)]
theorem inp_2050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2050 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_2050 v hb
def cl_2051 : CNF.NClause := [(94,true),(35,false),(40,true),(45,false),(50,false),(55,false),(56,false)]
theorem inp_2051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2051 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 1) 1) (activationX_mem 1) cl_2051 (by decide) v hb
end Percolation.NReplay
