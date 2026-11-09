import NInputs168
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_10412 : CNF.NClause := [(528,true),(533,true),(538,true),(543,false),(548,true),(552,true)]
theorem inp_10412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10412 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 4) (closed_mem 13 4) cl_10412 (by decide) v hb
def cl_10413 : CNF.NClause := [(528,true),(533,true),(538,false),(543,true),(548,true),(552,true)]
theorem inp_10413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10413 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 4) (closed_mem 13 4) cl_10413 (by decide) v hb
def cl_10414 : CNF.NClause := [(528,true),(533,false),(538,true),(543,true),(548,true),(552,true)]
theorem inp_10414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10414 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 4) (closed_mem 13 4) cl_10414 (by decide) v hb
def cl_10415 : CNF.NClause := [(528,false),(533,true),(538,true),(543,true),(548,true),(552,true)]
theorem inp_10415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10415 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 4) (closed_mem 13 4) cl_10415 (by decide) v hb
def cl_10417 : CNF.NClause := [(547,true),(548,true),(549,true),(550,true),(551,false),(557,true)]
theorem inp_10417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10417 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 5) (closed_mem 13 5) cl_10417 (by decide) v hb
def cl_10418 : CNF.NClause := [(547,true),(548,true),(549,true),(550,false),(551,true),(557,true)]
theorem inp_10418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10418 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 5) (closed_mem 13 5) cl_10418 (by decide) v hb
def cl_10419 : CNF.NClause := [(547,true),(548,true),(549,false),(550,true),(551,true),(557,true)]
theorem inp_10419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10419 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 5) (closed_mem 13 5) cl_10419 (by decide) v hb
def cl_10420 : CNF.NClause := [(547,true),(548,false),(549,true),(550,true),(551,true),(557,true)]
theorem inp_10420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10420 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 5) (closed_mem 13 5) cl_10420 (by decide) v hb
def cl_10421 : CNF.NClause := [(547,false),(548,true),(549,true),(550,true),(551,true),(557,true)]
theorem inp_10421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10421 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 5) (closed_mem 13 5) cl_10421 (by decide) v hb
def cl_10426 : CNF.NClause := [(531,true),(535,false),(539,true),(543,true),(547,true),(556,true)]
theorem inp_10426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10426 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 6) (closed_mem 13 6) cl_10426 (by decide) v hb
def cl_10427 : CNF.NClause := [(531,false),(535,true),(539,true),(543,true),(547,true),(556,true)]
theorem inp_10427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10427 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 6) (closed_mem 13 6) cl_10427 (by decide) v hb
def cl_10429 : CNF.NClause := [(529,true),(536,true),(538,true),(545,true),(547,false),(554,true)]
theorem inp_10429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10429 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 7) (closed_mem 13 7) cl_10429 (by decide) v hb
def cl_10430 : CNF.NClause := [(529,true),(536,true),(538,true),(545,false),(547,true),(554,true)]
theorem inp_10430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10430 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 7) (closed_mem 13 7) cl_10430 (by decide) v hb
def cl_10432 : CNF.NClause := [(529,true),(536,false),(538,true),(545,true),(547,true),(554,true)]
theorem inp_10432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10432 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 7) (closed_mem 13 7) cl_10432 (by decide) v hb
def cl_10434 : CNF.NClause := [(530,true),(533,true),(541,true),(544,true),(547,true),(555,false)]
theorem inp_10434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10434 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 8) (closed_mem 13 8) cl_10434 (by decide) v hb
def cl_10436 : CNF.NClause := [(530,true),(533,true),(541,true),(544,false),(547,true),(555,true)]
theorem inp_10436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10436 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 8) (closed_mem 13 8) cl_10436 (by decide) v hb
def cl_10437 : CNF.NClause := [(530,true),(533,true),(541,false),(544,true),(547,true),(555,true)]
theorem inp_10437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10437 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 8) (closed_mem 13 8) cl_10437 (by decide) v hb
def cl_10439 : CNF.NClause := [(530,false),(533,true),(541,true),(544,true),(547,true),(555,true)]
theorem inp_10439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10439 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 8) (closed_mem 13 8) cl_10439 (by decide) v hb
def cl_10443 : CNF.NClause := [(528,true),(534,true),(540,false),(546,true),(547,true),(553,true)]
theorem inp_10443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10443 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 9) (closed_mem 13 9) cl_10443 (by decide) v hb
def cl_10448 : CNF.NClause := [(537,true),(538,true),(539,true),(540,false),(541,true),(557,true)]
theorem inp_10448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10448 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 10) (closed_mem 13 10) cl_10448 (by decide) v hb
def cl_10452 : CNF.NClause := [(531,true),(534,true),(537,true),(545,true),(548,true),(555,false)]
theorem inp_10452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10452 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 11) (closed_mem 13 11) cl_10452 (by decide) v hb
def cl_10453 : CNF.NClause := [(531,true),(534,true),(537,true),(545,true),(548,false),(555,true)]
theorem inp_10453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10453 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 11) (closed_mem 13 11) cl_10453 (by decide) v hb
def cl_10455 : CNF.NClause := [(531,true),(534,true),(537,false),(545,true),(548,true),(555,true)]
theorem inp_10455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10455 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 11) (closed_mem 13 11) cl_10455 (by decide) v hb
def cl_10456 : CNF.NClause := [(531,true),(534,false),(537,true),(545,true),(548,true),(555,true)]
theorem inp_10456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10456 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 11) (closed_mem 13 11) cl_10456 (by decide) v hb
def cl_10457 : CNF.NClause := [(531,false),(534,true),(537,true),(545,true),(548,true),(555,true)]
theorem inp_10457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10457 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 11) (closed_mem 13 11) cl_10457 (by decide) v hb
def cl_10459 : CNF.NClause := [(529,true),(533,true),(537,true),(546,true),(550,false),(556,true)]
theorem inp_10459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10459 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 12) (closed_mem 13 12) cl_10459 (by decide) v hb
def cl_10460 : CNF.NClause := [(529,true),(533,true),(537,true),(546,false),(550,true),(556,true)]
theorem inp_10460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10460 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 12) (closed_mem 13 12) cl_10460 (by decide) v hb
def cl_10461 : CNF.NClause := [(529,true),(533,true),(537,false),(546,true),(550,true),(556,true)]
theorem inp_10461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10461 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 12) (closed_mem 13 12) cl_10461 (by decide) v hb
def cl_10467 : CNF.NClause := [(530,true),(536,true),(537,false),(543,true),(549,true),(553,true)]
theorem inp_10467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10467 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 13) (closed_mem 13 13) cl_10467 (by decide) v hb
def cl_10469 : CNF.NClause := [(530,false),(536,true),(537,true),(543,true),(549,true),(553,true)]
theorem inp_10469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10469 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 13) (closed_mem 13 13) cl_10469 (by decide) v hb
def cl_10471 : CNF.NClause := [(528,true),(535,true),(537,true),(544,true),(551,false),(554,true)]
theorem inp_10471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10471 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 14) (closed_mem 13 14) cl_10471 (by decide) v hb
def cl_10472 : CNF.NClause := [(528,true),(535,true),(537,true),(544,false),(551,true),(554,true)]
theorem inp_10472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10472 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 14) (closed_mem 13 14) cl_10472 (by decide) v hb
def cl_10474 : CNF.NClause := [(528,true),(535,false),(537,true),(544,true),(551,true),(554,true)]
theorem inp_10474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10474 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 14) (closed_mem 13 14) cl_10474 (by decide) v hb
def cl_10478 : CNF.NClause := [(542,true),(543,true),(544,true),(545,false),(546,true),(557,true)]
theorem inp_10478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10478 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 15) (closed_mem 13 15) cl_10478 (by decide) v hb
def cl_10479 : CNF.NClause := [(542,true),(543,true),(544,false),(545,true),(546,true),(557,true)]
theorem inp_10479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10479 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 15) (closed_mem 13 15) cl_10479 (by decide) v hb
def cl_10480 : CNF.NClause := [(542,true),(543,false),(544,true),(545,true),(546,true),(557,true)]
theorem inp_10480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10480 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 15) (closed_mem 13 15) cl_10480 (by decide) v hb
def cl_10481 : CNF.NClause := [(542,false),(543,true),(544,true),(545,true),(546,true),(557,true)]
theorem inp_10481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10481 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 15) (closed_mem 13 15) cl_10481 (by decide) v hb
def cl_10485 : CNF.NClause := [(531,true),(533,true),(540,false),(542,true),(549,true),(554,true)]
theorem inp_10485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10485 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 16) (closed_mem 13 16) cl_10485 (by decide) v hb
def cl_10489 : CNF.NClause := [(529,true),(535,true),(541,true),(542,true),(548,false),(553,true)]
theorem inp_10489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10489 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 17) (closed_mem 13 17) cl_10489 (by decide) v hb
def cl_10490 : CNF.NClause := [(529,true),(535,true),(541,true),(542,false),(548,true),(553,true)]
theorem inp_10490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10490 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 17) (closed_mem 13 17) cl_10490 (by decide) v hb
def cl_10494 : CNF.NClause := [(530,true),(534,true),(538,true),(542,true),(551,true),(556,false)]
theorem inp_10494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10494 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 18) (closed_mem 13 18) cl_10494 (by decide) v hb
def cl_10496 : CNF.NClause := [(530,true),(534,true),(538,true),(542,false),(551,true),(556,true)]
theorem inp_10496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10496 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 18) (closed_mem 13 18) cl_10496 (by decide) v hb
def cl_10497 : CNF.NClause := [(530,true),(534,true),(538,false),(542,true),(551,true),(556,true)]
theorem inp_10497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10497 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 18) (closed_mem 13 18) cl_10497 (by decide) v hb
def cl_10500 : CNF.NClause := [(528,true),(536,true),(539,true),(542,true),(550,true),(555,false)]
theorem inp_10500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10500 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 19) (closed_mem 13 19) cl_10500 (by decide) v hb
def cl_10501 : CNF.NClause := [(528,true),(536,true),(539,true),(542,true),(550,false),(555,true)]
theorem inp_10501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10501 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 19) (closed_mem 13 19) cl_10501 (by decide) v hb
def cl_10503 : CNF.NClause := [(528,true),(536,true),(539,false),(542,true),(550,true),(555,true)]
theorem inp_10503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10503 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 19) (closed_mem 13 19) cl_10503 (by decide) v hb
def cl_10505 : CNF.NClause := [(528,false),(536,true),(539,true),(542,true),(550,true),(555,true)]
theorem inp_10505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10505 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 19) (closed_mem 13 19) cl_10505 (by decide) v hb
def cl_10507 : CNF.NClause := [(532,true),(533,true),(534,true),(535,true),(536,false),(557,true)]
theorem inp_10507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10507 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 20) (closed_mem 13 20) cl_10507 (by decide) v hb
def cl_10508 : CNF.NClause := [(532,true),(533,true),(534,true),(535,false),(536,true),(557,true)]
theorem inp_10508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10508 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 20) (closed_mem 13 20) cl_10508 (by decide) v hb
def cl_10510 : CNF.NClause := [(532,true),(533,false),(534,true),(535,true),(536,true),(557,true)]
theorem inp_10510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10510 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 13 20) (closed_mem 13 20) cl_10510 (by decide) v hb
end Percolation.NReplay
