import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause3600 : CNF.NClause := [(118,true),(31,true),(32,true),(33,true),(34,true),(35,false),(61,false)]
theorem inputList3600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3600 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3600 (by decide) v hb
mask_input "3600|2305843043573432320|332306998946228968225951797282340864"
def inputClause3601 : CNF.NClause := [(118,true),(31,false),(32,false),(33,false),(34,false),(35,true),(61,false)]
theorem inputList3601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3601 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3601 (by decide) v hb
mask_input "3601|2305843041425948672|332306998946228968225951799429824512"
def inputClause3602 : CNF.NClause := [(118,true),(31,true),(32,false),(33,false),(34,false),(35,true),(61,false)]
theorem inputList3602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3602 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3602 (by decide) v hb
mask_input "3602|2305843039278465024|332306998946228968225951801577308160"
def inputClause3603 : CNF.NClause := [(118,true),(31,false),(32,true),(33,false),(34,false),(35,true),(61,false)]
theorem inputList3603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3603 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3603 (by decide) v hb
mask_input "3603|2305843037130981376|332306998946228968225951803724791808"
def inputClause3604 : CNF.NClause := [(118,true),(31,true),(32,true),(33,false),(34,false),(35,true),(61,false)]
theorem inputList3604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3604 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3604 (by decide) v hb
mask_input "3604|2305843034983497728|332306998946228968225951805872275456"
def inputClause3605 : CNF.NClause := [(118,true),(31,false),(32,false),(33,true),(34,false),(35,true),(61,false)]
theorem inputList3605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3605 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3605 (by decide) v hb
mask_input "3605|2305843032836014080|332306998946228968225951808019759104"
def inputClause3606 : CNF.NClause := [(118,true),(31,true),(32,false),(33,true),(34,false),(35,true),(61,false)]
theorem inputList3606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3606 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3606 (by decide) v hb
mask_input "3606|2305843030688530432|332306998946228968225951810167242752"
def inputClause3607 : CNF.NClause := [(118,true),(31,false),(32,true),(33,true),(34,false),(35,true),(61,false)]
theorem inputList3607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3607 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3607 (by decide) v hb
mask_input "3607|2305843028541046784|332306998946228968225951812314726400"
def inputClause3608 : CNF.NClause := [(118,true),(31,true),(32,true),(33,true),(34,false),(35,true),(61,false)]
theorem inputList3608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3608 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3608 (by decide) v hb
mask_input "3608|2305843026393563136|332306998946228968225951814462210048"
def inputClause3609 : CNF.NClause := [(118,true),(31,false),(32,false),(33,false),(34,true),(35,true),(61,false)]
theorem inputList3609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3609 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3609 (by decide) v hb
mask_input "3609|2305843024246079488|332306998946228968225951816609693696"
def inputClause3610 : CNF.NClause := [(118,true),(31,true),(32,false),(33,false),(34,true),(35,true),(61,false)]
theorem inputList3610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3610 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3610 (by decide) v hb
mask_input "3610|2305843022098595840|332306998946228968225951818757177344"
def inputClause3613 : CNF.NClause := [(118,true),(31,false),(32,false),(33,true),(34,true),(35,true),(61,false)]
theorem inputList3613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3613 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3613 (by decide) v hb
mask_input "3613|2305843015656144896|332306998946228968225951825199628288"
def inputClause3614 : CNF.NClause := [(118,true),(31,true),(32,false),(33,true),(34,true),(35,true),(61,false)]
theorem inputList3614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3614 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3614 (by decide) v hb
mask_input "3614|2305843013508661248|332306998946228968225951827347111936"
def inputClause3615 : CNF.NClause := [(118,true),(31,false),(32,true),(33,true),(34,true),(35,true),(61,false)]
theorem inputList3615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3615 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3615 (by decide) v hb
mask_input "3615|2305843011361177600|332306998946228968225951829494595584"
def inputClause3616 : CNF.NClause := [(118,false),(31,true),(32,true),(33,true),(34,true),(35,true),(61,false)]
theorem inputList3616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3616 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3616 (by decide) v hb
mask_input "3616|332306998946228970531794774283780096|66571993088"
def inputClause3618 : CNF.NClause := [(118,true),(31,true),(32,false),(33,false),(34,false),(35,false),(61,true)]
theorem inputList3618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3618 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3618 (by decide) v hb
mask_input "3618|64424509440|332306998946228970531794776431263744"
def inputClause3620 : CNF.NClause := [(118,true),(31,true),(32,true),(33,false),(34,false),(35,false),(61,true)]
theorem inputList3620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3620 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3620 (by decide) v hb
mask_input "3620|60129542144|332306998946228970531794780726231040"
def inputClause3621 : CNF.NClause := [(118,true),(31,false),(32,false),(33,true),(34,false),(35,false),(61,true)]
theorem inputList3621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3621 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3621 (by decide) v hb
mask_input "3621|57982058496|332306998946228970531794782873714688"
def inputClause3622 : CNF.NClause := [(118,true),(31,true),(32,false),(33,true),(34,false),(35,false),(61,true)]
theorem inputList3622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3622 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3622 (by decide) v hb
mask_input "3622|55834574848|332306998946228970531794785021198336"
def inputClause3623 : CNF.NClause := [(118,true),(31,false),(32,true),(33,true),(34,false),(35,false),(61,true)]
theorem inputList3623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3623 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3623 (by decide) v hb
mask_input "3623|53687091200|332306998946228970531794787168681984"
def inputClause3624 : CNF.NClause := [(118,true),(31,true),(32,true),(33,true),(34,false),(35,false),(61,true)]
theorem inputList3624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3624 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3624 (by decide) v hb
mask_input "3624|51539607552|332306998946228970531794789316165632"
def inputClause3625 : CNF.NClause := [(118,true),(31,false),(32,false),(33,false),(34,true),(35,false),(61,true)]
theorem inputList3625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3625 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3625 (by decide) v hb
mask_input "3625|49392123904|332306998946228970531794791463649280"
def inputClause3626 : CNF.NClause := [(118,true),(31,true),(32,false),(33,false),(34,true),(35,false),(61,true)]
theorem inputList3626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3626 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3626 (by decide) v hb
mask_input "3626|47244640256|332306998946228970531794793611132928"
def inputClause3627 : CNF.NClause := [(118,true),(31,false),(32,true),(33,false),(34,true),(35,false),(61,true)]
theorem inputList3627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3627 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3627 (by decide) v hb
mask_input "3627|45097156608|332306998946228970531794795758616576"
def inputClause3628 : CNF.NClause := [(118,true),(31,true),(32,true),(33,false),(34,true),(35,false),(61,true)]
theorem inputList3628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3628 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3628 (by decide) v hb
mask_input "3628|42949672960|332306998946228970531794797906100224"
def inputClause3629 : CNF.NClause := [(118,true),(31,false),(32,false),(33,true),(34,true),(35,false),(61,true)]
theorem inputList3629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3629 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3629 (by decide) v hb
mask_input "3629|40802189312|332306998946228970531794800053583872"
def inputClause3630 : CNF.NClause := [(118,true),(31,true),(32,false),(33,true),(34,true),(35,false),(61,true)]
theorem inputList3630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3630 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3630 (by decide) v hb
mask_input "3630|38654705664|332306998946228970531794802201067520"
def inputClause3634 : CNF.NClause := [(118,true),(31,true),(32,false),(33,false),(34,false),(35,true),(61,true)]
theorem inputList3634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3634 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3634 (by decide) v hb
mask_input "3634|30064771072|332306998946228970531794810791002112"
def inputClause3636 : CNF.NClause := [(118,true),(31,true),(32,true),(33,false),(34,false),(35,true),(61,true)]
theorem inputList3636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3636 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3636 (by decide) v hb
mask_input "3636|25769803776|332306998946228970531794815085969408"
def inputClause3637 : CNF.NClause := [(118,true),(31,false),(32,false),(33,true),(34,false),(35,true),(61,true)]
theorem inputList3637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3637 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3637 (by decide) v hb
mask_input "3637|23622320128|332306998946228970531794817233453056"
def inputClause3638 : CNF.NClause := [(118,true),(31,true),(32,false),(33,true),(34,false),(35,true),(61,true)]
theorem inputList3638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3638 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3638 (by decide) v hb
mask_input "3638|21474836480|332306998946228970531794819380936704"
def inputClause3641 : CNF.NClause := [(118,true),(31,false),(32,false),(33,false),(34,true),(35,true),(61,true)]
theorem inputList3641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3641 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3641 (by decide) v hb
mask_input "3641|15032385536|332306998946228970531794825823387648"
def inputClause3642 : CNF.NClause := [(118,true),(31,true),(32,false),(33,false),(34,true),(35,true),(61,true)]
theorem inputList3642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3642 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3642 (by decide) v hb
mask_input "3642|12884901888|332306998946228970531794827970871296"
def inputClause3645 : CNF.NClause := [(118,true),(31,false),(32,false),(33,true),(34,true),(35,true),(61,true)]
theorem inputList3645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3645 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3645 (by decide) v hb
mask_input "3645|6442450944|332306998946228970531794834413322240"
def inputClause3648 : CNF.NClause := [(118,false),(31,true),(32,true),(33,true),(34,true),(35,true),(61,true)]
theorem inputList3648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3648 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3648 (by decide) v hb
mask_input "3648|332306998946228968225951765070086144|2305843075785687040"
def inputClause3649 : CNF.NClause := [(119,true),(31,false),(40,false),(44,false),(48,false),(52,false),(60,false)]
theorem inputList3649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3649 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3649 (by decide) v hb
mask_input "3649|1157725273056083968|664613997892457936451903530140172288"
def inputClause3650 : CNF.NClause := [(119,true),(31,true),(40,false),(44,false),(48,false),(52,false),(60,false)]
theorem inputList3650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3650 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3650 (by decide) v hb
mask_input "3650|1157725270908600320|664613997892457936451903532287655936"
def inputClause3651 : CNF.NClause := [(119,true),(31,false),(40,true),(44,false),(48,false),(52,false),(60,false)]
theorem inputList3651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3651 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3651 (by decide) v hb
mask_input "3651|1157724173544456192|664613997892457936451904629651800064"
def inputClause3652 : CNF.NClause := [(119,true),(31,true),(40,true),(44,false),(48,false),(52,false),(60,false)]
theorem inputList3652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3652 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3652 (by decide) v hb
mask_input "3652|1157724171396972544|664613997892457936451904631799283712"
def inputClause3653 : CNF.NClause := [(119,true),(31,false),(40,false),(44,true),(48,false),(52,false),(60,false)]
theorem inputList3653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3653 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3653 (by decide) v hb
mask_input "3653|1157707680870039552|664613997892457936451921122326216704"
end Percolation.MaskChain
