import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause2507 : CNF.NClause := [(101,true),(34,false),(37,true),(45,false),(48,true),(51,false),(59,false)]
theorem inputList2507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2507 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2507 (by decide) v hb
mask_input "2507|578747753669066752|2535301200456459084605822074880"
def inputClause2508 : CNF.NClause := [(101,true),(34,true),(37,true),(45,false),(48,true),(51,false),(59,false)]
theorem inputList2508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2508 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2508 (by decide) v hb
mask_input "2508|578747736489197568|2535301200456459084623001944064"
def inputClause2509 : CNF.NClause := [(101,true),(34,false),(37,false),(45,true),(48,true),(51,false),(59,false)]
theorem inputList2509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2509 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2509 (by decide) v hb
mask_input "2509|578712706735931392|2535301200456459119652755210240"
def inputClause2510 : CNF.NClause := [(101,true),(34,true),(37,false),(45,true),(48,true),(51,false),(59,false)]
theorem inputList2510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2510 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2510 (by decide) v hb
mask_input "2510|578712689556062208|2535301200456459119669935079424"
def inputClause2511 : CNF.NClause := [(101,true),(34,false),(37,true),(45,true),(48,true),(51,false),(59,false)]
theorem inputList2511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2511 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2511 (by decide) v hb
mask_input "2511|578712569296977920|2535301200456459119790194163712"
def inputClause2512 : CNF.NClause := [(101,true),(34,true),(37,true),(45,true),(48,true),(51,false),(59,false)]
theorem inputList2512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2512 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2512 (by decide) v hb
mask_input "2512|578712552117108736|2535301200456459119807374032896"
def inputClause2513 : CNF.NClause := [(101,true),(34,false),(37,false),(45,false),(48,false),(51,true),(59,false)]
theorem inputList2513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2513 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2513 (by decide) v hb
mask_input "2513|576777566271045632|2535301200456461054793220096000"
def inputClause2514 : CNF.NClause := [(101,true),(34,true),(37,false),(45,false),(48,false),(51,true),(59,false)]
theorem inputList2514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2514 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2514 (by decide) v hb
mask_input "2514|576777549091176448|2535301200456461054810399965184"
def inputClause2515 : CNF.NClause := [(101,true),(34,false),(37,true),(45,false),(48,false),(51,true),(59,false)]
theorem inputList2515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2515 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2515 (by decide) v hb
mask_input "2515|576777428832092160|2535301200456461054930659049472"
def inputClause2516 : CNF.NClause := [(101,true),(34,true),(37,true),(45,false),(48,false),(51,true),(59,false)]
theorem inputList2516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2516 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2516 (by decide) v hb
mask_input "2516|576777411652222976|2535301200456461054947838918656"
def inputClause2517 : CNF.NClause := [(101,true),(34,false),(37,false),(45,true),(48,false),(51,true),(59,false)]
theorem inputList2517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2517 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2517 (by decide) v hb
mask_input "2517|576742381898956800|2535301200456461089977592184832"
def inputClause2518 : CNF.NClause := [(101,true),(34,true),(37,false),(45,true),(48,false),(51,true),(59,false)]
theorem inputList2518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2518 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2518 (by decide) v hb
mask_input "2518|576742364719087616|2535301200456461089994772054016"
def inputClause2519 : CNF.NClause := [(101,true),(34,false),(37,true),(45,true),(48,false),(51,true),(59,false)]
theorem inputList2519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2519 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2519 (by decide) v hb
mask_input "2519|576742244460003328|2535301200456461090115031138304"
def inputClause2520 : CNF.NClause := [(101,true),(34,true),(37,true),(45,true),(48,false),(51,true),(59,false)]
theorem inputList2520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2520 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2520 (by decide) v hb
mask_input "2520|576742227280134144|2535301200456461090132211007488"
def inputClause2521 : CNF.NClause := [(101,true),(34,false),(37,false),(45,false),(48,true),(51,true),(59,false)]
theorem inputList2521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2521 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2521 (by decide) v hb
mask_input "2521|576496091294334976|2535301200456461336268196806656"
def inputClause2522 : CNF.NClause := [(101,true),(34,true),(37,false),(45,false),(48,true),(51,true),(59,false)]
theorem inputList2522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2522 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2522 (by decide) v hb
mask_input "2522|576496074114465792|2535301200456461336285376675840"
def inputClause2523 : CNF.NClause := [(101,true),(34,false),(37,true),(45,false),(48,true),(51,true),(59,false)]
theorem inputList2523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2523 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2523 (by decide) v hb
mask_input "2523|576495953855381504|2535301200456461336405635760128"
def inputClause2524 : CNF.NClause := [(101,true),(34,true),(37,true),(45,false),(48,true),(51,true),(59,false)]
theorem inputList2524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2524 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2524 (by decide) v hb
mask_input "2524|576495936675512320|2535301200456461336422815629312"
def inputClause2525 : CNF.NClause := [(101,true),(34,false),(37,false),(45,true),(48,true),(51,true),(59,false)]
theorem inputList2525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2525 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2525 (by decide) v hb
mask_input "2525|576460906922246144|2535301200456461371452568895488"
def inputClause2526 : CNF.NClause := [(101,true),(34,true),(37,false),(45,true),(48,true),(51,true),(59,false)]
theorem inputList2526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2526 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2526 (by decide) v hb
mask_input "2526|576460889742376960|2535301200456461371469748764672"
def inputClause2527 : CNF.NClause := [(101,true),(34,false),(37,true),(45,true),(48,true),(51,true),(59,false)]
theorem inputList2527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2527 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2527 (by decide) v hb
mask_input "2527|576460769483292672|2535301200456461371590007848960"
def inputClause2528 : CNF.NClause := [(101,false),(34,true),(37,true),(45,true),(48,true),(51,true),(59,false)]
theorem inputList2528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2528 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2528 (by decide) v hb
mask_input "2528|2535301200457035263745709834240|2568613781307392"
def inputClause2529 : CNF.NClause := [(101,true),(34,false),(37,false),(45,false),(48,false),(51,false),(59,true)]
theorem inputList2529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2529 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2529 (by decide) v hb
mask_input "2529|2568613781307392|2535301200457035263745709834240"
def inputClause2530 : CNF.NClause := [(101,true),(34,true),(37,false),(45,false),(48,false),(51,false),(59,true)]
theorem inputList2530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2530 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2530 (by decide) v hb
mask_input "2530|2568596601438208|2535301200457035263762889703424"
def inputClause2531 : CNF.NClause := [(101,true),(34,false),(37,true),(45,false),(48,false),(51,false),(59,true)]
theorem inputList2531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2531 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2531 (by decide) v hb
mask_input "2531|2568476342353920|2535301200457035263883148787712"
def inputClause2532 : CNF.NClause := [(101,true),(34,true),(37,true),(45,false),(48,false),(51,false),(59,true)]
theorem inputList2532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2532 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2532 (by decide) v hb
mask_input "2532|2568459162484736|2535301200457035263900328656896"
def inputClause2533 : CNF.NClause := [(101,true),(34,false),(37,false),(45,true),(48,false),(51,false),(59,true)]
theorem inputList2533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2533 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2533 (by decide) v hb
mask_input "2533|2533429409218560|2535301200457035298930081923072"
def inputClause2534 : CNF.NClause := [(101,true),(34,true),(37,false),(45,true),(48,false),(51,false),(59,true)]
theorem inputList2534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2534 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2534 (by decide) v hb
mask_input "2534|2533412229349376|2535301200457035298947261792256"
def inputClause2535 : CNF.NClause := [(101,true),(34,false),(37,true),(45,true),(48,false),(51,false),(59,true)]
theorem inputList2535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2535 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2535 (by decide) v hb
mask_input "2535|2533291970265088|2535301200457035299067520876544"
def inputClause2536 : CNF.NClause := [(101,true),(34,true),(37,true),(45,true),(48,false),(51,false),(59,true)]
theorem inputList2536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2536 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2536 (by decide) v hb
mask_input "2536|2533274790395904|2535301200457035299084700745728"
def inputClause2537 : CNF.NClause := [(101,true),(34,false),(37,false),(45,false),(48,true),(51,false),(59,true)]
theorem inputList2537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2537 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2537 (by decide) v hb
mask_input "2537|2287138804596736|2535301200457035545220686544896"
def inputClause2538 : CNF.NClause := [(101,true),(34,true),(37,false),(45,false),(48,true),(51,false),(59,true)]
theorem inputList2538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2538 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2538 (by decide) v hb
mask_input "2538|2287121624727552|2535301200457035545237866414080"
def inputClause2539 : CNF.NClause := [(101,true),(34,false),(37,true),(45,false),(48,true),(51,false),(59,true)]
theorem inputList2539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2539 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2539 (by decide) v hb
mask_input "2539|2287001365643264|2535301200457035545358125498368"
def inputClause2540 : CNF.NClause := [(101,true),(34,true),(37,true),(45,false),(48,true),(51,false),(59,true)]
theorem inputList2540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2540 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2540 (by decide) v hb
mask_input "2540|2286984185774080|2535301200457035545375305367552"
def inputClause2541 : CNF.NClause := [(101,true),(34,false),(37,false),(45,true),(48,true),(51,false),(59,true)]
theorem inputList2541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2541 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2541 (by decide) v hb
mask_input "2541|2251954432507904|2535301200457035580405058633728"
def inputClause2542 : CNF.NClause := [(101,true),(34,true),(37,false),(45,true),(48,true),(51,false),(59,true)]
theorem inputList2542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2542 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2542 (by decide) v hb
mask_input "2542|2251937252638720|2535301200457035580422238502912"
def inputClause2543 : CNF.NClause := [(101,true),(34,false),(37,true),(45,true),(48,true),(51,false),(59,true)]
theorem inputList2543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2543 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2543 (by decide) v hb
mask_input "2543|2251816993554432|2535301200457035580542497587200"
def inputClause2545 : CNF.NClause := [(101,true),(34,false),(37,false),(45,false),(48,false),(51,true),(59,true)]
theorem inputList2545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2545 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2545 (by decide) v hb
mask_input "2545|316813967622144|2535301200457037515545523519488"
def inputClause2546 : CNF.NClause := [(101,true),(34,true),(37,false),(45,false),(48,false),(51,true),(59,true)]
theorem inputList2546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2546 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2546 (by decide) v hb
mask_input "2546|316796787752960|2535301200457037515562703388672"
def inputClause2547 : CNF.NClause := [(101,true),(34,false),(37,true),(45,false),(48,false),(51,true),(59,true)]
theorem inputList2547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2547 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2547 (by decide) v hb
mask_input "2547|316676528668672|2535301200457037515682962472960"
end Percolation.MaskChain
