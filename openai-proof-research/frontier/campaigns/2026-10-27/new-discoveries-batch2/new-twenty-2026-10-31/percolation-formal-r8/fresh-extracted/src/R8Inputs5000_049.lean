import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause6514 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,false),(77,true),(85,true),(90,true)]
theorem inputList6514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6514 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6514 (by decide) v hb
mask_input "6514|21259873670850165080064|1276776781240500237137084416"
def inputClause6515 : CNF.NClause := [(50,false),(19,false),(63,true),(71,false),(74,false),(77,true),(85,true),(90,true)]
theorem inputList6515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6515 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6515 (by decide) v hb
mask_input "6515|21250650298813310828544|1276776790463872273991335936"
def inputClause6516 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,false),(77,true),(85,true),(90,true)]
theorem inputList6516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6516 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6516 (by decide) v hb
mask_input "6516|21250650298813310304256|1276776790463872273991860224"
def inputClause6517 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(74,false),(77,true),(85,true),(90,true)]
theorem inputList6517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6517 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6517 (by decide) v hb
mask_input "6517|18898690429415342997504|1276779142423741671959166976"
def inputClause6518 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,false),(77,true),(85,true),(90,true)]
theorem inputList6518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6518 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6518 (by decide) v hb
mask_input "6518|18898690429415342473216|1276779142423741671959691264"
def inputClause6519 : CNF.NClause := [(50,false),(19,false),(63,true),(71,true),(74,false),(77,true),(85,true),(90,true)]
theorem inputList6519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6519 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6519 (by decide) v hb
mask_input "6519|18889467057378488221696|1276779151647113708813942784"
def inputClause6520 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,false),(77,true),(85,true),(90,true)]
theorem inputList6520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6520 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6520 (by decide) v hb
mask_input "6520|18889467057378487697408|1276779151647113708814467072"
def inputClause6521 : CNF.NClause := [(50,false),(19,false),(63,false),(71,false),(74,true),(77,true),(85,true),(90,true)]
theorem inputList6521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6521 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6521 (by decide) v hb
mask_input "6521|2370407739371584749568|1276795670706431715717414912"
def inputClause6523 : CNF.NClause := [(50,false),(19,false),(63,true),(71,false),(74,true),(77,true),(85,true),(90,true)]
theorem inputList6523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6523 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6523 (by decide) v hb
mask_input "6523|2361184367334729973760|1276795679929803752572190720"
def inputClause6524 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,true),(77,true),(85,true),(90,true)]
theorem inputList6524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6524 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6524 (by decide) v hb
mask_input "6524|2361184367334729449472|1276795679929803752572715008"
def inputClause6526 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,true),(77,true),(85,true),(90,true)]
theorem inputList6526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6526 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6526 (by decide) v hb
mask_input "6526|9224497936761618432|1276798031889673150540546048"
def inputClause6528 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,true),(77,true),(85,true),(90,true)]
theorem inputList6528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6528 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6528 (by decide) v hb
mask_input "6528|1125899906842624|1276798041113045187395321856"
def inputClause6529 : CNF.NClause := [(51,true),(20,false),(67,false),(68,false),(69,false),(70,false),(71,false),(92,false)]
theorem inputList6529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6529 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6529 (by decide) v hb
mask_input "6529|4951764731934051379566346240|2251799813685248"
def inputClause6530 : CNF.NClause := [(51,false),(20,true),(67,false),(68,false),(69,false),(70,false),(71,false),(92,false)]
theorem inputList6530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6530 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6530 (by decide) v hb
mask_input "6530|4951764731936303179378982912|1048576"
def inputClause6531 : CNF.NClause := [(51,false),(20,false),(67,true),(68,false),(69,false),(70,false),(71,false),(92,false)]
theorem inputList6531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6531 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6531 (by decide) v hb
mask_input "6531|4951764584362350589703618560|147573952589676412928"
def inputClause6532 : CNF.NClause := [(51,false),(20,true),(67,true),(68,false),(69,false),(70,false),(71,false),(92,false)]
theorem inputList6532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6532 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6532 (by decide) v hb
mask_input "6532|4951764584362350589702569984|147573952589677461504"
def inputClause6533 : CNF.NClause := [(51,false),(20,false),(67,false),(68,true),(69,false),(70,false),(71,false),(92,false)]
theorem inputList6533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6533 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6533 (by decide) v hb
mask_input "6533|4951764436788398000027205632|295147905179352825856"
def inputClause6534 : CNF.NClause := [(51,false),(20,true),(67,false),(68,true),(69,false),(70,false),(71,false),(92,false)]
theorem inputList6534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6534 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6534 (by decide) v hb
mask_input "6534|4951764436788398000026157056|295147905179353874432"
def inputClause6535 : CNF.NClause := [(51,false),(20,false),(67,true),(68,true),(69,false),(70,false),(71,false),(92,false)]
theorem inputList6535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6535 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6535 (by decide) v hb
mask_input "6535|4951764289214445410350792704|442721857769029238784"
def inputClause6536 : CNF.NClause := [(51,false),(20,true),(67,true),(68,true),(69,false),(70,false),(71,false),(92,false)]
theorem inputList6536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6536 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6536 (by decide) v hb
mask_input "6536|4951764289214445410349744128|442721857769030287360"
def inputClause6537 : CNF.NClause := [(51,false),(20,false),(67,false),(68,false),(69,true),(70,false),(71,false),(92,false)]
theorem inputList6537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6537 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6537 (by decide) v hb
mask_input "6537|4951764141640492820674379776|590295810358705651712"
def inputClause6538 : CNF.NClause := [(51,false),(20,true),(67,false),(68,false),(69,true),(70,false),(71,false),(92,false)]
theorem inputList6538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6538 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6538 (by decide) v hb
mask_input "6538|4951764141640492820673331200|590295810358706700288"
def inputClause6539 : CNF.NClause := [(51,false),(20,false),(67,true),(68,false),(69,true),(70,false),(71,false),(92,false)]
theorem inputList6539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6539 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6539 (by decide) v hb
mask_input "6539|4951763994066540230997966848|737869762948382064640"
def inputClause6540 : CNF.NClause := [(51,false),(20,true),(67,true),(68,false),(69,true),(70,false),(71,false),(92,false)]
theorem inputList6540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6540 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6540 (by decide) v hb
mask_input "6540|4951763994066540230996918272|737869762948383113216"
def inputClause6541 : CNF.NClause := [(51,false),(20,false),(67,false),(68,true),(69,true),(70,false),(71,false),(92,false)]
theorem inputList6541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6541 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6541 (by decide) v hb
mask_input "6541|4951763846492587641321553920|885443715538058477568"
def inputClause6542 : CNF.NClause := [(51,false),(20,true),(67,false),(68,true),(69,true),(70,false),(71,false),(92,false)]
theorem inputList6542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6542 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6542 (by decide) v hb
mask_input "6542|4951763846492587641320505344|885443715538059526144"
def inputClause6543 : CNF.NClause := [(51,false),(20,false),(67,true),(68,true),(69,true),(70,false),(71,false),(92,false)]
theorem inputList6543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6543 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6543 (by decide) v hb
mask_input "6543|4951763698918635051645140992|1033017668127734890496"
def inputClause6544 : CNF.NClause := [(51,false),(20,true),(67,true),(68,true),(69,true),(70,false),(71,false),(92,false)]
theorem inputList6544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6544 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6544 (by decide) v hb
mask_input "6544|4951763698918635051644092416|1033017668127735939072"
def inputClause6545 : CNF.NClause := [(51,false),(20,false),(67,false),(68,false),(69,false),(70,true),(71,false),(92,false)]
theorem inputList6545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6545 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6545 (by decide) v hb
mask_input "6545|4951763551344682461968728064|1180591620717411303424"
def inputClause6546 : CNF.NClause := [(51,false),(20,true),(67,false),(68,false),(69,false),(70,true),(71,false),(92,false)]
theorem inputList6546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6546 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6546 (by decide) v hb
mask_input "6546|4951763551344682461967679488|1180591620717412352000"
def inputClause6547 : CNF.NClause := [(51,false),(20,false),(67,true),(68,false),(69,false),(70,true),(71,false),(92,false)]
theorem inputList6547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6547 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6547 (by decide) v hb
mask_input "6547|4951763403770729872292315136|1328165573307087716352"
def inputClause6548 : CNF.NClause := [(51,false),(20,true),(67,true),(68,false),(69,false),(70,true),(71,false),(92,false)]
theorem inputList6548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6548 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6548 (by decide) v hb
mask_input "6548|4951763403770729872291266560|1328165573307088764928"
def inputClause6549 : CNF.NClause := [(51,false),(20,false),(67,false),(68,true),(69,false),(70,true),(71,false),(92,false)]
theorem inputList6549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6549 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6549 (by decide) v hb
mask_input "6549|4951763256196777282615902208|1475739525896764129280"
def inputClause6550 : CNF.NClause := [(51,false),(20,true),(67,false),(68,true),(69,false),(70,true),(71,false),(92,false)]
theorem inputList6550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6550 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6550 (by decide) v hb
mask_input "6550|4951763256196777282614853632|1475739525896765177856"
def inputClause6551 : CNF.NClause := [(51,false),(20,false),(67,true),(68,true),(69,false),(70,true),(71,false),(92,false)]
theorem inputList6551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6551 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6551 (by decide) v hb
mask_input "6551|4951763108622824692939489280|1623313478486440542208"
def inputClause6552 : CNF.NClause := [(51,false),(20,true),(67,true),(68,true),(69,false),(70,true),(71,false),(92,false)]
theorem inputList6552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6552 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6552 (by decide) v hb
mask_input "6552|4951763108622824692938440704|1623313478486441590784"
def inputClause6553 : CNF.NClause := [(51,false),(20,false),(67,false),(68,false),(69,true),(70,true),(71,false),(92,false)]
theorem inputList6553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6553 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6553 (by decide) v hb
mask_input "6553|4951762961048872103263076352|1770887431076116955136"
def inputClause6554 : CNF.NClause := [(51,false),(20,true),(67,false),(68,false),(69,true),(70,true),(71,false),(92,false)]
theorem inputList6554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6554 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6554 (by decide) v hb
mask_input "6554|4951762961048872103262027776|1770887431076118003712"
def inputClause6555 : CNF.NClause := [(51,false),(20,false),(67,true),(68,false),(69,true),(70,true),(71,false),(92,false)]
theorem inputList6555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6555 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6555 (by decide) v hb
mask_input "6555|4951762813474919513586663424|1918461383665793368064"
def inputClause6556 : CNF.NClause := [(51,false),(20,true),(67,true),(68,false),(69,true),(70,true),(71,false),(92,false)]
theorem inputList6556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6556 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6556 (by decide) v hb
mask_input "6556|4951762813474919513585614848|1918461383665794416640"
end Percolation.MaskChain
