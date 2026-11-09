import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause7453 : CNF.NClause := [(58,false),(27,false),(62,false),(69,true),(76,true),(78,true),(85,false),(89,false)]
theorem inputList7453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7453 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7453 (by decide) v hb
mask_input "7453|657655650770274665753477120|378379614439930322747392"
def inputClause7454 : CNF.NClause := [(58,false),(27,true),(62,false),(69,true),(76,true),(78,true),(85,false),(89,false)]
theorem inputList7454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7454 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7454 (by decide) v hb
mask_input "7454|657655650770274665619259392|378379614439930456965120"
def inputClause7455 : CNF.NClause := [(58,false),(27,false),(62,true),(69,true),(76,true),(78,true),(85,false),(89,false)]
theorem inputList7455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7455 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7455 (by decide) v hb
mask_input "7455|657655646158588647326089216|378384226125948750135296"
def inputClause7456 : CNF.NClause := [(58,false),(27,true),(62,true),(69,true),(76,true),(78,true),(85,false),(89,false)]
theorem inputList7456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7456 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7456 (by decide) v hb
mask_input "7456|657655646158588647191871488|378384226125948884353024"
def inputClause7457 : CNF.NClause := [(58,false),(27,false),(62,false),(69,false),(76,false),(78,false),(85,true),(89,false)]
theorem inputList7457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7457 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7457 (by decide) v hb
mask_input "7457|619348404157046462485626880|38685626227668133590597632"
def inputClause7458 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,false),(78,false),(85,true),(89,false)]
theorem inputList7458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7458 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7458 (by decide) v hb
mask_input "7458|619348404157046462351409152|38685626227668133724815360"
def inputClause7459 : CNF.NClause := [(58,false),(27,false),(62,true),(69,false),(76,false),(78,false),(85,true),(89,false)]
theorem inputList7459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7459 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7459 (by decide) v hb
mask_input "7459|619348399545360444058238976|38685630839354152017985536"
def inputClause7460 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,false),(78,false),(85,true),(89,false)]
theorem inputList7460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7460 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7460 (by decide) v hb
mask_input "7460|619348399545360443924021248|38685630839354152152203264"
def inputClause7461 : CNF.NClause := [(58,false),(27,false),(62,false),(69,true),(76,false),(78,false),(85,true),(89,false)]
theorem inputList7461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7461 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7461 (by decide) v hb
mask_input "7461|619347813861236103779975168|38686216523478492296249344"
def inputClause7462 : CNF.NClause := [(58,false),(27,true),(62,false),(69,true),(76,false),(78,false),(85,true),(89,false)]
theorem inputList7462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7462 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7462 (by decide) v hb
mask_input "7462|619347813861236103645757440|38686216523478492430467072"
def inputClause7463 : CNF.NClause := [(58,false),(27,false),(62,true),(69,true),(76,false),(78,false),(85,true),(89,false)]
theorem inputList7463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7463 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7463 (by decide) v hb
mask_input "7463|619347809249550085352587264|38686221135164510723637248"
def inputClause7464 : CNF.NClause := [(58,false),(27,true),(62,true),(69,true),(76,false),(78,false),(85,true),(89,false)]
theorem inputList7464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7464 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7464 (by decide) v hb
mask_input "7464|619347809249550085218369536|38686221135164510857854976"
def inputClause7465 : CNF.NClause := [(58,false),(27,false),(62,false),(69,false),(76,true),(78,false),(85,true),(89,false)]
theorem inputList7465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7465 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7465 (by decide) v hb
mask_input "7465|619272846293320548162207744|38761184091394047914016768"
def inputClause7466 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,true),(78,false),(85,true),(89,false)]
theorem inputList7466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7466 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7466 (by decide) v hb
mask_input "7466|619272846293320548027990016|38761184091394048048234496"
def inputClause7467 : CNF.NClause := [(58,false),(27,false),(62,true),(69,false),(76,true),(78,false),(85,true),(89,false)]
theorem inputList7467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7467 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7467 (by decide) v hb
mask_input "7467|619272841681634529734819840|38761188703080066341404672"
def inputClause7468 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,true),(78,false),(85,true),(89,false)]
theorem inputList7468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7468 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7468 (by decide) v hb
mask_input "7468|619272841681634529600602112|38761188703080066475622400"
def inputClause7469 : CNF.NClause := [(58,false),(27,false),(62,false),(69,true),(76,true),(78,false),(85,true),(89,false)]
theorem inputList7469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7469 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7469 (by decide) v hb
mask_input "7469|619272255997510189456556032|38761774387204406619668480"
def inputClause7470 : CNF.NClause := [(58,false),(27,true),(62,false),(69,true),(76,true),(78,false),(85,true),(89,false)]
theorem inputList7470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7470 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7470 (by decide) v hb
mask_input "7470|619272255997510189322338304|38761774387204406753886208"
def inputClause7471 : CNF.NClause := [(58,false),(27,false),(62,true),(69,true),(76,true),(78,false),(85,true),(89,false)]
theorem inputList7471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7471 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7471 (by decide) v hb
mask_input "7471|619272251385824171029168128|38761778998890425047056384"
def inputClause7472 : CNF.NClause := [(58,false),(27,true),(62,true),(69,true),(76,true),(78,false),(85,true),(89,false)]
theorem inputList7472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7472 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7472 (by decide) v hb
mask_input "7472|619272251385824170894950400|38761778998890425181274112"
def inputClause7473 : CNF.NClause := [(58,false),(27,false),(62,false),(69,false),(76,false),(78,true),(85,true),(89,false)]
theorem inputList7473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7473 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7473 (by decide) v hb
mask_input "7473|619046172702142805191950336|38987857682571790884274176"
def inputClause7474 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,false),(78,true),(85,true),(89,false)]
theorem inputList7474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7474 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7474 (by decide) v hb
mask_input "7474|619046172702142805057732608|38987857682571791018491904"
def inputClause7475 : CNF.NClause := [(58,false),(27,false),(62,true),(69,false),(76,false),(78,true),(85,true),(89,false)]
theorem inputList7475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7475 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7475 (by decide) v hb
mask_input "7475|619046168090456786764562432|38987862294257809311662080"
def inputClause7476 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,false),(78,true),(85,true),(89,false)]
theorem inputList7476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7476 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7476 (by decide) v hb
mask_input "7476|619046168090456786630344704|38987862294257809445879808"
def inputClause7477 : CNF.NClause := [(58,false),(27,false),(62,false),(69,true),(76,false),(78,true),(85,true),(89,false)]
theorem inputList7477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7477 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7477 (by decide) v hb
mask_input "7477|619045582406332446486298624|38988447978382149589925888"
def inputClause7478 : CNF.NClause := [(58,false),(27,true),(62,false),(69,true),(76,false),(78,true),(85,true),(89,false)]
theorem inputList7478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7478 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7478 (by decide) v hb
mask_input "7478|619045582406332446352080896|38988447978382149724143616"
def inputClause7479 : CNF.NClause := [(58,false),(27,false),(62,true),(69,true),(76,false),(78,true),(85,true),(89,false)]
theorem inputList7479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7479 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7479 (by decide) v hb
mask_input "7479|619045577794646428058910720|38988452590068168017313792"
def inputClause7480 : CNF.NClause := [(58,false),(27,true),(62,true),(69,true),(76,false),(78,true),(85,true),(89,false)]
theorem inputList7480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7480 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7480 (by decide) v hb
mask_input "7480|619045577794646427924692992|38988452590068168151531520"
def inputClause7481 : CNF.NClause := [(58,false),(27,false),(62,false),(69,false),(76,true),(78,true),(85,true),(89,false)]
theorem inputList7481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7481 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7481 (by decide) v hb
mask_input "7481|618970614838416890868531200|39063415546297705207693312"
def inputClause7482 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,true),(78,true),(85,true),(89,false)]
theorem inputList7482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7482 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7482 (by decide) v hb
mask_input "7482|618970614838416890734313472|39063415546297705341911040"
def inputClause7483 : CNF.NClause := [(58,false),(27,false),(62,true),(69,false),(76,true),(78,true),(85,true),(89,false)]
theorem inputList7483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7483 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7483 (by decide) v hb
mask_input "7483|618970610226730872441143296|39063420157983723635081216"
def inputClause7484 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,true),(78,true),(85,true),(89,false)]
theorem inputList7484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7484 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7484 (by decide) v hb
mask_input "7484|618970610226730872306925568|39063420157983723769298944"
def inputClause7485 : CNF.NClause := [(58,false),(27,false),(62,false),(69,true),(76,true),(78,true),(85,true),(89,false)]
theorem inputList7485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7485 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7485 (by decide) v hb
mask_input "7485|618970024542606532162879488|39064005842108063913345024"
def inputClause7486 : CNF.NClause := [(58,false),(27,true),(62,false),(69,true),(76,true),(78,true),(85,true),(89,false)]
theorem inputList7486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7486 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7486 (by decide) v hb
mask_input "7486|618970024542606532028661760|39064005842108064047562752"
def inputClause7488 : CNF.NClause := [(58,false),(27,true),(62,true),(69,true),(76,true),(78,true),(85,true),(89,false)]
theorem inputList7488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7488 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7488 (by decide) v hb
mask_input "7488|618970019930920513601273856|39064010453794082474950656"
def inputClause7489 : CNF.NClause := [(58,false),(27,false),(62,false),(69,false),(76,false),(78,false),(85,false),(89,true)]
theorem inputList7489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7489 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7489 (by decide) v hb
mask_input "7489|39064010742024458626662400|618970019642690137449562112"
def inputClause7490 : CNF.NClause := [(58,false),(27,true),(62,false),(69,false),(76,false),(78,false),(85,false),(89,true)]
theorem inputList7490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7490 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7490 (by decide) v hb
mask_input "7490|39064010742024458492444672|618970019642690137583779840"
def inputClause7491 : CNF.NClause := [(58,false),(27,false),(62,true),(69,false),(76,false),(78,false),(85,false),(89,true)]
theorem inputList7491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7491 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7491 (by decide) v hb
mask_input "7491|39064006130338440199274496|618970024254376155876950016"
def inputClause7492 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,false),(78,false),(85,false),(89,true)]
theorem inputList7492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7492 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7492 (by decide) v hb
mask_input "7492|39064006130338440065056768|618970024254376156011167744"
def inputClause7493 : CNF.NClause := [(58,false),(27,false),(62,false),(69,true),(76,false),(78,false),(85,false),(89,true)]
theorem inputList7493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7493 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 27) (spread_mem 27) inputClause7493 (by decide) v hb
mask_input "7493|39063420446214099921010688|618970609938500496155213824"
end Percolation.MaskChain
