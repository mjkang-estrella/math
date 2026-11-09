import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause6424 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,false),(77,true),(85,false),(90,false)]
theorem inputList6424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6424 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6424 (by decide) v hb
mask_input "6424|1276644554980105786977419264|153486134065300324745216"
def inputClause6425 : CNF.NClause := [(50,false),(19,false),(63,false),(71,false),(74,true),(77,true),(85,false),(90,false)]
theorem inputList6425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6425 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6425 (by decide) v hb
mask_input "6425|1276628035920787780074471424|170005193383307227693056"
def inputClause6427 : CNF.NClause := [(50,false),(19,false),(63,true),(71,false),(74,true),(77,true),(85,false),(90,false)]
theorem inputList6427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6427 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6427 (by decide) v hb
mask_input "6427|1276628026697415743219695616|170014416755344082468864"
def inputClause6428 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,true),(77,true),(85,false),(90,false)]
theorem inputList6428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6428 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6428 (by decide) v hb
mask_input "6428|1276628026697415743219171328|170014416755344082993152"
def inputClause6429 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(74,true),(77,true),(85,false),(90,false)]
theorem inputList6429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6429 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6429 (by decide) v hb
mask_input "6429|1276625674737546345251864576|172366376624742050299904"
def inputClause6430 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,true),(77,true),(85,false),(90,false)]
theorem inputList6430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6430 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6430 (by decide) v hb
mask_input "6430|1276625674737546345251340288|172366376624742050824192"
def inputClause6431 : CNF.NClause := [(50,false),(19,false),(63,true),(71,true),(74,true),(77,true),(85,false),(90,false)]
theorem inputList6431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6431 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6431 (by decide) v hb
mask_input "6431|1276625665514174308397088768|172375599996778905075712"
def inputClause6432 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,true),(77,true),(85,false),(90,false)]
theorem inputList6432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6432 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6432 (by decide) v hb
mask_input "6432|1276625665514174308396564480|172375599996778905600000"
def inputClause6433 : CNF.NClause := [(50,false),(19,false),(63,false),(71,false),(74,false),(77,false),(85,true),(90,false)]
theorem inputList6433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6433 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6433 (by decide) v hb
mask_input "6433|1238112414886502953711566848|38685626227668133590597632"
def inputClause6434 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,false),(77,false),(85,true),(90,false)]
theorem inputList6434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6434 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6434 (by decide) v hb
mask_input "6434|1238112414886502953711042560|38685626227668133591121920"
def inputClause6435 : CNF.NClause := [(50,false),(19,false),(63,true),(71,false),(74,false),(77,false),(85,true),(90,false)]
theorem inputList6435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6435 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6435 (by decide) v hb
mask_input "6435|1238112405663130916856791040|38685635451040170445373440"
def inputClause6436 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,false),(77,false),(85,true),(90,false)]
theorem inputList6436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6436 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6436 (by decide) v hb
mask_input "6436|1238112405663130916856266752|38685635451040170445897728"
def inputClause6437 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(74,false),(77,false),(85,true),(90,false)]
theorem inputList6437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6437 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6437 (by decide) v hb
mask_input "6437|1238110053703261518888960000|38687987410909568413204480"
def inputClause6438 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,false),(77,false),(85,true),(90,false)]
theorem inputList6438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6438 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6438 (by decide) v hb
mask_input "6438|1238110053703261518888435712|38687987410909568413728768"
def inputClause6439 : CNF.NClause := [(50,false),(19,false),(63,true),(71,true),(74,false),(77,false),(85,true),(90,false)]
theorem inputList6439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6439 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6439 (by decide) v hb
mask_input "6439|1238110044479889482034184192|38687996634281605267980288"
def inputClause6440 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,false),(77,false),(85,true),(90,false)]
theorem inputList6440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6440 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6440 (by decide) v hb
mask_input "6440|1238110044479889482033659904|38687996634281605268504576"
def inputClause6441 : CNF.NClause := [(50,false),(19,false),(63,false),(71,false),(74,true),(77,false),(85,true),(90,false)]
theorem inputList6441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6441 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6441 (by decide) v hb
mask_input "6441|1238093525420571475130712064|38704515693599612171452416"
def inputClause6443 : CNF.NClause := [(50,false),(19,false),(63,true),(71,false),(74,true),(77,false),(85,true),(90,false)]
theorem inputList6443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6443 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6443 (by decide) v hb
mask_input "6443|1238093516197199438275936256|38704524916971649026228224"
def inputClause6444 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,true),(77,false),(85,true),(90,false)]
theorem inputList6444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6444 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6444 (by decide) v hb
mask_input "6444|1238093516197199438275411968|38704524916971649026752512"
def inputClause6445 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(74,true),(77,false),(85,true),(90,false)]
theorem inputList6445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6445 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6445 (by decide) v hb
mask_input "6445|1238091164237330040308105216|38706876876841046994059264"
def inputClause6446 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,true),(77,false),(85,true),(90,false)]
theorem inputList6446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6446 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6446 (by decide) v hb
mask_input "6446|1238091164237330040307580928|38706876876841046994583552"
def inputClause6447 : CNF.NClause := [(50,false),(19,false),(63,true),(71,true),(74,true),(77,false),(85,true),(90,false)]
theorem inputList6447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6447 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6447 (by decide) v hb
mask_input "6447|1238091155013958003453329408|38706886100213083848835072"
def inputClause6448 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,true),(77,false),(85,true),(90,false)]
theorem inputList6448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6448 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6448 (by decide) v hb
mask_input "6448|1238091155013958003452805120|38706886100213083849359360"
def inputClause6449 : CNF.NClause := [(50,false),(19,false),(63,false),(71,false),(74,false),(77,true),(85,true),(90,false)]
theorem inputList6449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6449 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6449 (by decide) v hb
mask_input "6449|1237961299159051125064728576|38836741955119962237435904"
def inputClause6450 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,false),(77,true),(85,true),(90,false)]
theorem inputList6450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6450 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6450 (by decide) v hb
mask_input "6450|1237961299159051125064204288|38836741955119962237960192"
def inputClause6451 : CNF.NClause := [(50,false),(19,false),(63,true),(71,false),(74,false),(77,true),(85,true),(90,false)]
theorem inputList6451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6451 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6451 (by decide) v hb
mask_input "6451|1237961289935679088209952768|38836751178491999092211712"
def inputClause6452 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,false),(77,true),(85,true),(90,false)]
theorem inputList6452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6452 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6452 (by decide) v hb
mask_input "6452|1237961289935679088209428480|38836751178491999092736000"
def inputClause6453 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(74,false),(77,true),(85,true),(90,false)]
theorem inputList6453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6453 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6453 (by decide) v hb
mask_input "6453|1237958937975809690242121728|38839103138361397060042752"
def inputClause6454 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,false),(77,true),(85,true),(90,false)]
theorem inputList6454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6454 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6454 (by decide) v hb
mask_input "6454|1237958937975809690241597440|38839103138361397060567040"
def inputClause6455 : CNF.NClause := [(50,false),(19,false),(63,true),(71,true),(74,false),(77,true),(85,true),(90,false)]
theorem inputList6455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6455 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6455 (by decide) v hb
mask_input "6455|1237958928752437653387345920|38839112361733433914818560"
def inputClause6456 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,false),(77,true),(85,true),(90,false)]
theorem inputList6456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6456 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6456 (by decide) v hb
mask_input "6456|1237958928752437653386821632|38839112361733433915342848"
def inputClause6457 : CNF.NClause := [(50,false),(19,false),(63,false),(71,false),(74,true),(77,true),(85,true),(90,false)]
theorem inputList6457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6457 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6457 (by decide) v hb
mask_input "6457|1237942409693119646483873792|38855631421051440818290688"
def inputClause6459 : CNF.NClause := [(50,false),(19,false),(63,true),(71,false),(74,true),(77,true),(85,true),(90,false)]
theorem inputList6459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6459 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6459 (by decide) v hb
mask_input "6459|1237942400469747609629097984|38855640644423477673066496"
def inputClause6460 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,true),(77,true),(85,true),(90,false)]
theorem inputList6460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6460 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6460 (by decide) v hb
mask_input "6460|1237942400469747609628573696|38855640644423477673590784"
def inputClause6461 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(74,true),(77,true),(85,true),(90,false)]
theorem inputList6461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6461 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6461 (by decide) v hb
mask_input "6461|1237940048509878211661266944|38857992604292875640897536"
def inputClause6462 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,true),(77,true),(85,true),(90,false)]
theorem inputList6462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6462 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6462 (by decide) v hb
mask_input "6462|1237940048509878211660742656|38857992604292875641421824"
def inputClause6463 : CNF.NClause := [(50,false),(19,false),(63,true),(71,true),(74,true),(77,true),(85,true),(90,false)]
theorem inputList6463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6463 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6463 (by decide) v hb
mask_input "6463|1237940039286506174806491136|38858001827664912495673344"
def inputClause6464 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,true),(77,true),(85,true),(90,false)]
theorem inputList6464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6464 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6464 (by decide) v hb
mask_input "6464|1237940039286506174805966848|38858001827664912496197632"
def inputClause6465 : CNF.NClause := [(50,false),(19,false),(63,false),(71,false),(74,false),(77,false),(85,false),(90,true)]
theorem inputList6465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6465 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6465 (by decide) v hb
mask_input "6465|38858001828790812403040256|1237940039285380274899124224"
def inputClause6467 : CNF.NClause := [(50,false),(19,false),(63,true),(71,false),(74,false),(77,false),(85,false),(90,true)]
theorem inputList6467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6467 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6467 (by decide) v hb
mask_input "6467|38857992605418775548264448|1237940048508752311753900032"
end Percolation.MaskChain
