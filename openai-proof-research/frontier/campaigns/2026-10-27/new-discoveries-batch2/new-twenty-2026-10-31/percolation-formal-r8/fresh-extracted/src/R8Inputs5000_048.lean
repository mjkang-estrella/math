import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause6468 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,false),(77,false),(85,false),(90,true)]
theorem inputList6468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6468 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6468 (by decide) v hb
mask_input "6468|38857992605418775547740160|1237940048508752311754424320"
def inputClause6469 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(74,false),(77,false),(85,false),(90,true)]
theorem inputList6469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6469 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6469 (by decide) v hb
mask_input "6469|38855640645549377580433408|1237942400468621709721731072"
def inputClause6470 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,false),(77,false),(85,false),(90,true)]
theorem inputList6470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6470 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6470 (by decide) v hb
mask_input "6470|38855640645549377579909120|1237942400468621709722255360"
def inputClause6471 : CNF.NClause := [(50,false),(19,false),(63,true),(71,true),(74,false),(77,false),(85,false),(90,true)]
theorem inputList6471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6471 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6471 (by decide) v hb
mask_input "6471|38855631422177340725657600|1237942409691993746576506880"
def inputClause6472 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,false),(77,false),(85,false),(90,true)]
theorem inputList6472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6472 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6472 (by decide) v hb
mask_input "6472|38855631422177340725133312|1237942409691993746577031168"
def inputClause6473 : CNF.NClause := [(50,false),(19,false),(63,false),(71,false),(74,true),(77,false),(85,false),(90,true)]
theorem inputList6473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6473 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6473 (by decide) v hb
mask_input "6473|38839112362859333822185472|1237958928751311753479979008"
def inputClause6475 : CNF.NClause := [(50,false),(19,false),(63,true),(71,false),(74,true),(77,false),(85,false),(90,true)]
theorem inputList6475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6475 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6475 (by decide) v hb
mask_input "6475|38839103139487296967409664|1237958937974683790334754816"
def inputClause6476 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,true),(77,false),(85,false),(90,true)]
theorem inputList6476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6476 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6476 (by decide) v hb
mask_input "6476|38839103139487296966885376|1237958937974683790335279104"
def inputClause6477 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(74,true),(77,false),(85,false),(90,true)]
theorem inputList6477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6477 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6477 (by decide) v hb
mask_input "6477|38836751179617898999578624|1237961289934553188302585856"
def inputClause6478 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,true),(77,false),(85,false),(90,true)]
theorem inputList6478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6478 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6478 (by decide) v hb
mask_input "6478|38836751179617898999054336|1237961289934553188303110144"
def inputClause6479 : CNF.NClause := [(50,false),(19,false),(63,true),(71,true),(74,true),(77,false),(85,false),(90,true)]
theorem inputList6479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6479 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6479 (by decide) v hb
mask_input "6479|38836741956245862144802816|1237961299157925225157361664"
def inputClause6480 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,true),(77,false),(85,false),(90,true)]
theorem inputList6480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6480 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6480 (by decide) v hb
mask_input "6480|38836741956245862144278528|1237961299157925225157885952"
def inputClause6483 : CNF.NClause := [(50,false),(19,false),(63,true),(71,false),(74,false),(77,true),(85,false),(90,true)]
theorem inputList6483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6483 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6483 (by decide) v hb
mask_input "6483|38706876877966946901426176|1238091164236204140400738304"
def inputClause6484 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,false),(77,true),(85,false),(90,true)]
theorem inputList6484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6484 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6484 (by decide) v hb
mask_input "6484|38706876877966946900901888|1238091164236204140401262592"
def inputClause6485 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(74,false),(77,true),(85,false),(90,true)]
theorem inputList6485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6485 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6485 (by decide) v hb
mask_input "6485|38704524918097548933595136|1238093516196073538368569344"
def inputClause6486 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,false),(77,true),(85,false),(90,true)]
theorem inputList6486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6486 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6486 (by decide) v hb
mask_input "6486|38704524918097548933070848|1238093516196073538369093632"
def inputClause6487 : CNF.NClause := [(50,false),(19,false),(63,true),(71,true),(74,false),(77,true),(85,false),(90,true)]
theorem inputList6487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6487 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6487 (by decide) v hb
mask_input "6487|38704515694725512078819328|1238093525419445575223345152"
def inputClause6488 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,false),(77,true),(85,false),(90,true)]
theorem inputList6488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6488 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6488 (by decide) v hb
mask_input "6488|38704515694725512078295040|1238093525419445575223869440"
def inputClause6489 : CNF.NClause := [(50,false),(19,false),(63,false),(71,false),(74,true),(77,true),(85,false),(90,true)]
theorem inputList6489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6489 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6489 (by decide) v hb
mask_input "6489|38687996635407505175347200|1238110044478763582126817280"
def inputClause6491 : CNF.NClause := [(50,false),(19,false),(63,true),(71,false),(74,true),(77,true),(85,false),(90,true)]
theorem inputList6491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6491 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6491 (by decide) v hb
mask_input "6491|38687987412035468320571392|1238110053702135618981593088"
def inputClause6492 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,true),(77,true),(85,false),(90,true)]
theorem inputList6492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6492 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6492 (by decide) v hb
mask_input "6492|38687987412035468320047104|1238110053702135618982117376"
def inputClause6493 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(74,true),(77,true),(85,false),(90,true)]
theorem inputList6493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6493 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6493 (by decide) v hb
mask_input "6493|38685635452166070352740352|1238112405662005016949424128"
def inputClause6494 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,true),(77,true),(85,false),(90,true)]
theorem inputList6494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6494 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6494 (by decide) v hb
mask_input "6494|38685635452166070352216064|1238112405662005016949948416"
def inputClause6495 : CNF.NClause := [(50,false),(19,false),(63,true),(71,true),(74,true),(77,true),(85,false),(90,true)]
theorem inputList6495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6495 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6495 (by decide) v hb
mask_input "6495|38685626228794033497964544|1238112414885377053804199936"
def inputClause6496 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,true),(77,true),(85,false),(90,true)]
theorem inputList6496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6496 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6496 (by decide) v hb
mask_input "6496|38685626228794033497440256|1238112414885377053804724224"
def inputClause6497 : CNF.NClause := [(50,false),(19,false),(63,false),(71,false),(74,false),(77,false),(85,true),(90,true)]
theorem inputList6497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6497 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6497 (by decide) v hb
mask_input "6497|172375601122678812442624|1276625665513048408489721856"
def inputClause6498 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,false),(77,false),(85,true),(90,true)]
theorem inputList6498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6498 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6498 (by decide) v hb
mask_input "6498|172375601122678811918336|1276625665513048408490246144"
def inputClause6499 : CNF.NClause := [(50,false),(19,false),(63,true),(71,false),(74,false),(77,false),(85,true),(90,true)]
theorem inputList6499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6499 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6499 (by decide) v hb
mask_input "6499|172366377750641957666816|1276625674736420445344497664"
def inputClause6500 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,false),(77,false),(85,true),(90,true)]
theorem inputList6500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6500 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6500 (by decide) v hb
mask_input "6500|172366377750641957142528|1276625674736420445345021952"
def inputClause6501 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(74,false),(77,false),(85,true),(90,true)]
theorem inputList6501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6501 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6501 (by decide) v hb
mask_input "6501|170014417881243989835776|1276628026696289843312328704"
def inputClause6502 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,false),(77,false),(85,true),(90,true)]
theorem inputList6502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6502 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6502 (by decide) v hb
mask_input "6502|170014417881243989311488|1276628026696289843312852992"
def inputClause6503 : CNF.NClause := [(50,false),(19,false),(63,true),(71,true),(74,false),(77,false),(85,true),(90,true)]
theorem inputList6503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6503 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6503 (by decide) v hb
mask_input "6503|170005194509207135059968|1276628035919661880167104512"
def inputClause6504 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,false),(77,false),(85,true),(90,true)]
theorem inputList6504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6504 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6504 (by decide) v hb
mask_input "6504|170005194509207134535680|1276628035919661880167628800"
def inputClause6505 : CNF.NClause := [(50,false),(19,false),(63,false),(71,false),(74,true),(77,false),(85,true),(90,true)]
theorem inputList6505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6505 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6505 (by decide) v hb
mask_input "6505|153486135191200231587840|1276644554978979887070576640"
def inputClause6507 : CNF.NClause := [(50,false),(19,false),(63,true),(71,false),(74,true),(77,false),(85,true),(90,true)]
theorem inputList6507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6507 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6507 (by decide) v hb
mask_input "6507|153476911819163376812032|1276644564202351923925352448"
def inputClause6508 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,true),(77,false),(85,true),(90,true)]
theorem inputList6508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6508 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6508 (by decide) v hb
mask_input "6508|153476911819163376287744|1276644564202351923925876736"
def inputClause6509 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(74,true),(77,false),(85,true),(90,true)]
theorem inputList6509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6509 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6509 (by decide) v hb
mask_input "6509|151124951949765408980992|1276646916162221321893183488"
def inputClause6510 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,true),(77,false),(85,true),(90,true)]
theorem inputList6510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6510 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6510 (by decide) v hb
mask_input "6510|151124951949765408456704|1276646916162221321893707776"
def inputClause6511 : CNF.NClause := [(50,false),(19,false),(63,true),(71,true),(74,true),(77,false),(85,true),(90,true)]
theorem inputList6511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6511 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6511 (by decide) v hb
mask_input "6511|151115728577728554205184|1276646925385593358747959296"
def inputClause6512 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,true),(77,false),(85,true),(90,true)]
theorem inputList6512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6512 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 19) (spread_mem 19) inputClause6512 (by decide) v hb
mask_input "6512|151115728577728553680896|1276646925385593358748483584"
end Percolation.MaskChain
