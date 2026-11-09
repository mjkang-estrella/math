import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause4485 : CNF.NClause := [(35,false),(4,false),(63,false),(68,true),(73,false),(78,false),(83,false),(87,false)]
theorem inputList4485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4485 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4485 (by decide) v hb
mask_input "4485|164725596878831035558658064|295147905179352825856"
def inputClause4486 : CNF.NClause := [(35,false),(4,true),(63,false),(68,true),(73,false),(78,false),(83,false),(87,false)]
theorem inputList4486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4486 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4486 (by decide) v hb
mask_input "4486|164725596878831035558658048|295147905179352825872"
def inputClause4487 : CNF.NClause := [(35,false),(4,false),(63,true),(68,true),(73,false),(78,false),(83,false),(87,false)]
theorem inputList4487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4487 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4487 (by decide) v hb
mask_input "4487|164725587655458998703882256|304371277216207601664"
def inputClause4488 : CNF.NClause := [(35,false),(4,true),(63,true),(68,true),(73,false),(78,false),(83,false),(87,false)]
theorem inputList4488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4488 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4488 (by decide) v hb
mask_input "4488|164725587655458998703882240|304371277216207601680"
def inputClause4489 : CNF.NClause := [(35,false),(4,false),(63,false),(68,false),(73,true),(78,false),(83,false),(87,false)]
theorem inputList4489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4489 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4489 (by decide) v hb
mask_input "4489|164716447293770475621056528|9444732965739290427392"
def inputClause4490 : CNF.NClause := [(35,false),(4,true),(63,false),(68,false),(73,true),(78,false),(83,false),(87,false)]
theorem inputList4490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4490 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4490 (by decide) v hb
mask_input "4490|164716447293770475621056512|9444732965739290427408"
def inputClause4491 : CNF.NClause := [(35,false),(4,false),(63,true),(68,false),(73,true),(78,false),(83,false),(87,false)]
theorem inputList4491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4491 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4491 (by decide) v hb
mask_input "4491|164716438070398438766280720|9453956337776145203200"
def inputClause4492 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,true),(78,false),(83,false),(87,false)]
theorem inputList4492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4492 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4492 (by decide) v hb
mask_input "4492|164716438070398438766280704|9453956337776145203216"
def inputClause4493 : CNF.NClause := [(35,false),(4,false),(63,false),(68,true),(73,true),(78,false),(83,false),(87,false)]
theorem inputList4493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4493 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4493 (by decide) v hb
mask_input "4493|164716152145865296268230672|9739880870918643253248"
def inputClause4494 : CNF.NClause := [(35,false),(4,true),(63,false),(68,true),(73,true),(78,false),(83,false),(87,false)]
theorem inputList4494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4494 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4494 (by decide) v hb
mask_input "4494|164716152145865296268230656|9739880870918643253264"
def inputClause4495 : CNF.NClause := [(35,false),(4,false),(63,true),(68,true),(73,true),(78,false),(83,false),(87,false)]
theorem inputList4495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4495 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4495 (by decide) v hb
mask_input "4495|164716142922493259413454864|9749104242955498029056"
def inputClause4496 : CNF.NClause := [(35,false),(4,true),(63,true),(68,true),(73,true),(78,false),(83,false),(87,false)]
theorem inputList4496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4496 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4496 (by decide) v hb
mask_input "4496|164716142922493259413454848|9749104242955498029072"
def inputClause4497 : CNF.NClause := [(35,false),(4,false),(63,false),(68,false),(73,false),(78,true),(83,false),(87,false)]
theorem inputList4497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4497 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4497 (by decide) v hb
mask_input "4497|164423660571832557617807376|302231454903657293676544"
def inputClause4498 : CNF.NClause := [(35,false),(4,true),(63,false),(68,false),(73,false),(78,true),(83,false),(87,false)]
theorem inputList4498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4498 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4498 (by decide) v hb
mask_input "4498|164423660571832557617807360|302231454903657293676560"
def inputClause4499 : CNF.NClause := [(35,false),(4,false),(63,true),(68,false),(73,false),(78,true),(83,false),(87,false)]
theorem inputList4499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4499 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4499 (by decide) v hb
mask_input "4499|164423651348460520763031568|302240678275694148452352"
def inputClause4500 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,false),(78,true),(83,false),(87,false)]
theorem inputList4500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4500 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4500 (by decide) v hb
mask_input "4500|164423651348460520763031552|302240678275694148452368"
def inputClause4501 : CNF.NClause := [(35,false),(4,false),(63,false),(68,true),(73,false),(78,true),(83,false),(87,false)]
theorem inputList4501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4501 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4501 (by decide) v hb
mask_input "4501|164423365423927378264981520|302526602808836646502400"
def inputClause4502 : CNF.NClause := [(35,false),(4,true),(63,false),(68,true),(73,false),(78,true),(83,false),(87,false)]
theorem inputList4502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4502 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4502 (by decide) v hb
mask_input "4502|164423365423927378264981504|302526602808836646502416"
def inputClause4503 : CNF.NClause := [(35,false),(4,false),(63,true),(68,true),(73,false),(78,true),(83,false),(87,false)]
theorem inputList4503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4503 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4503 (by decide) v hb
mask_input "4503|164423356200555341410205712|302535826180873501278208"
def inputClause4504 : CNF.NClause := [(35,false),(4,true),(63,true),(68,true),(73,false),(78,true),(83,false),(87,false)]
theorem inputList4504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4504 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4504 (by decide) v hb
mask_input "4504|164423356200555341410205696|302535826180873501278224"
def inputClause4505 : CNF.NClause := [(35,false),(4,false),(63,false),(68,false),(73,true),(78,true),(83,false),(87,false)]
theorem inputList4505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4505 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4505 (by decide) v hb
mask_input "4505|164414215838866818327379984|311676187869396584103936"
def inputClause4506 : CNF.NClause := [(35,false),(4,true),(63,false),(68,false),(73,true),(78,true),(83,false),(87,false)]
theorem inputList4506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4506 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4506 (by decide) v hb
mask_input "4506|164414215838866818327379968|311676187869396584103952"
def inputClause4507 : CNF.NClause := [(35,false),(4,false),(63,true),(68,false),(73,true),(78,true),(83,false),(87,false)]
theorem inputList4507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4507 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4507 (by decide) v hb
mask_input "4507|164414206615494781472604176|311685411241433438879744"
def inputClause4508 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,true),(78,true),(83,false),(87,false)]
theorem inputList4508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4508 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4508 (by decide) v hb
mask_input "4508|164414206615494781472604160|311685411241433438879760"
def inputClause4509 : CNF.NClause := [(35,false),(4,false),(63,false),(68,true),(73,true),(78,true),(83,false),(87,false)]
theorem inputList4509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4509 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4509 (by decide) v hb
mask_input "4509|164413920690961638974554128|311971335774575936929792"
def inputClause4510 : CNF.NClause := [(35,false),(4,true),(63,false),(68,true),(73,true),(78,true),(83,false),(87,false)]
theorem inputList4510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4510 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4510 (by decide) v hb
mask_input "4510|164413920690961638974554112|311971335774575936929808"
def inputClause4511 : CNF.NClause := [(35,false),(4,false),(63,true),(68,true),(73,true),(78,true),(83,false),(87,false)]
theorem inputList4511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4511 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4511 (by decide) v hb
mask_input "4511|164413911467589602119778320|311980559146612791705600"
def inputClause4512 : CNF.NClause := [(35,false),(4,true),(63,true),(68,true),(73,true),(78,true),(83,false),(87,false)]
theorem inputList4512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4512 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4512 (by decide) v hb
mask_input "4512|164413911467589602119778304|311980559146612791705616"
def inputClause4513 : CNF.NClause := [(35,false),(4,false),(63,false),(68,false),(73,false),(78,false),(83,true),(87,false)]
theorem inputList4513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4513 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4513 (by decide) v hb
mask_input "4513|155054485469819181513834512|9671406556917033397649408"
def inputClause4514 : CNF.NClause := [(35,false),(4,true),(63,false),(68,false),(73,false),(78,false),(83,true),(87,false)]
theorem inputList4514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4514 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4514 (by decide) v hb
mask_input "4514|155054485469819181513834496|9671406556917033397649424"
def inputClause4515 : CNF.NClause := [(35,false),(4,false),(63,true),(68,false),(73,false),(78,false),(83,true),(87,false)]
theorem inputList4515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4515 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4515 (by decide) v hb
mask_input "4515|155054476246447144659058704|9671415780289070252425216"
def inputClause4516 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,false),(78,false),(83,true),(87,false)]
theorem inputList4516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4516 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4516 (by decide) v hb
mask_input "4516|155054476246447144659058688|9671415780289070252425232"
def inputClause4517 : CNF.NClause := [(35,false),(4,false),(63,false),(68,true),(73,false),(78,false),(83,true),(87,false)]
theorem inputList4517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4517 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4517 (by decide) v hb
mask_input "4517|155054190321914002161008656|9671701704822212750475264"
def inputClause4518 : CNF.NClause := [(35,false),(4,true),(63,false),(68,true),(73,false),(78,false),(83,true),(87,false)]
theorem inputList4518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4518 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4518 (by decide) v hb
mask_input "4518|155054190321914002161008640|9671701704822212750475280"
def inputClause4519 : CNF.NClause := [(35,false),(4,false),(63,true),(68,true),(73,false),(78,false),(83,true),(87,false)]
theorem inputList4519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4519 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4519 (by decide) v hb
mask_input "4519|155054181098541965306232848|9671710928194249605251072"
def inputClause4520 : CNF.NClause := [(35,false),(4,true),(63,true),(68,true),(73,false),(78,false),(83,true),(87,false)]
theorem inputList4520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4520 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4520 (by decide) v hb
mask_input "4520|155054181098541965306232832|9671710928194249605251088"
def inputClause4521 : CNF.NClause := [(35,false),(4,false),(63,false),(68,false),(73,true),(78,false),(83,true),(87,false)]
theorem inputList4521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4521 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4521 (by decide) v hb
mask_input "4521|155045040736853442223407120|9680851289882772688076800"
def inputClause4522 : CNF.NClause := [(35,false),(4,true),(63,false),(68,false),(73,true),(78,false),(83,true),(87,false)]
theorem inputList4522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4522 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4522 (by decide) v hb
mask_input "4522|155045040736853442223407104|9680851289882772688076816"
def inputClause4523 : CNF.NClause := [(35,false),(4,false),(63,true),(68,false),(73,true),(78,false),(83,true),(87,false)]
theorem inputList4523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4523 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4523 (by decide) v hb
mask_input "4523|155045031513481405368631312|9680860513254809542852608"
def inputClause4524 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,true),(78,false),(83,true),(87,false)]
theorem inputList4524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4524 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4524 (by decide) v hb
mask_input "4524|155045031513481405368631296|9680860513254809542852624"
end Percolation.MaskChain
