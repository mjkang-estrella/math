import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause4566 : CNF.NClause := [(35,false),(4,true),(63,false),(68,true),(73,false),(78,true),(83,false),(87,true)]
theorem inputList4566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4566 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4566 (by decide) v hb
mask_input "4566|9680860513254843902590976|155045031513481371008892944"
def inputClause4567 : CNF.NClause := [(35,false),(4,false),(63,true),(68,true),(73,false),(78,true),(83,false),(87,true)]
theorem inputList4567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4567 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4567 (by decide) v hb
mask_input "4567|9680851289882807047815184|155045040736853407863668736"
def inputClause4568 : CNF.NClause := [(35,false),(4,true),(63,true),(68,true),(73,false),(78,true),(83,false),(87,true)]
theorem inputList4568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4568 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4568 (by decide) v hb
mask_input "4568|9680851289882807047815168|155045040736853407863668752"
def inputClause4569 : CNF.NClause := [(35,false),(4,false),(63,false),(68,false),(73,true),(78,true),(83,false),(87,true)]
theorem inputList4569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4569 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4569 (by decide) v hb
mask_input "4569|9671710928194283964989456|155054181098541930946494464"
def inputClause4570 : CNF.NClause := [(35,false),(4,true),(63,false),(68,false),(73,true),(78,true),(83,false),(87,true)]
theorem inputList4570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4570 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4570 (by decide) v hb
mask_input "4570|9671710928194283964989440|155054181098541930946494480"
def inputClause4571 : CNF.NClause := [(35,false),(4,false),(63,true),(68,false),(73,true),(78,true),(83,false),(87,true)]
theorem inputList4571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4571 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4571 (by decide) v hb
mask_input "4571|9671701704822247110213648|155054190321913967801270272"
def inputClause4572 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,true),(78,true),(83,false),(87,true)]
theorem inputList4572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4572 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4572 (by decide) v hb
mask_input "4572|9671701704822247110213632|155054190321913967801270288"
def inputClause4573 : CNF.NClause := [(35,false),(4,false),(63,false),(68,true),(73,true),(78,true),(83,false),(87,true)]
theorem inputList4573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4573 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4573 (by decide) v hb
mask_input "4573|9671415780289104612163600|155054476246447110299320320"
def inputClause4574 : CNF.NClause := [(35,false),(4,true),(63,false),(68,true),(73,true),(78,true),(83,false),(87,true)]
theorem inputList4574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4574 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4574 (by decide) v hb
mask_input "4574|9671415780289104612163584|155054476246447110299320336"
def inputClause4575 : CNF.NClause := [(35,false),(4,false),(63,true),(68,true),(73,true),(78,true),(83,false),(87,true)]
theorem inputList4575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4575 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4575 (by decide) v hb
mask_input "4575|9671406556917067757387792|155054485469819147154096128"
def inputClause4576 : CNF.NClause := [(35,false),(4,true),(63,true),(68,true),(73,true),(78,true),(83,false),(87,true)]
theorem inputList4576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4576 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4576 (by decide) v hb
mask_input "4576|9671406556917067757387776|155054485469819147154096144"
def inputClause4577 : CNF.NClause := [(35,false),(4,false),(63,false),(68,false),(73,false),(78,false),(83,true),(87,true)]
theorem inputList4577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4577 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4577 (by decide) v hb
mask_input "4577|311980559146647151443984|164413911467589567760039936"
def inputClause4578 : CNF.NClause := [(35,false),(4,true),(63,false),(68,false),(73,false),(78,false),(83,true),(87,true)]
theorem inputList4578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4578 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4578 (by decide) v hb
mask_input "4578|311980559146647151443968|164413911467589567760039952"
def inputClause4579 : CNF.NClause := [(35,false),(4,false),(63,true),(68,false),(73,false),(78,false),(83,true),(87,true)]
theorem inputList4579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4579 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4579 (by decide) v hb
mask_input "4579|311971335774610296668176|164413920690961604614815744"
def inputClause4580 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,false),(78,false),(83,true),(87,true)]
theorem inputList4580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4580 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4580 (by decide) v hb
mask_input "4580|311971335774610296668160|164413920690961604614815760"
def inputClause4581 : CNF.NClause := [(35,false),(4,false),(63,false),(68,true),(73,false),(78,false),(83,true),(87,true)]
theorem inputList4581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4581 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4581 (by decide) v hb
mask_input "4581|311685411241467798618128|164414206615494747112865792"
def inputClause4582 : CNF.NClause := [(35,false),(4,true),(63,false),(68,true),(73,false),(78,false),(83,true),(87,true)]
theorem inputList4582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4582 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4582 (by decide) v hb
mask_input "4582|311685411241467798618112|164414206615494747112865808"
def inputClause4583 : CNF.NClause := [(35,false),(4,false),(63,true),(68,true),(73,false),(78,false),(83,true),(87,true)]
theorem inputList4583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4583 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4583 (by decide) v hb
mask_input "4583|311676187869430943842320|164414215838866783967641600"
def inputClause4584 : CNF.NClause := [(35,false),(4,true),(63,true),(68,true),(73,false),(78,false),(83,true),(87,true)]
theorem inputList4584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4584 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4584 (by decide) v hb
mask_input "4584|311676187869430943842304|164414215838866783967641616"
def inputClause4585 : CNF.NClause := [(35,false),(4,false),(63,false),(68,false),(73,true),(78,false),(83,true),(87,true)]
theorem inputList4585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4585 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4585 (by decide) v hb
mask_input "4585|302535826180907861016592|164423356200555307050467328"
def inputClause4586 : CNF.NClause := [(35,false),(4,true),(63,false),(68,false),(73,true),(78,false),(83,true),(87,true)]
theorem inputList4586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4586 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4586 (by decide) v hb
mask_input "4586|302535826180907861016576|164423356200555307050467344"
def inputClause4587 : CNF.NClause := [(35,false),(4,false),(63,true),(68,false),(73,true),(78,false),(83,true),(87,true)]
theorem inputList4587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4587 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4587 (by decide) v hb
mask_input "4587|302526602808871006240784|164423365423927343905243136"
def inputClause4588 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,true),(78,false),(83,true),(87,true)]
theorem inputList4588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4588 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4588 (by decide) v hb
mask_input "4588|302526602808871006240768|164423365423927343905243152"
def inputClause4589 : CNF.NClause := [(35,false),(4,false),(63,false),(68,true),(73,true),(78,false),(83,true),(87,true)]
theorem inputList4589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4589 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4589 (by decide) v hb
mask_input "4589|302240678275728508190736|164423651348460486403293184"
def inputClause4590 : CNF.NClause := [(35,false),(4,true),(63,false),(68,true),(73,true),(78,false),(83,true),(87,true)]
theorem inputList4590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4590 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4590 (by decide) v hb
mask_input "4590|302240678275728508190720|164423651348460486403293200"
def inputClause4591 : CNF.NClause := [(35,false),(4,false),(63,true),(68,true),(73,true),(78,false),(83,true),(87,true)]
theorem inputList4591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4591 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4591 (by decide) v hb
mask_input "4591|302231454903691653414928|164423660571832523258068992"
def inputClause4592 : CNF.NClause := [(35,false),(4,true),(63,true),(68,true),(73,true),(78,false),(83,true),(87,true)]
theorem inputList4592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4592 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4592 (by decide) v hb
mask_input "4592|302231454903691653414912|164423660571832523258069008"
def inputClause4593 : CNF.NClause := [(35,false),(4,false),(63,false),(68,false),(73,false),(78,true),(83,true),(87,true)]
theorem inputList4593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4593 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4593 (by decide) v hb
mask_input "4593|9749104242989857767440|164716142922493225053716480"
def inputClause4594 : CNF.NClause := [(35,false),(4,true),(63,false),(68,false),(73,false),(78,true),(83,true),(87,true)]
theorem inputList4594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4594 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4594 (by decide) v hb
mask_input "4594|9749104242989857767424|164716142922493225053716496"
def inputClause4595 : CNF.NClause := [(35,false),(4,false),(63,true),(68,false),(73,false),(78,true),(83,true),(87,true)]
theorem inputList4595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4595 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4595 (by decide) v hb
mask_input "4595|9739880870953002991632|164716152145865261908492288"
def inputClause4596 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,false),(78,true),(83,true),(87,true)]
theorem inputList4596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4596 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4596 (by decide) v hb
mask_input "4596|9739880870953002991616|164716152145865261908492304"
def inputClause4597 : CNF.NClause := [(35,false),(4,false),(63,false),(68,true),(73,false),(78,true),(83,true),(87,true)]
theorem inputList4597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4597 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4597 (by decide) v hb
mask_input "4597|9453956337810504941584|164716438070398404406542336"
def inputClause4598 : CNF.NClause := [(35,false),(4,true),(63,false),(68,true),(73,false),(78,true),(83,true),(87,true)]
theorem inputList4598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4598 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4598 (by decide) v hb
mask_input "4598|9453956337810504941568|164716438070398404406542352"
def inputClause4599 : CNF.NClause := [(35,false),(4,false),(63,true),(68,true),(73,false),(78,true),(83,true),(87,true)]
theorem inputList4599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4599 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4599 (by decide) v hb
mask_input "4599|9444732965773650165776|164716447293770441261318144"
def inputClause4600 : CNF.NClause := [(35,false),(4,true),(63,true),(68,true),(73,false),(78,true),(83,true),(87,true)]
theorem inputList4600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4600 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4600 (by decide) v hb
mask_input "4600|9444732965773650165760|164716447293770441261318160"
def inputClause4601 : CNF.NClause := [(35,false),(4,false),(63,false),(68,false),(73,true),(78,true),(83,true),(87,true)]
theorem inputList4601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4601 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4601 (by decide) v hb
mask_input "4601|304371277250567340048|164725587655458964344143872"
def inputClause4602 : CNF.NClause := [(35,false),(4,true),(63,false),(68,false),(73,true),(78,true),(83,true),(87,true)]
theorem inputList4602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4602 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4602 (by decide) v hb
mask_input "4602|304371277250567340032|164725587655458964344143888"
def inputClause4603 : CNF.NClause := [(35,false),(4,false),(63,true),(68,false),(73,true),(78,true),(83,true),(87,true)]
theorem inputList4603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4603 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4603 (by decide) v hb
mask_input "4603|295147905213712564240|164725596878831001198919680"
def inputClause4604 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,true),(78,true),(83,true),(87,true)]
theorem inputList4604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4604 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4604 (by decide) v hb
mask_input "4604|295147905213712564224|164725596878831001198919696"
def inputClause4605 : CNF.NClause := [(35,false),(4,false),(63,false),(68,true),(73,true),(78,true),(83,true),(87,true)]
theorem inputList4605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4605 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 4) (spread_mem 4) inputClause4605 (by decide) v hb
mask_input "4605|9223372071214514192|164725882803364143696969728"
end Percolation.MaskChain
