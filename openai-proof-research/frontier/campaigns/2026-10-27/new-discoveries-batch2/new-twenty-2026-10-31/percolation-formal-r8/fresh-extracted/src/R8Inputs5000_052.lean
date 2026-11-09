import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause6638 : CNF.NClause := [(51,false),(20,true),(67,false),(68,true),(69,true),(70,false),(71,true),(92,true)]
theorem inputList6638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6638 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6638 (by decide) v hb
mask_input "6638|1328167825106901401600|4951763403768478072478629888"
def inputClause6640 : CNF.NClause := [(51,false),(20,true),(67,true),(68,true),(69,true),(70,false),(71,true),(92,true)]
theorem inputList6640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6640 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6640 (by decide) v hb
mask_input "6640|1180593872517224988672|4951763551342430662155042816"
def inputClause6641 : CNF.NClause := [(51,false),(20,false),(67,false),(68,false),(69,false),(70,true),(71,true),(92,true)]
theorem inputList6641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6641 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6641 (by decide) v hb
mask_input "6641|1033019919927549624320|4951763698916383251830407168"
def inputClause6642 : CNF.NClause := [(51,false),(20,true),(67,false),(68,false),(69,false),(70,true),(71,true),(92,true)]
theorem inputList6642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6642 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6642 (by decide) v hb
mask_input "6642|1033019919927548575744|4951763698916383251831455744"
def inputClause6643 : CNF.NClause := [(51,false),(20,false),(67,true),(68,false),(69,false),(70,true),(71,true),(92,true)]
theorem inputList6643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6643 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6643 (by decide) v hb
mask_input "6643|885445967337873211392|4951763846490335841506820096"
def inputClause6644 : CNF.NClause := [(51,false),(20,true),(67,true),(68,false),(69,false),(70,true),(71,true),(92,true)]
theorem inputList6644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6644 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6644 (by decide) v hb
mask_input "6644|885445967337872162816|4951763846490335841507868672"
def inputClause6646 : CNF.NClause := [(51,false),(20,true),(67,false),(68,true),(69,false),(70,true),(71,true),(92,true)]
theorem inputList6646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6646 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6646 (by decide) v hb
mask_input "6646|737872014748195749888|4951763994064288431184281600"
def inputClause6648 : CNF.NClause := [(51,false),(20,true),(67,true),(68,true),(69,false),(70,true),(71,true),(92,true)]
theorem inputList6648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6648 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6648 (by decide) v hb
mask_input "6648|590298062158519336960|4951764141638241020860694528"
def inputClause6649 : CNF.NClause := [(51,false),(20,false),(67,false),(68,false),(69,true),(70,true),(71,true),(92,true)]
theorem inputList6649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6649 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6649 (by decide) v hb
mask_input "6649|442724109568843972608|4951764289212193610536058880"
def inputClause6650 : CNF.NClause := [(51,false),(20,true),(67,false),(68,false),(69,true),(70,true),(71,true),(92,true)]
theorem inputList6650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6650 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6650 (by decide) v hb
mask_input "6650|442724109568842924032|4951764289212193610537107456"
def inputClause6651 : CNF.NClause := [(51,false),(20,false),(67,true),(68,false),(69,true),(70,true),(71,true),(92,true)]
theorem inputList6651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6651 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6651 (by decide) v hb
mask_input "6651|295150156979167559680|4951764436786146200212471808"
def inputClause6652 : CNF.NClause := [(51,false),(20,true),(67,true),(68,false),(69,true),(70,true),(71,true),(92,true)]
theorem inputList6652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6652 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6652 (by decide) v hb
mask_input "6652|295150156979166511104|4951764436786146200213520384"
def inputClause6653 : CNF.NClause := [(51,false),(20,false),(67,false),(68,true),(69,true),(70,true),(71,true),(92,true)]
theorem inputList6653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6653 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6653 (by decide) v hb
mask_input "6653|147576204389491146752|4951764584360098789888884736"
def inputClause6654 : CNF.NClause := [(51,false),(20,true),(67,false),(68,true),(69,true),(70,true),(71,true),(92,true)]
theorem inputList6654 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6654 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6654 (by decide) v hb
mask_input "6654|147576204389490098176|4951764584360098789889933312"
def inputClause6655 : CNF.NClause := [(51,false),(20,false),(67,true),(68,true),(69,true),(70,true),(71,true),(92,true)]
theorem inputList6655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6655 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6655 (by decide) v hb
mask_input "6655|2251799814733824|4951764731934051379565297664"
def inputClause6656 : CNF.NClause := [(51,false),(20,true),(67,true),(68,true),(69,true),(70,true),(71,true),(92,true)]
theorem inputList6656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6656 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6656 (by decide) v hb
mask_input "6656|2251799813685248|4951764731934051379566346240"
def inputClause6657 : CNF.NClause := [(52,true),(21,false),(66,false),(67,false),(73,false),(79,false),(85,false),(88,false)]
theorem inputList6657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6657 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6657 (by decide) v hb
mask_input "6657|348784765052715140709875712|4503599627370496"
def inputClause6659 : CNF.NClause := [(52,false),(21,false),(66,true),(67,false),(73,false),(79,false),(85,false),(88,false)]
theorem inputList6659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6659 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6659 (by decide) v hb
mask_input "6659|348784691270242445499039744|73786976294838206464"
def inputClause6660 : CNF.NClause := [(52,false),(21,true),(66,true),(67,false),(73,false),(79,false),(85,false),(88,false)]
theorem inputList6660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6660 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6660 (by decide) v hb
mask_input "6660|348784691270242445496942592|73786976294840303616"
def inputClause6661 : CNF.NClause := [(52,false),(21,false),(66,false),(67,true),(73,false),(79,false),(85,false),(88,false)]
theorem inputList6661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6661 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6661 (by decide) v hb
mask_input "6661|348784617483266150660833280|147573952589676412928"
def inputClause6663 : CNF.NClause := [(52,false),(21,false),(66,true),(67,true),(73,false),(79,false),(85,false),(88,false)]
theorem inputList6663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6663 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6663 (by decide) v hb
mask_input "6663|348784543696289855822626816|221360928884514619392"
def inputClause6664 : CNF.NClause := [(52,false),(21,true),(66,true),(67,true),(73,false),(79,false),(85,false),(88,false)]
theorem inputList6664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6664 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6664 (by decide) v hb
mask_input "6664|348784543696289855820529664|221360928884516716544"
def inputClause6665 : CNF.NClause := [(52,false),(21,false),(66,false),(67,false),(73,true),(79,false),(85,false),(88,false)]
theorem inputList6665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6665 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6665 (by decide) v hb
mask_input "6665|348775320324253001046818816|9444732965739290427392"
def inputClause6666 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,true),(79,false),(85,false),(88,false)]
theorem inputList6666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6666 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6666 (by decide) v hb
mask_input "6666|348775320324253001044721664|9444732965739292524544"
def inputClause6667 : CNF.NClause := [(52,false),(21,false),(66,true),(67,false),(73,true),(79,false),(85,false),(88,false)]
theorem inputList6667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6667 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6667 (by decide) v hb
mask_input "6667|348775246537276706208612352|9518519942034128633856"
def inputClause6668 : CNF.NClause := [(52,false),(21,true),(66,true),(67,false),(73,true),(79,false),(85,false),(88,false)]
theorem inputList6668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6668 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6668 (by decide) v hb
mask_input "6668|348775246537276706206515200|9518519942034130731008"
def inputClause6669 : CNF.NClause := [(52,false),(21,false),(66,false),(67,true),(73,true),(79,false),(85,false),(88,false)]
theorem inputList6669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6669 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6669 (by decide) v hb
mask_input "6669|348775172750300411370405888|9592306918328966840320"
def inputClause6671 : CNF.NClause := [(52,false),(21,false),(66,true),(67,true),(73,true),(79,false),(85,false),(88,false)]
theorem inputList6671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6671 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6671 (by decide) v hb
mask_input "6671|348775098963324116532199424|9666093894623805046784"
def inputClause6672 : CNF.NClause := [(52,false),(21,true),(66,true),(67,true),(73,true),(79,false),(85,false),(88,false)]
theorem inputList6672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6672 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6672 (by decide) v hb
mask_input "6672|348775098963324116530102272|9666093894623807143936"
def inputClause6673 : CNF.NClause := [(52,false),(21,false),(66,false),(67,false),(73,false),(79,true),(85,false),(88,false)]
theorem inputList6673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6673 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6673 (by decide) v hb
mask_input "6673|348180302147411425749893120|604462909807314587353088"
def inputClause6674 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,false),(79,true),(85,false),(88,false)]
theorem inputList6674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6674 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6674 (by decide) v hb
mask_input "6674|348180302147411425747795968|604462909807314589450240"
def inputClause6675 : CNF.NClause := [(52,false),(21,false),(66,true),(67,false),(73,false),(79,true),(85,false),(88,false)]
theorem inputList6675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6675 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6675 (by decide) v hb
mask_input "6675|348180228360435130911686656|604536696783609425559552"
def inputClause6676 : CNF.NClause := [(52,false),(21,true),(66,true),(67,false),(73,false),(79,true),(85,false),(88,false)]
theorem inputList6676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6676 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6676 (by decide) v hb
mask_input "6676|348180228360435130909589504|604536696783609427656704"
def inputClause6677 : CNF.NClause := [(52,false),(21,false),(66,false),(67,true),(73,false),(79,true),(85,false),(88,false)]
theorem inputList6677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6677 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6677 (by decide) v hb
mask_input "6677|348180154573458836073480192|604610483759904263766016"
def inputClause6679 : CNF.NClause := [(52,false),(21,false),(66,true),(67,true),(73,false),(79,true),(85,false),(88,false)]
theorem inputList6679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6679 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6679 (by decide) v hb
mask_input "6679|348180080786482541235273728|604684270736199101972480"
def inputClause6680 : CNF.NClause := [(52,false),(21,true),(66,true),(67,true),(73,false),(79,true),(85,false),(88,false)]
theorem inputList6680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6680 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6680 (by decide) v hb
mask_input "6680|348180080786482541233176576|604684270736199104069632"
def inputClause6681 : CNF.NClause := [(52,false),(21,false),(66,false),(67,false),(73,true),(79,true),(85,false),(88,false)]
theorem inputList6681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6681 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6681 (by decide) v hb
mask_input "6681|348170857414445686459465728|613907642773053877780480"
def inputClause6682 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,true),(79,true),(85,false),(88,false)]
theorem inputList6682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6682 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6682 (by decide) v hb
mask_input "6682|348170857414445686457368576|613907642773053879877632"
def inputClause6683 : CNF.NClause := [(52,false),(21,false),(66,true),(67,false),(73,true),(79,true),(85,false),(88,false)]
theorem inputList6683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6683 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6683 (by decide) v hb
mask_input "6683|348170783627469391621259264|613981429749348715986944"
def inputClause6684 : CNF.NClause := [(52,false),(21,true),(66,true),(67,false),(73,true),(79,true),(85,false),(88,false)]
theorem inputList6684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6684 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6684 (by decide) v hb
mask_input "6684|348170783627469391619162112|613981429749348718084096"
end Percolation.MaskChain
