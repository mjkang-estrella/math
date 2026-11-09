import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause6597 : CNF.NClause := [(51,false),(20,false),(67,false),(68,true),(69,false),(70,false),(71,false),(92,true)]
theorem inputList6597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6597 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6597 (by decide) v hb
mask_input "6597|4279646876900430708736|4951760452289426278949322752"
def inputClause6598 : CNF.NClause := [(51,false),(20,true),(67,false),(68,true),(69,false),(70,false),(71,false),(92,true)]
theorem inputList6598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6598 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6598 (by decide) v hb
mask_input "6598|4279646876900429660160|4951760452289426278950371328"
def inputClause6599 : CNF.NClause := [(51,false),(20,false),(67,true),(68,true),(69,false),(70,false),(71,false),(92,true)]
theorem inputList6599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6599 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6599 (by decide) v hb
mask_input "6599|4132072924310754295808|4951760599863378868625735680"
def inputClause6600 : CNF.NClause := [(51,false),(20,true),(67,true),(68,true),(69,false),(70,false),(71,false),(92,true)]
theorem inputList6600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6600 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6600 (by decide) v hb
mask_input "6600|4132072924310753247232|4951760599863378868626784256"
def inputClause6601 : CNF.NClause := [(51,false),(20,false),(67,false),(68,false),(69,true),(70,false),(71,false),(92,true)]
theorem inputList6601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6601 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6601 (by decide) v hb
mask_input "6601|3984498971721077882880|4951760747437331458302148608"
def inputClause6602 : CNF.NClause := [(51,false),(20,true),(67,false),(68,false),(69,true),(70,false),(71,false),(92,true)]
theorem inputList6602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6602 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6602 (by decide) v hb
mask_input "6602|3984498971721076834304|4951760747437331458303197184"
def inputClause6603 : CNF.NClause := [(51,false),(20,false),(67,true),(68,false),(69,true),(70,false),(71,false),(92,true)]
theorem inputList6603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6603 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6603 (by decide) v hb
mask_input "6603|3836925019131401469952|4951760895011284047978561536"
def inputClause6604 : CNF.NClause := [(51,false),(20,true),(67,true),(68,false),(69,true),(70,false),(71,false),(92,true)]
theorem inputList6604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6604 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6604 (by decide) v hb
mask_input "6604|3836925019131400421376|4951760895011284047979610112"
def inputClause6605 : CNF.NClause := [(51,false),(20,false),(67,false),(68,true),(69,true),(70,false),(71,false),(92,true)]
theorem inputList6605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6605 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6605 (by decide) v hb
mask_input "6605|3689351066541725057024|4951761042585236637654974464"
def inputClause6606 : CNF.NClause := [(51,false),(20,true),(67,false),(68,true),(69,true),(70,false),(71,false),(92,true)]
theorem inputList6606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6606 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6606 (by decide) v hb
mask_input "6606|3689351066541724008448|4951761042585236637656023040"
def inputClause6607 : CNF.NClause := [(51,false),(20,false),(67,true),(68,true),(69,true),(70,false),(71,false),(92,true)]
theorem inputList6607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6607 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6607 (by decide) v hb
mask_input "6607|3541777113952048644096|4951761190159189227331387392"
def inputClause6608 : CNF.NClause := [(51,false),(20,true),(67,true),(68,true),(69,true),(70,false),(71,false),(92,true)]
theorem inputList6608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6608 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6608 (by decide) v hb
mask_input "6608|3541777113952047595520|4951761190159189227332435968"
def inputClause6609 : CNF.NClause := [(51,false),(20,false),(67,false),(68,false),(69,false),(70,true),(71,false),(92,true)]
theorem inputList6609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6609 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6609 (by decide) v hb
mask_input "6609|3394203161362372231168|4951761337733141817007800320"
def inputClause6610 : CNF.NClause := [(51,false),(20,true),(67,false),(68,false),(69,false),(70,true),(71,false),(92,true)]
theorem inputList6610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6610 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6610 (by decide) v hb
mask_input "6610|3394203161362371182592|4951761337733141817008848896"
def inputClause6611 : CNF.NClause := [(51,false),(20,false),(67,true),(68,false),(69,false),(70,true),(71,false),(92,true)]
theorem inputList6611 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6611 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6611 (by decide) v hb
mask_input "6611|3246629208772695818240|4951761485307094406684213248"
def inputClause6612 : CNF.NClause := [(51,false),(20,true),(67,true),(68,false),(69,false),(70,true),(71,false),(92,true)]
theorem inputList6612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6612 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6612 (by decide) v hb
mask_input "6612|3246629208772694769664|4951761485307094406685261824"
def inputClause6613 : CNF.NClause := [(51,false),(20,false),(67,false),(68,true),(69,false),(70,true),(71,false),(92,true)]
theorem inputList6613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6613 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6613 (by decide) v hb
mask_input "6613|3099055256183019405312|4951761632881046996360626176"
def inputClause6614 : CNF.NClause := [(51,false),(20,true),(67,false),(68,true),(69,false),(70,true),(71,false),(92,true)]
theorem inputList6614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6614 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6614 (by decide) v hb
mask_input "6614|3099055256183018356736|4951761632881046996361674752"
def inputClause6615 : CNF.NClause := [(51,false),(20,false),(67,true),(68,true),(69,false),(70,true),(71,false),(92,true)]
theorem inputList6615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6615 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6615 (by decide) v hb
mask_input "6615|2951481303593342992384|4951761780454999586037039104"
def inputClause6616 : CNF.NClause := [(51,false),(20,true),(67,true),(68,true),(69,false),(70,true),(71,false),(92,true)]
theorem inputList6616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6616 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6616 (by decide) v hb
mask_input "6616|2951481303593341943808|4951761780454999586038087680"
def inputClause6617 : CNF.NClause := [(51,false),(20,false),(67,false),(68,false),(69,true),(70,true),(71,false),(92,true)]
theorem inputList6617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6617 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6617 (by decide) v hb
mask_input "6617|2803907351003666579456|4951761928028952175713452032"
def inputClause6618 : CNF.NClause := [(51,false),(20,true),(67,false),(68,false),(69,true),(70,true),(71,false),(92,true)]
theorem inputList6618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6618 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6618 (by decide) v hb
mask_input "6618|2803907351003665530880|4951761928028952175714500608"
def inputClause6619 : CNF.NClause := [(51,false),(20,false),(67,true),(68,false),(69,true),(70,true),(71,false),(92,true)]
theorem inputList6619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6619 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6619 (by decide) v hb
mask_input "6619|2656333398413990166528|4951762075602904765389864960"
def inputClause6620 : CNF.NClause := [(51,false),(20,true),(67,true),(68,false),(69,true),(70,true),(71,false),(92,true)]
theorem inputList6620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6620 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6620 (by decide) v hb
mask_input "6620|2656333398413989117952|4951762075602904765390913536"
def inputClause6621 : CNF.NClause := [(51,false),(20,false),(67,false),(68,true),(69,true),(70,true),(71,false),(92,true)]
theorem inputList6621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6621 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6621 (by decide) v hb
mask_input "6621|2508759445824313753600|4951762223176857355066277888"
def inputClause6622 : CNF.NClause := [(51,false),(20,true),(67,false),(68,true),(69,true),(70,true),(71,false),(92,true)]
theorem inputList6622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6622 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6622 (by decide) v hb
mask_input "6622|2508759445824312705024|4951762223176857355067326464"
def inputClause6623 : CNF.NClause := [(51,false),(20,false),(67,true),(68,true),(69,true),(70,true),(71,false),(92,true)]
theorem inputList6623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6623 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6623 (by decide) v hb
mask_input "6623|2361185493234637340672|4951762370750809944742690816"
def inputClause6624 : CNF.NClause := [(51,false),(20,true),(67,true),(68,true),(69,true),(70,true),(71,false),(92,true)]
theorem inputList6624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6624 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6624 (by decide) v hb
mask_input "6624|2361185493234636292096|4951762370750809944743739392"
def inputClause6625 : CNF.NClause := [(51,false),(20,false),(67,false),(68,false),(69,false),(70,false),(71,true),(92,true)]
theorem inputList6625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6625 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6625 (by decide) v hb
mask_input "6625|2213611540644960927744|4951762518324762534419103744"
def inputClause6626 : CNF.NClause := [(51,false),(20,true),(67,false),(68,false),(69,false),(70,false),(71,true),(92,true)]
theorem inputList6626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6626 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6626 (by decide) v hb
mask_input "6626|2213611540644959879168|4951762518324762534420152320"
def inputClause6627 : CNF.NClause := [(51,false),(20,false),(67,true),(68,false),(69,false),(70,false),(71,true),(92,true)]
theorem inputList6627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6627 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6627 (by decide) v hb
mask_input "6627|2066037588055284514816|4951762665898715124095516672"
def inputClause6628 : CNF.NClause := [(51,false),(20,true),(67,true),(68,false),(69,false),(70,false),(71,true),(92,true)]
theorem inputList6628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6628 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6628 (by decide) v hb
mask_input "6628|2066037588055283466240|4951762665898715124096565248"
def inputClause6630 : CNF.NClause := [(51,false),(20,true),(67,false),(68,true),(69,false),(70,false),(71,true),(92,true)]
theorem inputList6630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6630 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6630 (by decide) v hb
mask_input "6630|1918463635465607053312|4951762813472667713772978176"
def inputClause6631 : CNF.NClause := [(51,false),(20,false),(67,true),(68,true),(69,false),(70,false),(71,true),(92,true)]
theorem inputList6631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6631 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6631 (by decide) v hb
mask_input "6631|1770889682875931688960|4951762961046620303448342528"
def inputClause6632 : CNF.NClause := [(51,false),(20,true),(67,true),(68,true),(69,false),(70,false),(71,true),(92,true)]
theorem inputList6632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6632 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6632 (by decide) v hb
mask_input "6632|1770889682875930640384|4951762961046620303449391104"
def inputClause6633 : CNF.NClause := [(51,false),(20,false),(67,false),(68,false),(69,true),(70,false),(71,true),(92,true)]
theorem inputList6633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6633 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6633 (by decide) v hb
mask_input "6633|1623315730286255276032|4951763108620572893124755456"
def inputClause6634 : CNF.NClause := [(51,false),(20,true),(67,false),(68,false),(69,true),(70,false),(71,true),(92,true)]
theorem inputList6634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6634 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6634 (by decide) v hb
mask_input "6634|1623315730286254227456|4951763108620572893125804032"
def inputClause6635 : CNF.NClause := [(51,false),(20,false),(67,true),(68,false),(69,true),(70,false),(71,true),(92,true)]
theorem inputList6635 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6635 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6635 (by decide) v hb
mask_input "6635|1475741777696578863104|4951763256194525482801168384"
def inputClause6636 : CNF.NClause := [(51,false),(20,true),(67,true),(68,false),(69,true),(70,false),(71,true),(92,true)]
theorem inputList6636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6636 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6636 (by decide) v hb
mask_input "6636|1475741777696577814528|4951763256194525482802216960"
def inputClause6637 : CNF.NClause := [(51,false),(20,false),(67,false),(68,true),(69,true),(70,false),(71,true),(92,true)]
theorem inputList6637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6637 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 20) (spread_mem 20) inputClause6637 (by decide) v hb
mask_input "6637|1328167825106902450176|4951763403768478072477581312"
end Percolation.MaskChain
