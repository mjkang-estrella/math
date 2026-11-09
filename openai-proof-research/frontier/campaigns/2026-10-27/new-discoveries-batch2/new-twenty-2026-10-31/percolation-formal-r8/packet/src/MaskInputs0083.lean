import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause4755 : CNF.NClause := [(37,false),(6,false),(66,true),(70,false),(74,false),(78,true),(82,false),(91,false)]
theorem inputList4755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4755 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4755 (by decide) v hb
mask_input "4755|2480735851906771399928184896|302305241879952131883008"
def inputClause4756 : CNF.NClause := [(37,false),(6,true),(66,true),(70,false),(74,false),(78,true),(82,false),(91,false)]
theorem inputList4756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4756 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4756 (by decide) v hb
mask_input "4756|2480735851906771399928184832|302305241879952131883072"
def inputClause4757 : CNF.NClause := [(37,false),(6,false),(66,false),(70,true),(74,false),(78,true),(82,false),(91,false)]
theorem inputList4757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4757 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4757 (by decide) v hb
mask_input "4757|2480734745102126977355087936|303412046524374704979968"
def inputClause4758 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,false),(78,true),(82,false),(91,false)]
theorem inputList4758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4758 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4758 (by decide) v hb
mask_input "4758|2480734745102126977355087872|303412046524374704980032"
def inputClause4759 : CNF.NClause := [(37,false),(6,false),(66,true),(70,true),(74,false),(78,true),(82,false),(91,false)]
theorem inputList4759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4759 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4759 (by decide) v hb
mask_input "4759|2480734671315150682516881472|303485833500669543186432"
def inputClause4760 : CNF.NClause := [(37,false),(6,true),(66,true),(70,true),(74,false),(78,true),(82,false),(91,false)]
theorem inputList4760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4760 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4760 (by decide) v hb
mask_input "4760|2480734671315150682516881408|303485833500669543186496"
def inputClause4761 : CNF.NClause := [(37,false),(6,false),(66,false),(70,false),(74,true),(78,true),(82,false),(91,false)]
theorem inputList4761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4761 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4761 (by decide) v hb
mask_input "4761|2480717036227816216185536576|321120920835135874531328"
def inputClause4762 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,true),(78,true),(82,false),(91,false)]
theorem inputList4762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4762 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4762 (by decide) v hb
mask_input "4762|2480717036227816216185536512|321120920835135874531392"
def inputClause4763 : CNF.NClause := [(37,false),(6,false),(66,true),(70,false),(74,true),(78,true),(82,false),(91,false)]
theorem inputList4763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4763 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4763 (by decide) v hb
mask_input "4763|2480716962440839921347330112|321194707811430712737792"
def inputClause4764 : CNF.NClause := [(37,false),(6,true),(66,true),(70,false),(74,true),(78,true),(82,false),(91,false)]
theorem inputList4764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4764 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4764 (by decide) v hb
mask_input "4764|2480716962440839921347330048|321194707811430712737856"
def inputClause4765 : CNF.NClause := [(37,false),(6,false),(66,false),(70,true),(74,true),(78,true),(82,false),(91,false)]
theorem inputList4765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4765 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4765 (by decide) v hb
mask_input "4765|2480715855636195498774233152|322301512455853285834752"
def inputClause4766 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,true),(78,true),(82,false),(91,false)]
theorem inputList4766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4766 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4766 (by decide) v hb
mask_input "4766|2480715855636195498774233088|322301512455853285834816"
def inputClause4767 : CNF.NClause := [(37,false),(6,false),(66,true),(70,true),(74,true),(78,true),(82,false),(91,false)]
theorem inputList4767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4767 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4767 (by decide) v hb
mask_input "4767|2480715781849219203936026688|322375299432148124041216"
def inputClause4768 : CNF.NClause := [(37,false),(6,true),(66,true),(70,true),(74,true),(78,true),(82,false),(91,false)]
theorem inputList4768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4768 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4768 (by decide) v hb
mask_input "4768|2480715781849219203936026624|322375299432148124041280"
def inputClause4769 : CNF.NClause := [(37,false),(6,false),(66,false),(70,false),(74,false),(78,false),(82,true),(91,false)]
theorem inputList4769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4769 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4769 (by decide) v hb
mask_input "4769|2476202453870192835361243200|4835703278458516698824704"
def inputClause4770 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,false),(78,false),(82,true),(91,false)]
theorem inputList4770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4770 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4770 (by decide) v hb
mask_input "4770|2476202453870192835361243136|4835703278458516698824768"
def inputClause4771 : CNF.NClause := [(37,false),(6,false),(66,true),(70,false),(74,false),(78,false),(82,true),(91,false)]
theorem inputList4771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4771 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4771 (by decide) v hb
mask_input "4771|2476202380083216540523036736|4835777065434811537031168"
def inputClause4772 : CNF.NClause := [(37,false),(6,true),(66,true),(70,false),(74,false),(78,false),(82,true),(91,false)]
theorem inputList4772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4772 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4772 (by decide) v hb
mask_input "4772|2476202380083216540523036672|4835777065434811537031232"
def inputClause4773 : CNF.NClause := [(37,false),(6,false),(66,false),(70,true),(74,false),(78,false),(82,true),(91,false)]
theorem inputList4773 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4773 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4773 (by decide) v hb
mask_input "4773|2476201273278572117949939776|4836883870079234110128128"
def inputClause4774 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,false),(78,false),(82,true),(91,false)]
theorem inputList4774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4774 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4774 (by decide) v hb
mask_input "4774|2476201273278572117949939712|4836883870079234110128192"
def inputClause4775 : CNF.NClause := [(37,false),(6,false),(66,true),(70,true),(74,false),(78,false),(82,true),(91,false)]
theorem inputList4775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4775 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4775 (by decide) v hb
mask_input "4775|2476201199491595823111733312|4836957657055528948334592"
def inputClause4776 : CNF.NClause := [(37,false),(6,true),(66,true),(70,true),(74,false),(78,false),(82,true),(91,false)]
theorem inputList4776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4776 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4776 (by decide) v hb
mask_input "4776|2476201199491595823111733248|4836957657055528948334656"
def inputClause4777 : CNF.NClause := [(37,false),(6,false),(66,false),(70,false),(74,true),(78,false),(82,true),(91,false)]
theorem inputList4777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4777 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4777 (by decide) v hb
mask_input "4777|2476183564404261356780388416|4854592744389995279679488"
def inputClause4778 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,true),(78,false),(82,true),(91,false)]
theorem inputList4778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4778 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4778 (by decide) v hb
mask_input "4778|2476183564404261356780388352|4854592744389995279679552"
def inputClause4779 : CNF.NClause := [(37,false),(6,false),(66,true),(70,false),(74,true),(78,false),(82,true),(91,false)]
theorem inputList4779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4779 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4779 (by decide) v hb
mask_input "4779|2476183490617285061942181952|4854666531366290117885952"
def inputClause4780 : CNF.NClause := [(37,false),(6,true),(66,true),(70,false),(74,true),(78,false),(82,true),(91,false)]
theorem inputList4780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4780 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4780 (by decide) v hb
mask_input "4780|2476183490617285061942181888|4854666531366290117886016"
def inputClause4781 : CNF.NClause := [(37,false),(6,false),(66,false),(70,true),(74,true),(78,false),(82,true),(91,false)]
theorem inputList4781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4781 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4781 (by decide) v hb
mask_input "4781|2476182383812640639369084992|4855773336010712690982912"
def inputClause4782 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,true),(78,false),(82,true),(91,false)]
theorem inputList4782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4782 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4782 (by decide) v hb
mask_input "4782|2476182383812640639369084928|4855773336010712690982976"
def inputClause4783 : CNF.NClause := [(37,false),(6,false),(66,true),(70,true),(74,true),(78,false),(82,true),(91,false)]
theorem inputList4783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4783 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4783 (by decide) v hb
mask_input "4783|2476182310025664344530878528|4855847122987007529189376"
def inputClause4784 : CNF.NClause := [(37,false),(6,true),(66,true),(70,true),(74,true),(78,false),(82,true),(91,false)]
theorem inputList4784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4784 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4784 (by decide) v hb
mask_input "4784|2476182310025664344530878464|4855847122987007529189440"
def inputClause4785 : CNF.NClause := [(37,false),(6,false),(66,false),(70,false),(74,false),(78,true),(82,true),(91,false)]
theorem inputList4785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4785 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4785 (by decide) v hb
mask_input "4785|2475900222415289178067566656|5137934733362173992501248"
def inputClause4786 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,false),(78,true),(82,true),(91,false)]
theorem inputList4786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4786 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4786 (by decide) v hb
mask_input "4786|2475900222415289178067566592|5137934733362173992501312"
def inputClause4787 : CNF.NClause := [(37,false),(6,false),(66,true),(70,false),(74,false),(78,true),(82,true),(91,false)]
theorem inputList4787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4787 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4787 (by decide) v hb
mask_input "4787|2475900148628312883229360192|5138008520338468830707712"
def inputClause4788 : CNF.NClause := [(37,false),(6,true),(66,true),(70,false),(74,false),(78,true),(82,true),(91,false)]
theorem inputList4788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4788 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4788 (by decide) v hb
mask_input "4788|2475900148628312883229360128|5138008520338468830707776"
def inputClause4789 : CNF.NClause := [(37,false),(6,false),(66,false),(70,true),(74,false),(78,true),(82,true),(91,false)]
theorem inputList4789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4789 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4789 (by decide) v hb
mask_input "4789|2475899041823668460656263232|5139115324982891403804672"
def inputClause4790 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,false),(78,true),(82,true),(91,false)]
theorem inputList4790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4790 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4790 (by decide) v hb
mask_input "4790|2475899041823668460656263168|5139115324982891403804736"
def inputClause4791 : CNF.NClause := [(37,false),(6,false),(66,true),(70,true),(74,false),(78,true),(82,true),(91,false)]
theorem inputList4791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4791 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4791 (by decide) v hb
mask_input "4791|2475898968036692165818056768|5139189111959186242011136"
def inputClause4792 : CNF.NClause := [(37,false),(6,true),(66,true),(70,true),(74,false),(78,true),(82,true),(91,false)]
theorem inputList4792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4792 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4792 (by decide) v hb
mask_input "4792|2475898968036692165818056704|5139189111959186242011200"
def inputClause4793 : CNF.NClause := [(37,false),(6,false),(66,false),(70,false),(74,true),(78,true),(82,true),(91,false)]
theorem inputList4793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4793 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4793 (by decide) v hb
mask_input "4793|2475881332949357699486711872|5156824199293652573356032"
def inputClause4794 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,true),(78,true),(82,true),(91,false)]
theorem inputList4794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4794 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4794 (by decide) v hb
mask_input "4794|2475881332949357699486711808|5156824199293652573356096"
end Percolation.MaskChain
