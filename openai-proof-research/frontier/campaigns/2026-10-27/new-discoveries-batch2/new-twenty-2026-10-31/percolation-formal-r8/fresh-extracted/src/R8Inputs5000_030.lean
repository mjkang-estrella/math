import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause5649 : CNF.NClause := [(44,false),(13,false),(65,false),(71,false),(72,false),(78,true),(84,false),(88,false)]
theorem inputList5649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5649 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5649 (by decide) v hb
mask_input "5649|328834943378409179593056256|302231454903657293676544"
def inputClause5651 : CNF.NClause := [(44,false),(13,false),(65,true),(71,false),(72,false),(78,true),(84,false),(88,false)]
theorem inputList5651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5651 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5651 (by decide) v hb
mask_input "5651|328834906484921032173953024|302268348391804712779776"
def inputClause5652 : CNF.NClause := [(44,false),(13,true),(65,true),(71,false),(72,false),(78,true),(84,false),(88,false)]
theorem inputList5652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5652 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5652 (by decide) v hb
mask_input "5652|328834906484921032173944832|302268348391804712787968"
def inputClause5653 : CNF.NClause := [(44,false),(13,false),(65,false),(71,true),(72,false),(78,true),(84,false),(88,false)]
theorem inputList5653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5653 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5653 (by decide) v hb
mask_input "5653|328832582195167744770449408|304592638145092116283392"
def inputClause5654 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,false),(78,true),(84,false),(88,false)]
theorem inputList5654 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5654 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5654 (by decide) v hb
mask_input "5654|328832582195167744770441216|304592638145092116291584"
def inputClause5655 : CNF.NClause := [(44,false),(13,false),(65,true),(71,true),(72,false),(78,true),(84,false),(88,false)]
theorem inputList5655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5655 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5655 (by decide) v hb
mask_input "5655|328832545301679597351346176|304629531633239535386624"
def inputClause5656 : CNF.NClause := [(44,false),(13,true),(65,true),(71,true),(72,false),(78,true),(84,false),(88,false)]
theorem inputList5656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5656 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5656 (by decide) v hb
mask_input "5656|328832545301679597351337984|304629531633239535394816"
def inputClause5657 : CNF.NClause := [(44,false),(13,false),(65,false),(71,false),(72,true),(78,true),(84,false),(88,false)]
theorem inputList5657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5657 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5657 (by decide) v hb
mask_input "5657|328830221011926309947842560|306953821386526938890240"
def inputClause5658 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,true),(78,true),(84,false),(88,false)]
theorem inputList5658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5658 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5658 (by decide) v hb
mask_input "5658|328830221011926309947834368|306953821386526938898432"
def inputClause5659 : CNF.NClause := [(44,false),(13,false),(65,true),(71,false),(72,true),(78,true),(84,false),(88,false)]
theorem inputList5659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5659 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5659 (by decide) v hb
mask_input "5659|328830184118438162528739328|306990714874674357993472"
def inputClause5660 : CNF.NClause := [(44,false),(13,true),(65,true),(71,false),(72,true),(78,true),(84,false),(88,false)]
theorem inputList5660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5660 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5660 (by decide) v hb
mask_input "5660|328830184118438162528731136|306990714874674358001664"
def inputClause5661 : CNF.NClause := [(44,false),(13,false),(65,false),(71,true),(72,true),(78,true),(84,false),(88,false)]
theorem inputList5661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5661 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5661 (by decide) v hb
mask_input "5661|328827859828684875125235712|309315004627961761497088"
def inputClause5662 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,true),(78,true),(84,false),(88,false)]
theorem inputList5662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5662 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5662 (by decide) v hb
mask_input "5662|328827859828684875125227520|309315004627961761505280"
def inputClause5663 : CNF.NClause := [(44,false),(13,false),(65,true),(71,true),(72,true),(78,true),(84,false),(88,false)]
theorem inputList5663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5663 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5663 (by decide) v hb
mask_input "5663|328827822935196727706132480|309351898116109180600320"
def inputClause5664 : CNF.NClause := [(44,false),(13,true),(65,true),(71,true),(72,true),(78,true),(84,false),(88,false)]
theorem inputList5664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5664 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5664 (by decide) v hb
mask_input "5664|328827822935196727706124288|309351898116109180608512"
def inputClause5665 : CNF.NClause := [(44,false),(13,false),(65,false),(71,false),(72,false),(78,false),(84,true),(88,false)]
theorem inputList5665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5665 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5665 (by decide) v hb
mask_input "5665|309794361719478770091433984|19342813113834066795298816"
def inputClause5667 : CNF.NClause := [(44,false),(13,false),(65,true),(71,false),(72,false),(78,false),(84,true),(88,false)]
theorem inputList5667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5667 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5667 (by decide) v hb
mask_input "5667|309794324825990622672330752|19342850007322214214402048"
def inputClause5668 : CNF.NClause := [(44,false),(13,true),(65,true),(71,false),(72,false),(78,false),(84,true),(88,false)]
theorem inputList5668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5668 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5668 (by decide) v hb
mask_input "5668|309794324825990622672322560|19342850007322214214410240"
def inputClause5669 : CNF.NClause := [(44,false),(13,false),(65,false),(71,true),(72,false),(78,false),(84,true),(88,false)]
theorem inputList5669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5669 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5669 (by decide) v hb
mask_input "5669|309792000536237335268827136|19345174297075501617905664"
def inputClause5670 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,false),(78,false),(84,true),(88,false)]
theorem inputList5670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5670 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5670 (by decide) v hb
mask_input "5670|309792000536237335268818944|19345174297075501617913856"
def inputClause5671 : CNF.NClause := [(44,false),(13,false),(65,true),(71,true),(72,false),(78,false),(84,true),(88,false)]
theorem inputList5671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5671 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5671 (by decide) v hb
mask_input "5671|309791963642749187849723904|19345211190563649037008896"
def inputClause5672 : CNF.NClause := [(44,false),(13,true),(65,true),(71,true),(72,false),(78,false),(84,true),(88,false)]
theorem inputList5672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5672 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5672 (by decide) v hb
mask_input "5672|309791963642749187849715712|19345211190563649037017088"
def inputClause5673 : CNF.NClause := [(44,false),(13,false),(65,false),(71,false),(72,true),(78,false),(84,true),(88,false)]
theorem inputList5673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5673 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5673 (by decide) v hb
mask_input "5673|309789639352995900446220288|19347535480316936440512512"
def inputClause5674 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,true),(78,false),(84,true),(88,false)]
theorem inputList5674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5674 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5674 (by decide) v hb
mask_input "5674|309789639352995900446212096|19347535480316936440520704"
def inputClause5675 : CNF.NClause := [(44,false),(13,false),(65,true),(71,false),(72,true),(78,false),(84,true),(88,false)]
theorem inputList5675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5675 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5675 (by decide) v hb
mask_input "5675|309789602459507753027117056|19347572373805083859615744"
def inputClause5676 : CNF.NClause := [(44,false),(13,true),(65,true),(71,false),(72,true),(78,false),(84,true),(88,false)]
theorem inputList5676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5676 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5676 (by decide) v hb
mask_input "5676|309789602459507753027108864|19347572373805083859623936"
def inputClause5677 : CNF.NClause := [(44,false),(13,false),(65,false),(71,true),(72,true),(78,false),(84,true),(88,false)]
theorem inputList5677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5677 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5677 (by decide) v hb
mask_input "5677|309787278169754465623613440|19349896663558371263119360"
def inputClause5678 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,true),(78,false),(84,true),(88,false)]
theorem inputList5678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5678 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5678 (by decide) v hb
mask_input "5678|309787278169754465623605248|19349896663558371263127552"
def inputClause5679 : CNF.NClause := [(44,false),(13,false),(65,true),(71,true),(72,true),(78,false),(84,true),(88,false)]
theorem inputList5679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5679 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5679 (by decide) v hb
mask_input "5679|309787241276266318204510208|19349933557046518682222592"
def inputClause5680 : CNF.NClause := [(44,false),(13,true),(65,true),(71,true),(72,true),(78,false),(84,true),(88,false)]
theorem inputList5680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5680 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5680 (by decide) v hb
mask_input "5680|309787241276266318204502016|19349933557046518682230784"
def inputClause5681 : CNF.NClause := [(44,false),(13,false),(65,false),(71,false),(72,false),(78,true),(84,true),(88,false)]
theorem inputList5681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5681 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5681 (by decide) v hb
mask_input "5681|309492130264575112797757440|19645044568737724088975360"
def inputClause5683 : CNF.NClause := [(44,false),(13,false),(65,true),(71,false),(72,false),(78,true),(84,true),(88,false)]
theorem inputList5683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5683 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5683 (by decide) v hb
mask_input "5683|309492093371086965378654208|19645081462225871508078592"
def inputClause5684 : CNF.NClause := [(44,false),(13,true),(65,true),(71,false),(72,false),(78,true),(84,true),(88,false)]
theorem inputList5684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5684 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5684 (by decide) v hb
mask_input "5684|309492093371086965378646016|19645081462225871508086784"
def inputClause5685 : CNF.NClause := [(44,false),(13,false),(65,false),(71,true),(72,false),(78,true),(84,true),(88,false)]
theorem inputList5685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5685 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5685 (by decide) v hb
mask_input "5685|309489769081333677975150592|19647405751979158911582208"
def inputClause5686 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,false),(78,true),(84,true),(88,false)]
theorem inputList5686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5686 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5686 (by decide) v hb
mask_input "5686|309489769081333677975142400|19647405751979158911590400"
def inputClause5687 : CNF.NClause := [(44,false),(13,false),(65,true),(71,true),(72,false),(78,true),(84,true),(88,false)]
theorem inputList5687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5687 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5687 (by decide) v hb
mask_input "5687|309489732187845530556047360|19647442645467306330685440"
def inputClause5688 : CNF.NClause := [(44,false),(13,true),(65,true),(71,true),(72,false),(78,true),(84,true),(88,false)]
theorem inputList5688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5688 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5688 (by decide) v hb
mask_input "5688|309489732187845530556039168|19647442645467306330693632"
def inputClause5689 : CNF.NClause := [(44,false),(13,false),(65,false),(71,false),(72,true),(78,true),(84,true),(88,false)]
theorem inputList5689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5689 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5689 (by decide) v hb
mask_input "5689|309487407898092243152543744|19649766935220593734189056"
def inputClause5690 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,true),(78,true),(84,true),(88,false)]
theorem inputList5690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5690 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5690 (by decide) v hb
mask_input "5690|309487407898092243152535552|19649766935220593734197248"
def inputClause5691 : CNF.NClause := [(44,false),(13,false),(65,true),(71,false),(72,true),(78,true),(84,true),(88,false)]
theorem inputList5691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5691 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5691 (by decide) v hb
mask_input "5691|309487371004604095733440512|19649803828708741153292288"
end Percolation.MaskChain
