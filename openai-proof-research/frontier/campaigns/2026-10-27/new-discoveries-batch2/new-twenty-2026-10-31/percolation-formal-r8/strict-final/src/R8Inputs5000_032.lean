import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause5734 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,false),(78,false),(84,true),(88,true)]
theorem inputList5734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5734 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5734 (by decide) v hb
mask_input "5734|306990714892266544037888|328830184118420570342694912"
def inputClause5736 : CNF.NClause := [(44,false),(13,true),(65,true),(71,true),(72,false),(78,false),(84,true),(88,true)]
theorem inputList5736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5736 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5736 (by decide) v hb
mask_input "5736|306953821404119124934656|328830221011908717761798144"
def inputClause5737 : CNF.NClause := [(44,false),(13,false),(65,false),(71,false),(72,true),(78,false),(84,true),(88,true)]
theorem inputList5737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5737 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5737 (by decide) v hb
mask_input "5737|304629531650831721439232|328832545301662005165293568"
def inputClause5738 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,true),(78,false),(84,true),(88,true)]
theorem inputList5738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5738 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5738 (by decide) v hb
mask_input "5738|304629531650831721431040|328832545301662005165301760"
def inputClause5739 : CNF.NClause := [(44,false),(13,false),(65,true),(71,false),(72,true),(78,false),(84,true),(88,true)]
theorem inputList5739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5739 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5739 (by decide) v hb
mask_input "5739|304592638162684302336000|328832582195150152584396800"
def inputClause5740 : CNF.NClause := [(44,false),(13,true),(65,true),(71,false),(72,true),(78,false),(84,true),(88,true)]
theorem inputList5740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5740 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5740 (by decide) v hb
mask_input "5740|304592638162684302327808|328832582195150152584404992"
def inputClause5741 : CNF.NClause := [(44,false),(13,false),(65,false),(71,true),(72,true),(78,false),(84,true),(88,true)]
theorem inputList5741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5741 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5741 (by decide) v hb
mask_input "5741|302268348409396898832384|328834906484903439987900416"
def inputClause5742 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,true),(78,false),(84,true),(88,true)]
theorem inputList5742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5742 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5742 (by decide) v hb
mask_input "5742|302268348409396898824192|328834906484903439987908608"
def inputClause5743 : CNF.NClause := [(44,false),(13,false),(65,true),(71,true),(72,true),(78,false),(84,true),(88,true)]
theorem inputList5743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5743 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5743 (by decide) v hb
mask_input "5743|302231454921249479729152|328834943378391587407003648"
def inputClause5744 : CNF.NClause := [(44,false),(13,true),(65,true),(71,true),(72,true),(78,false),(84,true),(88,true)]
theorem inputList5744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5744 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5744 (by decide) v hb
mask_input "5744|302231454921249479720960|328834943378391587407011840"
def inputClause5745 : CNF.NClause := [(44,false),(13,false),(65,false),(71,false),(72,false),(78,true),(84,true),(88,true)]
theorem inputList5745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5745 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5745 (by decide) v hb
mask_input "5745|7120443230044072976384|329130054390082792813756416"
def inputClause5747 : CNF.NClause := [(44,false),(13,false),(65,true),(71,false),(72,false),(78,true),(84,true),(88,true)]
theorem inputList5747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5747 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5747 (by decide) v hb
mask_input "5747|7083549741896653873152|329130091283570940232859648"
def inputClause5748 : CNF.NClause := [(44,false),(13,true),(65,true),(71,false),(72,false),(78,true),(84,true),(88,true)]
theorem inputList5748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5748 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5748 (by decide) v hb
mask_input "5748|7083549741896653864960|329130091283570940232867840"
def inputClause5749 : CNF.NClause := [(44,false),(13,false),(65,false),(71,true),(72,false),(78,true),(84,true),(88,true)]
theorem inputList5749 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5749 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5749 (by decide) v hb
mask_input "5749|4759259988609250369536|329132415573324227636363264"
def inputClause5750 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,false),(78,true),(84,true),(88,true)]
theorem inputList5750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5750 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5750 (by decide) v hb
mask_input "5750|4759259988609250361344|329132415573324227636371456"
def inputClause5751 : CNF.NClause := [(44,false),(13,false),(65,true),(71,true),(72,false),(78,true),(84,true),(88,true)]
theorem inputList5751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5751 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5751 (by decide) v hb
mask_input "5751|4722366500461831266304|329132452466812375055466496"
def inputClause5752 : CNF.NClause := [(44,false),(13,true),(65,true),(71,true),(72,false),(78,true),(84,true),(88,true)]
theorem inputList5752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5752 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5752 (by decide) v hb
mask_input "5752|4722366500461831258112|329132452466812375055474688"
def inputClause5753 : CNF.NClause := [(44,false),(13,false),(65,false),(71,false),(72,true),(78,true),(84,true),(88,true)]
theorem inputList5753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5753 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5753 (by decide) v hb
mask_input "5753|2398076747174427762688|329134776756565662458970112"
def inputClause5754 : CNF.NClause := [(44,false),(13,true),(65,false),(71,false),(72,true),(78,true),(84,true),(88,true)]
theorem inputList5754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5754 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5754 (by decide) v hb
mask_input "5754|2398076747174427754496|329134776756565662458978304"
def inputClause5756 : CNF.NClause := [(44,false),(13,true),(65,true),(71,false),(72,true),(78,true),(84,true),(88,true)]
theorem inputList5756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5756 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5756 (by decide) v hb
mask_input "5756|2361183259027008651264|329134813650053809878081536"
def inputClause5757 : CNF.NClause := [(44,false),(13,false),(65,false),(71,true),(72,true),(78,true),(84,true),(88,true)]
theorem inputList5757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5757 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5757 (by decide) v hb
mask_input "5757|36893505739605155840|329137137939807097281576960"
def inputClause5758 : CNF.NClause := [(44,false),(13,true),(65,false),(71,true),(72,true),(78,true),(84,true),(88,true)]
theorem inputList5758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5758 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5758 (by decide) v hb
mask_input "5758|36893505739605147648|329137137939807097281585152"
def inputClause5759 : CNF.NClause := [(44,false),(13,false),(65,true),(71,true),(72,true),(78,true),(84,true),(88,true)]
theorem inputList5759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5759 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5759 (by decide) v hb
mask_input "5759|17592186052608|329137174833295244700680192"
def inputClause5760 : CNF.NClause := [(44,false),(13,true),(65,true),(71,true),(72,true),(78,true),(84,true),(88,true)]
theorem inputList5760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5760 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 13) (spread_mem 13) inputClause5760 (by decide) v hb
mask_input "5760|17592186044416|329137174833295244700688384"
def inputClause5761 : CNF.NClause := [(45,true),(14,false),(63,false),(70,false),(72,false),(79,false),(86,false),(89,false)]
theorem inputList5761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5761 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5761 (by decide) v hb
mask_input "5761|696951647189309343129419776|35184372088832"
def inputClause5763 : CNF.NClause := [(45,false),(14,false),(63,true),(70,false),(72,false),(79,false),(86,false),(89,false)]
theorem inputList5763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5763 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5763 (by decide) v hb
mask_input "5763|696951637965972490646732800|9223372036854775808"
def inputClause5764 : CNF.NClause := [(45,false),(14,true),(63,true),(70,false),(72,false),(79,false),(86,false),(89,false)]
theorem inputList5764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5764 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5764 (by decide) v hb
mask_input "5764|696951637965972490646716416|9223372036854792192"
def inputClause5765 : CNF.NClause := [(45,false),(14,false),(63,false),(70,true),(72,false),(79,false),(86,false),(89,false)]
theorem inputList5765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5765 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5765 (by decide) v hb
mask_input "5765|696950466597723810090205184|1180591620717411303424"
def inputClause5767 : CNF.NClause := [(45,false),(14,false),(63,true),(70,true),(72,false),(79,false),(86,false),(89,false)]
theorem inputList5767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5767 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5767 (by decide) v hb
mask_input "5767|696950457374351773235429376|1189814992754266079232"
def inputClause5768 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(72,false),(79,false),(86,false),(89,false)]
theorem inputList5768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5768 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5768 (by decide) v hb
mask_input "5768|696950457374351773235412992|1189814992754266095616"
def inputClause5769 : CNF.NClause := [(45,false),(14,false),(63,false),(70,false),(72,true),(79,false),(86,false),(89,false)]
theorem inputList5769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5769 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5769 (by decide) v hb
mask_input "5769|696946924822861657856294912|4722366482869645213696"
def inputClause5770 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,true),(79,false),(86,false),(89,false)]
theorem inputList5770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5770 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5770 (by decide) v hb
mask_input "5770|696946924822861657856278528|4722366482869645230080"
def inputClause5771 : CNF.NClause := [(45,false),(14,false),(63,true),(70,false),(72,true),(79,false),(86,false),(89,false)]
theorem inputList5771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5771 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5771 (by decide) v hb
mask_input "5771|696946915599489621001519104|4731589854906499989504"
def inputClause5772 : CNF.NClause := [(45,false),(14,true),(63,true),(70,false),(72,true),(79,false),(86,false),(89,false)]
theorem inputList5772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5772 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5772 (by decide) v hb
mask_input "5772|696946915599489621001502720|4731589854906500005888"
def inputClause5773 : CNF.NClause := [(45,false),(14,false),(63,false),(70,true),(72,true),(79,false),(86,false),(89,false)]
theorem inputList5773 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5773 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5773 (by decide) v hb
mask_input "5773|696945744231240940444991488|5902958103587056517120"
def inputClause5775 : CNF.NClause := [(45,false),(14,false),(63,true),(70,true),(72,true),(79,false),(86,false),(89,false)]
theorem inputList5775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5775 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5775 (by decide) v hb
mask_input "5775|696945735007868903590215680|5912181475623911292928"
def inputClause5776 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(72,true),(79,false),(86,false),(89,false)]
theorem inputList5776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5776 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5776 (by decide) v hb
mask_input "5776|696945735007868903590199296|5912181475623911309312"
def inputClause5777 : CNF.NClause := [(45,false),(14,false),(63,false),(70,false),(72,false),(79,true),(86,false),(89,false)]
theorem inputList5777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5777 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5777 (by decide) v hb
mask_input "5777|696347184279537212914155520|604462909807314587353088"
def inputClause5778 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,false),(79,true),(86,false),(89,false)]
theorem inputList5778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5778 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5778 (by decide) v hb
mask_input "5778|696347184279537212914139136|604462909807314587369472"
def inputClause5779 : CNF.NClause := [(45,false),(14,false),(63,true),(70,false),(72,false),(79,true),(86,false),(89,false)]
theorem inputList5779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5779 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5779 (by decide) v hb
mask_input "5779|696347175056165176059379712|604472133179351442128896"
end Percolation.MaskChain
