import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause7698 : CNF.NClause := [(60,false),(29,true),(62,false),(68,false),(74,false),(80,true),(86,false),(88,false)]
theorem inputList7698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7698 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7698 (by decide) v hb
mask_input "7698|386875452655125516873891840|1208925819614629711577088"
def inputClause7699 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,false),(80,true),(86,false),(88,false)]
theorem inputList7699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7699 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7699 (by decide) v hb
mask_input "7699|386875448043439498983374848|1208930431300647602094080"
def inputClause7700 : CNF.NClause := [(60,false),(29,true),(62,true),(68,false),(74,false),(80,true),(86,false),(88,false)]
theorem inputList7700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7700 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7700 (by decide) v hb
mask_input "7700|386875448043439498446503936|1208930431300648138964992"
def inputClause7701 : CNF.NClause := [(60,false),(29,false),(62,false),(68,true),(74,false),(80,true),(86,false),(88,false)]
theorem inputList7701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7701 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7701 (by decide) v hb
mask_input "7701|386875157507220338057936896|1209220967519808527532032"
def inputClause7702 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(74,false),(80,true),(86,false),(88,false)]
theorem inputList7702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7702 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7702 (by decide) v hb
mask_input "7702|386875157507220337521065984|1209220967519809064402944"
def inputClause7703 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(74,false),(80,true),(86,false),(88,false)]
theorem inputList7703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7703 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7703 (by decide) v hb
mask_input "7703|386875152895534319630548992|1209225579205826954919936"
def inputClause7704 : CNF.NClause := [(60,false),(29,true),(62,true),(68,true),(74,false),(80,true),(86,false),(88,false)]
theorem inputList7704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7704 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7704 (by decide) v hb
mask_input "7704|386875152895534319093678080|1209225579205827491790848"
def inputClause7705 : CNF.NClause := [(60,false),(29,false),(62,false),(68,false),(74,true),(80,true),(86,false),(88,false)]
theorem inputList7705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7705 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7705 (by decide) v hb
mask_input "7705|386856563189194038829907968|1227815285546107755560960"
def inputClause7706 : CNF.NClause := [(60,false),(29,true),(62,false),(68,false),(74,true),(80,true),(86,false),(88,false)]
theorem inputList7706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7706 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7706 (by decide) v hb
mask_input "7706|386856563189194038293037056|1227815285546108292431872"
def inputClause7707 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,true),(80,true),(86,false),(88,false)]
theorem inputList7707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7707 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7707 (by decide) v hb
mask_input "7707|386856558577508020402520064|1227819897232126182948864"
def inputClause7708 : CNF.NClause := [(60,false),(29,true),(62,true),(68,false),(74,true),(80,true),(86,false),(88,false)]
theorem inputList7708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7708 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7708 (by decide) v hb
mask_input "7708|386856558577508019865649152|1227819897232126719819776"
def inputClause7710 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(74,true),(80,true),(86,false),(88,false)]
theorem inputList7710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7710 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7710 (by decide) v hb
mask_input "7710|386856268041288858940211200|1228110433451287645257728"
def inputClause7711 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(74,true),(80,true),(86,false),(88,false)]
theorem inputList7711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7711 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7711 (by decide) v hb
mask_input "7711|386856263429602841049694208|1228115045137305535774720"
def inputClause7712 : CNF.NClause := [(60,false),(29,true),(62,true),(68,true),(74,true),(80,true),(86,false),(88,false)]
theorem inputList7712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7712 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7712 (by decide) v hb
mask_input "7712|386856263429602840512823296|1228115045137306072645632"
def inputClause7713 : CNF.NClause := [(60,false),(29,false),(62,false),(68,false),(74,false),(80,false),(86,true),(88,false)]
theorem inputList7713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7713 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7713 (by decide) v hb
mask_input "7713|310713126019403879404273664|77371252455336267181195264"
def inputClause7714 : CNF.NClause := [(60,false),(29,true),(62,false),(68,false),(74,false),(80,false),(86,true),(88,false)]
theorem inputList7714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7714 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7714 (by decide) v hb
mask_input "7714|310713126019403878867402752|77371252455336267718066176"
def inputClause7715 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,false),(80,false),(86,true),(88,false)]
theorem inputList7715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7715 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7715 (by decide) v hb
mask_input "7715|310713121407717860976885760|77371257067022285608583168"
def inputClause7716 : CNF.NClause := [(60,false),(29,true),(62,true),(68,false),(74,false),(80,false),(86,true),(88,false)]
theorem inputList7716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7716 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7716 (by decide) v hb
mask_input "7716|310713121407717860440014848|77371257067022286145454080"
def inputClause7717 : CNF.NClause := [(60,false),(29,false),(62,false),(68,true),(74,false),(80,false),(86,true),(88,false)]
theorem inputList7717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7717 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7717 (by decide) v hb
mask_input "7717|310712830871498700051447808|77371547603241446534021120"
def inputClause7718 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(74,false),(80,false),(86,true),(88,false)]
theorem inputList7718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7718 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7718 (by decide) v hb
mask_input "7718|310712830871498699514576896|77371547603241447070892032"
def inputClause7719 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(74,false),(80,false),(86,true),(88,false)]
theorem inputList7719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7719 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7719 (by decide) v hb
mask_input "7719|310712826259812681624059904|77371552214927464961409024"
def inputClause7720 : CNF.NClause := [(60,false),(29,true),(62,true),(68,true),(74,false),(80,false),(86,true),(88,false)]
theorem inputList7720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7720 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7720 (by decide) v hb
mask_input "7720|310712826259812681087188992|77371552214927465498279936"
def inputClause7721 : CNF.NClause := [(60,false),(29,false),(62,false),(68,false),(74,true),(80,false),(86,true),(88,false)]
theorem inputList7721 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7721 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7721 (by decide) v hb
mask_input "7721|310694236553472400823418880|77390141921267745762050048"
def inputClause7722 : CNF.NClause := [(60,false),(29,true),(62,false),(68,false),(74,true),(80,false),(86,true),(88,false)]
theorem inputList7722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7722 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7722 (by decide) v hb
mask_input "7722|310694236553472400286547968|77390141921267746298920960"
def inputClause7723 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,true),(80,false),(86,true),(88,false)]
theorem inputList7723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7723 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7723 (by decide) v hb
mask_input "7723|310694231941786382396030976|77390146532953764189437952"
def inputClause7724 : CNF.NClause := [(60,false),(29,true),(62,true),(68,false),(74,true),(80,false),(86,true),(88,false)]
theorem inputList7724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7724 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7724 (by decide) v hb
mask_input "7724|310694231941786381859160064|77390146532953764726308864"
def inputClause7725 : CNF.NClause := [(60,false),(29,false),(62,false),(68,true),(74,true),(80,false),(86,true),(88,false)]
theorem inputList7725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7725 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7725 (by decide) v hb
mask_input "7725|310693941405567221470593024|77390437069172925114875904"
def inputClause7726 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(74,true),(80,false),(86,true),(88,false)]
theorem inputList7726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7726 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7726 (by decide) v hb
mask_input "7726|310693941405567220933722112|77390437069172925651746816"
def inputClause7727 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(74,true),(80,false),(86,true),(88,false)]
theorem inputList7727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7727 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7727 (by decide) v hb
mask_input "7727|310693936793881203043205120|77390441680858943542263808"
def inputClause7728 : CNF.NClause := [(60,false),(29,true),(62,true),(68,true),(74,true),(80,false),(86,true),(88,false)]
theorem inputList7728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7728 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7728 (by decide) v hb
mask_input "7728|310693936793881202506334208|77390441680858944079134720"
def inputClause7729 : CNF.NClause := [(60,false),(29,false),(62,false),(68,false),(74,false),(80,true),(86,true),(88,false)]
theorem inputList7729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7729 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7729 (by decide) v hb
mask_input "7729|309504200199789250229567488|78580178274950896355901440"
def inputClause7730 : CNF.NClause := [(60,false),(29,true),(62,false),(68,false),(74,false),(80,true),(86,true),(88,false)]
theorem inputList7730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7730 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7730 (by decide) v hb
mask_input "7730|309504200199789249692696576|78580178274950896892772352"
def inputClause7731 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,false),(80,true),(86,true),(88,false)]
theorem inputList7731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7731 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7731 (by decide) v hb
mask_input "7731|309504195588103231802179584|78580182886636914783289344"
def inputClause7732 : CNF.NClause := [(60,false),(29,true),(62,true),(68,false),(74,false),(80,true),(86,true),(88,false)]
theorem inputList7732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7732 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7732 (by decide) v hb
mask_input "7732|309504195588103231265308672|78580182886636915320160256"
def inputClause7733 : CNF.NClause := [(60,false),(29,false),(62,false),(68,true),(74,false),(80,true),(86,true),(88,false)]
theorem inputList7733 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7733 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7733 (by decide) v hb
mask_input "7733|309503905051884070876741632|78580473422856075708727296"
def inputClause7734 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(74,false),(80,true),(86,true),(88,false)]
theorem inputList7734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7734 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7734 (by decide) v hb
mask_input "7734|309503905051884070339870720|78580473422856076245598208"
def inputClause7735 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(74,false),(80,true),(86,true),(88,false)]
theorem inputList7735 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7735 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7735 (by decide) v hb
mask_input "7735|309503900440198052449353728|78580478034542094136115200"
def inputClause7736 : CNF.NClause := [(60,false),(29,true),(62,true),(68,true),(74,false),(80,true),(86,true),(88,false)]
theorem inputList7736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7736 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7736 (by decide) v hb
mask_input "7736|309503900440198051912482816|78580478034542094672986112"
def inputClause7737 : CNF.NClause := [(60,false),(29,false),(62,false),(68,false),(74,true),(80,true),(86,true),(88,false)]
theorem inputList7737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7737 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7737 (by decide) v hb
mask_input "7737|309485310733857771648712704|78599067740882374936756224"
def inputClause7738 : CNF.NClause := [(60,false),(29,true),(62,false),(68,false),(74,true),(80,true),(86,true),(88,false)]
theorem inputList7738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7738 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7738 (by decide) v hb
mask_input "7738|309485310733857771111841792|78599067740882375473627136"
end Percolation.MaskChain
