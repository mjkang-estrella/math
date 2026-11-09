import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause7739 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,true),(80,true),(86,true),(88,false)]
theorem inputList7739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7739 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7739 (by decide) v hb
mask_input "7739|309485306122171753221324800|78599072352568393364144128"
def inputClause7740 : CNF.NClause := [(60,false),(29,true),(62,true),(68,false),(74,true),(80,true),(86,true),(88,false)]
theorem inputList7740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7740 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7740 (by decide) v hb
mask_input "7740|309485306122171752684453888|78599072352568393901015040"
def inputClause7741 : CNF.NClause := [(60,false),(29,false),(62,false),(68,true),(74,true),(80,true),(86,true),(88,false)]
theorem inputList7741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7741 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7741 (by decide) v hb
mask_input "7741|309485015585952592295886848|78599362888787554289582080"
def inputClause7742 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(74,true),(80,true),(86,true),(88,false)]
theorem inputList7742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7742 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7742 (by decide) v hb
mask_input "7742|309485015585952591759015936|78599362888787554826452992"
def inputClause7743 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(74,true),(80,true),(86,true),(88,false)]
theorem inputList7743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7743 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7743 (by decide) v hb
mask_input "7743|309485010974266573868498944|78599367500473572716969984"
def inputClause7744 : CNF.NClause := [(60,false),(29,true),(62,true),(68,true),(74,true),(80,true),(86,true),(88,false)]
theorem inputList7744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7744 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7744 (by decide) v hb
mask_input "7744|309485010974266573331628032|78599367500473573253840896"
def inputClause7745 : CNF.NClause := [(60,false),(29,false),(62,false),(68,false),(74,false),(80,false),(86,false),(88,true)]
theorem inputList7745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7745 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7745 (by decide) v hb
mask_input "7745|78599368653395077860687872|309485009821345068724781056"
def inputClause7746 : CNF.NClause := [(60,false),(29,true),(62,false),(68,false),(74,false),(80,false),(86,false),(88,true)]
theorem inputList7746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7746 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7746 (by decide) v hb
mask_input "7746|78599368653395077323816960|309485009821345069261651968"
def inputClause7747 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,false),(80,false),(86,false),(88,true)]
theorem inputList7747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7747 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7747 (by decide) v hb
mask_input "7747|78599364041709059433299968|309485014433031087152168960"
def inputClause7748 : CNF.NClause := [(60,false),(29,true),(62,true),(68,false),(74,false),(80,false),(86,false),(88,true)]
theorem inputList7748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7748 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7748 (by decide) v hb
mask_input "7748|78599364041709058896429056|309485014433031087689039872"
def inputClause7749 : CNF.NClause := [(60,false),(29,false),(62,false),(68,true),(74,false),(80,false),(86,false),(88,true)]
theorem inputList7749 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7749 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7749 (by decide) v hb
mask_input "7749|78599073505489898507862016|309485304969250248077606912"
def inputClause7750 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(74,false),(80,false),(86,false),(88,true)]
theorem inputList7750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7750 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7750 (by decide) v hb
mask_input "7750|78599073505489897970991104|309485304969250248614477824"
def inputClause7751 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(74,false),(80,false),(86,false),(88,true)]
theorem inputList7751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7751 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7751 (by decide) v hb
mask_input "7751|78599068893803880080474112|309485309580936266504994816"
def inputClause7752 : CNF.NClause := [(60,false),(29,true),(62,true),(68,true),(74,false),(80,false),(86,false),(88,true)]
theorem inputList7752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7752 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7752 (by decide) v hb
mask_input "7752|78599068893803879543603200|309485309580936267041865728"
def inputClause7753 : CNF.NClause := [(60,false),(29,false),(62,false),(68,false),(74,true),(80,false),(86,false),(88,true)]
theorem inputList7753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7753 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7753 (by decide) v hb
mask_input "7753|78580479187463599279833088|309503899287276547305635840"
def inputClause7754 : CNF.NClause := [(60,false),(29,true),(62,false),(68,false),(74,true),(80,false),(86,false),(88,true)]
theorem inputList7754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7754 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7754 (by decide) v hb
mask_input "7754|78580479187463598742962176|309503899287276547842506752"
def inputClause7755 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,true),(80,false),(86,false),(88,true)]
theorem inputList7755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7755 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7755 (by decide) v hb
mask_input "7755|78580474575777580852445184|309503903898962565733023744"
def inputClause7756 : CNF.NClause := [(60,false),(29,true),(62,true),(68,false),(74,true),(80,false),(86,false),(88,true)]
theorem inputList7756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7756 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7756 (by decide) v hb
mask_input "7756|78580474575777580315574272|309503903898962566269894656"
def inputClause7757 : CNF.NClause := [(60,false),(29,false),(62,false),(68,true),(74,true),(80,false),(86,false),(88,true)]
theorem inputList7757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7757 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7757 (by decide) v hb
mask_input "7757|78580184039558419927007232|309504194435181726658461696"
def inputClause7758 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(74,true),(80,false),(86,false),(88,true)]
theorem inputList7758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7758 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7758 (by decide) v hb
mask_input "7758|78580184039558419390136320|309504194435181727195332608"
def inputClause7759 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(74,true),(80,false),(86,false),(88,true)]
theorem inputList7759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7759 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7759 (by decide) v hb
mask_input "7759|78580179427872401499619328|309504199046867745085849600"
def inputClause7760 : CNF.NClause := [(60,false),(29,true),(62,true),(68,true),(74,true),(80,false),(86,false),(88,true)]
theorem inputList7760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7760 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7760 (by decide) v hb
mask_input "7760|78580179427872400962748416|309504199046867745622720512"
def inputClause7761 : CNF.NClause := [(60,false),(29,false),(62,false),(68,false),(74,false),(80,true),(86,false),(88,true)]
theorem inputList7761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7761 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7761 (by decide) v hb
mask_input "7761|77390442833780448685981696|310693935640959697899487232"
def inputClause7762 : CNF.NClause := [(60,false),(29,true),(62,false),(68,false),(74,false),(80,true),(86,false),(88,true)]
theorem inputList7762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7762 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7762 (by decide) v hb
mask_input "7762|77390442833780448149110784|310693935640959698436358144"
def inputClause7763 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,false),(80,true),(86,false),(88,true)]
theorem inputList7763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7763 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7763 (by decide) v hb
mask_input "7763|77390438222094430258593792|310693940252645716326875136"
def inputClause7764 : CNF.NClause := [(60,false),(29,true),(62,true),(68,false),(74,false),(80,true),(86,false),(88,true)]
theorem inputList7764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7764 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7764 (by decide) v hb
mask_input "7764|77390438222094429721722880|310693940252645716863746048"
def inputClause7765 : CNF.NClause := [(60,false),(29,false),(62,false),(68,true),(74,false),(80,true),(86,false),(88,true)]
theorem inputList7765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7765 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7765 (by decide) v hb
mask_input "7765|77390147685875269333155840|310694230788864877252313088"
def inputClause7766 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(74,false),(80,true),(86,false),(88,true)]
theorem inputList7766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7766 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7766 (by decide) v hb
mask_input "7766|77390147685875268796284928|310694230788864877789184000"
def inputClause7767 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(74,false),(80,true),(86,false),(88,true)]
theorem inputList7767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7767 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7767 (by decide) v hb
mask_input "7767|77390143074189250905767936|310694235400550895679700992"
def inputClause7768 : CNF.NClause := [(60,false),(29,true),(62,true),(68,true),(74,false),(80,true),(86,false),(88,true)]
theorem inputList7768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7768 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7768 (by decide) v hb
mask_input "7768|77390143074189250368897024|310694235400550896216571904"
def inputClause7769 : CNF.NClause := [(60,false),(29,false),(62,false),(68,false),(74,true),(80,true),(86,false),(88,true)]
theorem inputList7769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7769 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7769 (by decide) v hb
mask_input "7769|77371553367848970105126912|310712825106891176480342016"
def inputClause7770 : CNF.NClause := [(60,false),(29,true),(62,false),(68,false),(74,true),(80,true),(86,false),(88,true)]
theorem inputList7770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7770 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7770 (by decide) v hb
mask_input "7770|77371553367848969568256000|310712825106891177017212928"
def inputClause7771 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,true),(80,true),(86,false),(88,true)]
theorem inputList7771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7771 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7771 (by decide) v hb
mask_input "7771|77371548756162951677739008|310712829718577194907729920"
def inputClause7772 : CNF.NClause := [(60,false),(29,true),(62,true),(68,false),(74,true),(80,true),(86,false),(88,true)]
theorem inputList7772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7772 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7772 (by decide) v hb
mask_input "7772|77371548756162951140868096|310712829718577195444600832"
def inputClause7773 : CNF.NClause := [(60,false),(29,false),(62,false),(68,true),(74,true),(80,true),(86,false),(88,true)]
theorem inputList7773 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7773 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7773 (by decide) v hb
mask_input "7773|77371258219943790752301056|310713120254796355833167872"
def inputClause7774 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(74,true),(80,true),(86,false),(88,true)]
theorem inputList7774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7774 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7774 (by decide) v hb
mask_input "7774|77371258219943790215430144|310713120254796356370038784"
def inputClause7776 : CNF.NClause := [(60,false),(29,true),(62,true),(68,true),(74,true),(80,true),(86,false),(88,true)]
theorem inputList7776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7776 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7776 (by decide) v hb
mask_input "7776|77371253608257771788042240|310713124866482374797426688"
def inputClause7777 : CNF.NClause := [(60,false),(29,false),(62,false),(68,false),(74,false),(80,false),(86,true),(88,true)]
theorem inputList7777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7777 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7777 (by decide) v hb
mask_input "7777|1228116198058810679492608|386856262276681335905976320"
def inputClause7778 : CNF.NClause := [(60,false),(29,true),(62,false),(68,false),(74,false),(80,false),(86,true),(88,true)]
theorem inputList7778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7778 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7778 (by decide) v hb
mask_input "7778|1228116198058810142621696|386856262276681336442847232"
def inputClause7779 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,false),(80,false),(86,true),(88,true)]
theorem inputList7779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7779 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7779 (by decide) v hb
mask_input "7779|1228111586372792252104704|386856266888367354333364224"
end Percolation.MaskChain
