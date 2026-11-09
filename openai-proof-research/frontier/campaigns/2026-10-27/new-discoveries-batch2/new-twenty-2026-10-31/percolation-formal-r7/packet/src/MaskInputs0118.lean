import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause14691 : CNF.NClause := [(30,true),(25,true),(1079,false)]
theorem inputList14691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14691 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14691
  have he : decodeClause inputClause14691 = containClause5 30 25 := by decide
  rw [he]
  exact input_contain 30 25 (by decide) v hb
mask_input "14691|6476872105833939787279851095005353825585812792452547787420843456877770866175851100542732278445987983845986491658137981164473879596345391259744428798103632317488557576850123563662941047746982922919672565711127842193984239469590166355779307380773105802905921808395480625674669267687376081029962480276672200425846647714991833088|1107296256"
def inputClause14692 : CNF.NClause := [(30,true),(26,true),(1080,false)]
theorem inputList14692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14692 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14692
  have he : decodeClause inputClause14692 = containClause5 30 26 := by decide
  rw [he]
  exact input_contain 30 26 (by decide) v hb
mask_input "14692|12953744211667879574559702190010707651171625584905095574841686913755541732351702201085464556891975967691972983316275962328947759192690782519488857596207264634977115153700247127325882095493965845839345131422255684387968478939180332711558614761546211605811843616790961251349338535374752162059924960553344400851693295429983666176|1140850688"
def inputClause14693 : CNF.NClause := [(30,true),(27,true),(1081,false)]
theorem inputList14693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14693 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14693
  have he : decodeClause inputClause14693 = containClause5 30 27 := by decide
  rw [he]
  exact input_contain 30 27 (by decide) v hb
mask_input "14693|25907488423335759149119404380021415302343251169810191149683373827511083464703404402170929113783951935383945966632551924657895518385381565038977715192414529269954230307400494254651764190987931691678690262844511368775936957878360665423117229523092423211623687233581922502698677070749504324119849921106688801703386590859967332352|1207959552"
def inputClause14694 : CNF.NClause := [(30,true),(28,true),(1082,false)]
theorem inputList14694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14694 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14694 = (containClause5 30 28) := by decide
  rw [he]
  exact input_contain 30 28 (by decide) v hb
mask_input "14694|51814976846671518298238808760042830604686502339620382299366747655022166929406808804341858227567903870767891933265103849315791036770763130077955430384829058539908460614800988509303528381975863383357380525689022737551873915756721330846234459046184846423247374467163845005397354141499008648239699842213377603406773181719934664704|1342177280"
def inputClause14695 : CNF.NClause := [(30,true),(29,true),(1083,false)]
theorem inputList14695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14695 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14695 = (containClause5 30 29) := by decide
  rw [he]
  exact input_contain 30 29 (by decide) v hb
mask_input "14695|103629953693343036596477617520085661209373004679240764598733495310044333858813617608683716455135807741535783866530207698631582073541526260155910860769658117079816921229601977018607056763951726766714761051378045475103747831513442661692468918092369692846494748934327690010794708282998017296479399684426755206813546363439869329408|1610612736"
def inputClause14696 : CNF.NClause := [(0,false)]
theorem inputList14696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14696 := by
  apply holds_decode
  apply h
  exact List.mem_append_right _ (by decide : decodeClause inputClause14696 ∈ normalizedUnits5)
mask_input "14696|1|0"
def inputClause14697 : CNF.NClause := [(25,false)]
theorem inputList14697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14697 := by
  apply holds_decode
  apply h
  exact List.mem_append_right _ (by decide : decodeClause inputClause14697 ∈ normalizedUnits5)
mask_input "14697|33554432|0"
def inputClause14698 : CNF.NClause := [(30,false)]
theorem inputList14698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14698 := by
  apply holds_decode
  apply h
  exact List.mem_append_right _ (by decide : decodeClause inputClause14698 ∈ normalizedUnits5)
mask_input "14698|1073741824|0"
end Percolation.MaskChain
