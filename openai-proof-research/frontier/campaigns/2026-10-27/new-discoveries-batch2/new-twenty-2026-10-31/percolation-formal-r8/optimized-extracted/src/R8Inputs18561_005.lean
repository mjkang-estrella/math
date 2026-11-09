import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause8754 : CNF.NClause := [(250,true),(257,true),(259,true),(266,true),(268,true),(275,false)]
theorem inputList8754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8754 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 7) (closed_mem 4 7) inputClause8754 (by decide) v hb
mask_input "8754|60708402882054033466233184588234965832575213720379360039119137804340758912662765568|594015227038826415588472646391209728035835228678246494156230522485344478695522304"
def inputClause8755 : CNF.NClause := [(250,true),(257,true),(259,true),(266,true),(268,false),(275,true)]
theorem inputList8755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8755 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 7) (closed_mem 4 7) inputClause8755 (by decide) v hb
mask_input "8755|474284397516047136454946754595585670566993857190463750305618264096412179005177856|60828133711576812745366710480030589890044055091867142782969750062729691212353110016"
def inputClause8757 : CNF.NClause := [(250,true),(257,true),(259,false),(266,true),(268,true),(275,true)]
theorem inputList8757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8757 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 7) (closed_mem 4 7) inputClause8757 (by decide) v hb
mask_input "8757|926336713898529563388567880069503262826159877325124512315660672063305037119488|61301491772378961352258268666746106057348222789180281408763052666154040086321168384"
def inputClause8758 : CNF.NClause := [(250,true),(257,false),(259,true),(266,true),(268,true),(275,true)]
theorem inputList8758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8758 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 7) (closed_mem 4 7) inputClause8758 (by decide) v hb
mask_input "8758|231584178474632390847141970017375815706539969331281128078915168015826259279872|61302186524914385249430810092656158184795342409088275252147289411658087565099008000"
def inputClause8759 : CNF.NClause := [(250,false),(257,true),(259,true),(266,true),(268,true),(275,true)]
theorem inputList8759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8759 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 7) (closed_mem 4 7) inputClause8759 (by decide) v hb
mask_input "8759|1809251394333065553493296640760748560207343510400633813116524750123642650624|61302416299841465548756103741329534799862488741714096132641555210301353267715637248"
def inputClause8760 : CNF.NClause := [(251,true),(254,true),(262,true),(265,true),(268,true),(276,false)]
theorem inputList8760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8760 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 8) (closed_mem 4 8) inputClause8760 (by decide) v hb
mask_input "8760|121416805764108066932466369176469931665150427440758720078238275608681517825325531136|541013207441839260198886521300123598964561100541059926600981929930472367245492224"
def inputClause8763 : CNF.NClause := [(251,true),(254,true),(262,false),(265,true),(268,true),(276,true)]
theorem inputList8763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8763 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 8) (closed_mem 4 8) inputClause8763 (by decide) v hb
mask_input "8763|7410693711188236507108543040556026102609279018600996098525285376506440296955904|121950408277838717956158147154729499238012379262281179008740732253235483752274067456"
def inputClause8764 : CNF.NClause := [(251,true),(254,false),(262,true),(265,true),(268,true),(276,true)]
theorem inputList8764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8764 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 8) (closed_mem 4 8) inputClause8764 (by decide) v hb
mask_input "8764|28948022309329048855892746252171976963317496166410141009864396001978282409984|121957790023527596863616399805023803092138025223803613594698247674215988214288613376"
def inputClause8765 : CNF.NClause := [(251,false),(254,true),(262,true),(265,true),(268,true),(276,true)]
theorem inputList8765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8765 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 8) (closed_mem 4 8) inputClause8765 (by decide) v hb
mask_input "8765|3618502788666131106986593281521497120414687020801267626233049500247285301248|121957815353047117526534148711176773742617868126612759203571631305562489945285722112"
def inputClause8767 : CNF.NClause := [(249,true),(255,true),(261,true),(267,true),(268,false),(274,true)]
theorem inputList8767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8767 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 9) (closed_mem 4 9) inputClause8767 (by decide) v hb
mask_input "8767|474284397516047136454946754595585670566993857190463750305618264096412179005177856|30595107787310950244228108475076378488950615166958300413360566963961217784368594944"
def inputClause8768 : CNF.NClause := [(249,true),(255,true),(261,true),(267,false),(268,true),(274,true)]
theorem inputList8768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8768 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 9) (closed_mem 4 9) inputClause8768 (by decide) v hb
mask_input "8768|237142198758023568227473377297792835283496928595231875152809132048206089502588928|30832249986068973812455581852374171324234112095553532288513376096009423873871183872"
def inputClause8770 : CNF.NClause := [(249,true),(255,false),(261,true),(267,true),(268,true),(274,true)]
theorem inputList8770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8770 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 9) (closed_mem 4 9) inputClause8770 (by decide) v hb
mask_input "8770|57896044618658097711785492504343953926634992332820282019728792003956564819968|31069334288782378722585343444179459815563682389156431343384165499265626006808952832"
def inputClause8771 : CNF.NClause := [(249,false),(255,true),(261,true),(267,true),(268,true),(274,true)]
theorem inputList8771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8771 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 9) (closed_mem 4 9) inputClause8771 (by decide) v hb
mask_input "8771|904625697166532776746648320380374280103671755200316906558262375061821325312|31069391280201300214150278483023643779143328920477008963349278669795254901552447488"
def inputClause8774 : CNF.NClause := [(258,true),(259,true),(260,true),(261,false),(262,true),(278,true)]
theorem inputList8774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8774 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 10) (closed_mem 4 10) inputClause8774 (by decide) v hb
mask_input "8774|3705346855594118253554271520278013051304639509300498049262642688253220148477952|485677875928642100819844445236500525948124210601624119244844732532454799309228998656"
def inputClause8775 : CNF.NClause := [(258,true),(259,true),(260,false),(261,true),(262,true),(278,true)]
theorem inputList8775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8775 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 10) (closed_mem 4 10) inputClause8775 (by decide) v hb
mask_input "8775|1852673427797059126777135760139006525652319754650249024631321344126610074238976|485679728602069897878971222372260664954649862921378769493869363853798925919303237632"
def inputClause8776 : CNF.NClause := [(258,true),(259,false),(260,true),(261,true),(262,true),(278,true)]
theorem inputList8776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8776 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 10) (closed_mem 4 10) inputClause8776 (by decide) v hb
mask_input "8776|926336713898529563388567880069503262826159877325124512315660672063305037119488|485680654938783796408534610940140734457912689081256094618381679514470989224340357120"
def inputClause8783 : CNF.NClause := [(252,false),(255,true),(258,true),(266,true),(269,true),(276,true)]
theorem inputList8783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8783 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 11) (closed_mem 4 11) inputClause8783 (by decide) v hb
mask_input "8783|7237005577332262213973186563042994240829374041602535252466099000494570602496|122484466722920740912369405443742538519511503334368258898964094262026480837170561024"
def inputClause8784 : CNF.NClause := [(250,true),(254,true),(258,true),(267,true),(271,true),(277,false)]
theorem inputList8784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8784 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 12) (closed_mem 4 12) inputClause8784 (by decide) v hb
mask_input "8784|242833611528216133864932738352939863330300854881517440156476551217363035650651062272|4031911304517053586763151084045405884176384390897281250628736056076287275987632128"
def inputClause8786 : CNF.NClause := [(250,true),(254,true),(258,true),(267,false),(271,true),(277,true)]
theorem inputList8786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8786 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 12) (closed_mem 4 12) inputClause8786 (by decide) v hb
mask_input "8786|237142198758023568227473377297792835283496928595231875152809132048206089502588928|246628380633975163883468416059687476379193742343819489531952478141391116837136105472"
def inputClause8789 : CNF.NClause := [(250,false),(254,true),(258,true),(267,true),(271,true),(277,true)]
theorem inputList8789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8789 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 12) (closed_mem 4 12) inputClause8789 (by decide) v hb
mask_input "8789|1809251394333065553493296640760748560207343510400633813116524750123642650624|246865521023481793118630335943688628453728679065071211006471474156914572802996043776"
def inputClause8791 : CNF.NClause := [(251,true),(257,true),(258,true),(264,true),(270,false),(274,true)]
theorem inputList8791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8791 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 13) (closed_mem 4 13) inputClause8791 (by decide) v hb
mask_input "8791|1897137590064188545819787018382342682267975428761855001222473056385648716020711424|30384542586909982242448674878783040669642284010859098648605533022229952943582347264"
def inputClause8793 : CNF.NClause := [(251,true),(257,true),(258,false),(264,true),(270,true),(274,true)]
theorem inputList8793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8793 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 13) (closed_mem 4 13) inputClause8793 (by decide) v hb
mask_input "8793|463168356949264781694283940034751631413079938662562256157830336031652518559744|32281217008617221523486767613225348600278846359682291087571848248279570007084498944"
def inputClause8794 : CNF.NClause := [(251,true),(257,false),(258,true),(264,true),(270,true),(274,true)]
theorem inputList8794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8794 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 13) (closed_mem 4 13) inputClause8794 (by decide) v hb
mask_input "8794|231584178474632390847141970017375815706539969331281128078915168015826259279872|32281448592795696155877614755195365976094552899651622368699927163447585833343778816"
def inputClause8796 : CNF.NClause := [(249,true),(256,true),(258,true),(265,true),(272,true),(275,false)]
theorem inputList8796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8796 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 14) (closed_mem 4 14) inputClause8796 (by decide) v hb
mask_input "8796|60708402882054033466233184588234965832575213720379360039119137804340758912662765568|7648415775018143822845911019427182757806322400791311376815198354737061013928017920"
def inputClause8797 : CNF.NClause := [(249,true),(256,true),(258,true),(265,true),(272,false),(275,true)]
theorem inputList8797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8797 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 14) (closed_mem 4 14) inputClause8797 (by decide) v hb
mask_input "8797|7588550360256754183279148073529370729071901715047420004889892225542594864082845696|60768268296815423105799947534132777861309634406123251411044443933535225062507937792"
def inputClause8799 : CNF.NClause := [(249,true),(256,true),(258,false),(265,true),(272,true),(275,true)]
theorem inputList8799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8799 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 14) (closed_mem 4 14) inputClause8799 (by decide) v hb
mask_input "8799|463168356949264781694283940034751631413079938662562256157830336031652518559744|68356355488715228024297401323722113838750123041232008853678178328741788274072223744"
def inputClause8800 : CNF.NClause := [(249,true),(256,false),(258,true),(265,true),(272,true),(275,true)]
theorem inputList8800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8800 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 14) (closed_mem 4 14) inputClause8800 (by decide) v hb
mask_input "8800|115792089237316195423570985008687907853269984665640564039457584007913129639936|68356702864982939972883672036677139902473682851186005775370296701493812013461143552"
def inputClause8803 : CNF.NClause := [(263,true),(264,true),(265,true),(266,true),(267,false),(278,true)]
theorem inputList8803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8803 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 15) (closed_mem 4 15) inputClause8803 (by decide) v hb
mask_input "8803|237142198758023568227473377297792835283496928595231875152809132048206089502588928|485889543867767914825078732997096407443679988133592910195908860996021264510210801664"
def inputClause8804 : CNF.NClause := [(263,true),(264,true),(265,true),(266,false),(267,true),(278,true)]
theorem inputList8804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8804 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 15) (closed_mem 4 15) inputClause8804 (by decide) v hb
mask_input "8804|118571099379011784113736688648896417641748464297615937576404566024103044751294464|486008114967146926609192469685745303861321736597890526133485265562045367554962096128"
def inputClause8805 : CNF.NClause := [(263,true),(264,true),(265,false),(266,true),(267,true),(278,true)]
theorem inputList8805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8805 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 15) (closed_mem 4 15) inputClause8805 (by decide) v hb
mask_input "8805|59285549689505892056868344324448208820874232148807968788202283012051522375647232|486067400516836432501249338030069752070142610830039334102273467845057419077337743360"
def inputClause8806 : CNF.NClause := [(263,true),(264,false),(265,true),(266,true),(267,true),(278,true)]
theorem inputList8806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8806 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 15) (closed_mem 4 15) inputClause8806 (by decide) v hb
mask_input "8806|29642774844752946028434172162224104410437116074403984394101141506025761187823616|486097043291681185447277772202231976174553047946113738086667568986563444838525566976"
def inputClause8813 : CNF.NClause := [(252,false),(254,true),(261,true),(263,true),(270,true),(275,true)]
theorem inputList8813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8813 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 16) (closed_mem 4 16) inputClause8813 (by decide) v hb
mask_input "8813|7237005577332262213973186563042994240829374041602535252466099000494570602496|62624096154418501932369598856964950752076675664183883940728933938563675707708276736"
def inputClause8814 : CNF.NClause := [(250,true),(256,true),(262,true),(263,true),(269,true),(274,false)]
theorem inputList8814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8814 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 17) (closed_mem 4 17) inputClause8814 (by decide) v hb
mask_input "8814|30354201441027016733116592294117482916287606860189680019559568902170379456331382784|970918477506290631692196202594488868098229028764906530104664958431101715673513984"
def inputClause8818 : CNF.NClause := [(250,true),(256,false),(262,true),(263,true),(269,true),(274,true)]
theorem inputList8818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8818 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 17) (closed_mem 4 17) inputClause8818 (by decide) v hb
mask_input "8818|115792089237316195423570985008687907853269984665640564039457584007913129639936|31325004126444070048613364925726963096477982618969920909100194403017473258875256832"
def inputClause8819 : CNF.NClause := [(250,false),(256,true),(262,true),(263,true),(269,true),(274,true)]
theorem inputList8819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8819 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 17) (closed_mem 4 17) inputClause8819 (by decide) v hb
mask_input "8819|1809251394333065553493296640760748560207343510400633813116524750123642650624|31325118109281913031743235003415331023637275681611076149030420744076731048362246144"
def inputClause8820 : CNF.NClause := [(251,true),(255,true),(259,true),(263,true),(272,true),(277,false)]
theorem inputList8820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8820 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 18) (closed_mem 4 18) inputClause8820 (by decide) v hb
mask_input "8820|242833611528216133864932738352939863330300854881517440156476551217363035650651062272|7604359598940436510085572499576338149990993482641300743148904418809175253563998208"
def inputClause8821 : CNF.NClause := [(251,true),(255,true),(259,true),(263,true),(272,false),(277,true)]
theorem inputList8821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8821 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 18) (closed_mem 4 18) inputClause8821 (by decide) v hb
mask_input "8821|7588550360256754183279148073529370729071901715047420004889892225542594864082845696|242849420766899816191739162778986830751219946649111320894735563410629616040132214784"
def inputClause8822 : CNF.NClause := [(251,true),(255,true),(259,true),(263,false),(272,true),(277,true)]
theorem inputList8822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8822 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 18) (closed_mem 4 18) inputClause8822 (by decide) v hb
mask_input "8822|14821387422376473014217086081112052205218558037201992197050570753012880593911808|250423149739734193902004093766435089428086629806121538907428405065419198023621148672"
def inputClause8823 : CNF.NClause := [(251,true),(255,true),(259,false),(263,true),(272,true),(277,true)]
theorem inputList8823 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8823 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 18) (closed_mem 4 18) inputClause8823 (by decide) v hb
mask_input "8823|926336713898529563388567880069503262826159877325124512315660672063305037119488|250437044790442671845454922284636131977029022204281415775113139975500147599177940992"
def inputClause8825 : CNF.NClause := [(251,false),(255,true),(259,true),(263,true),(272,true),(277,true)]
theorem inputList8825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8825 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 18) (closed_mem 4 18) inputClause8825 (by decide) v hb
mask_input "8825|3618502788666131106986593281521497120414687020801267626233049500247285301248|250437967508653781708887203865922919958794727949471720098357829403122710656929759232"
end Percolation.MaskChain
