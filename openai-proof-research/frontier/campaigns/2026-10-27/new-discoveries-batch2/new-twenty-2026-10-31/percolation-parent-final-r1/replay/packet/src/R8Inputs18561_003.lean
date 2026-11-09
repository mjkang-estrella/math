import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause8536 : CNF.NClause := [(221,true),(226,false),(231,true),(236,true),(241,true),(242,true)]
theorem inputList8536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8536 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 1) (closed_mem 3 1) inputClause8536 (by decide) v hb
mask_input "8536|107839786668602559178668060348078522694548577690162289924414440996864|10714964573385683673822432809561967892384180883937577944461378995399688192"
def inputClause8539 : CNF.NClause := [(219,true),(224,true),(229,true),(234,true),(239,false),(242,true)]
theorem inputList8539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8539 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 2) (closed_mem 3 2) inputClause8539 (by decide) v hb
mask_input "8539|883423532389192164791648750371459257913741948437809479060803100646309888|7095885765239048893053646621262875282295428600317864421991841355691720704"
def inputClause8540 : CNF.NClause := [(219,true),(224,true),(229,true),(234,false),(239,true),(242,true)]
theorem inputList8540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8540 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 2) (closed_mem 3 2) inputClause8540 (by decide) v hb
mask_input "8540|27606985387162255149739023449108101809804435888681546220650096895197184|7951702312241078802695556348185226438399366112866992354831994359442833408"
def inputClause8541 : CNF.NClause := [(219,true),(224,true),(229,false),(234,true),(239,true),(242,true)]
theorem inputList8541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8541 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 2) (closed_mem 3 2) inputClause8541 (by decide) v hb
mask_input "8541|862718293348820473429344482784628181556388621521298319395315527974912|7978446579334892237371866027151549912027614160134152602733249140810055680"
def inputClause8542 : CNF.NClause := [(219,true),(224,false),(229,true),(234,true),(239,true),(242,true)]
theorem inputList8542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8542 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 2) (closed_mem 3 2) inputClause8542 (by decide) v hb
mask_input "8542|26959946667150639794667015087019630673637144422540572481103610249216|7979282337681573907205500704619247520578496911611251360480163352727781376"
def inputClause8551 : CNF.NClause := [(218,true),(223,true),(228,true),(233,true),(238,false),(242,true)]
theorem inputList8551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8551 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 4) (closed_mem 3 4) inputClause8551 (by decide) v hb
mask_input "8551|441711766194596082395824375185729628956870974218904739530401550323154944|7081637012176293105693418312117274672802682093910170127239133080431099904"
def inputClause8552 : CNF.NClause := [(218,true),(223,true),(228,true),(233,false),(238,true),(242,true)]
theorem inputList8552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8552 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 4) (closed_mem 3 4) inputClause8552 (by decide) v hb
mask_input "8552|13803492693581127574869511724554050904902217944340773110325048447598592|7509545285677308060514373175578450250854650850184734093659209582306656256"
def inputClause8554 : CNF.NClause := [(218,true),(223,false),(228,true),(233,true),(238,true),(242,true)]
theorem inputList8554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8554 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 4) (closed_mem 3 4) inputClause8554 (by decide) v hb
mask_input "8554|13479973333575319897333507543509815336818572211270286240551805124608|7523335298397555612769345353795460791944216249556863596483294078949130240"
def inputClause8562 : CNF.NClause := [(221,true),(225,true),(229,true),(233,true),(237,true),(246,false)]
theorem inputList8562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8562 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 6) (closed_mem 3 6) inputClause8562 (by decide) v hb
mask_input "8562|113078212145816597093331040047546785012958969400039613319782796882727665664|235579383970895684355774711207263410280075572607212339911443484308930560"
def inputClause8564 : CNF.NClause := [(221,true),(225,true),(229,true),(233,false),(237,true),(246,true)]
theorem inputList8564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8564 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 6) (closed_mem 3 6) inputClause8564 (by decide) v hb
mask_input "8564|13803492693581127574869511724554050904902217944340773110325048447598592|113299988037093911650111945247029494372334142754702484886583915318588997632"
def inputClause8565 : CNF.NClause := [(221,true),(225,true),(229,false),(233,true),(237,true),(246,true)]
theorem inputList8565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8565 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 6) (closed_mem 3 6) inputClause8565 (by decide) v hb
mask_input "8565|862718293348820473429344482784628181556388621521298319395315527974912|113312928811494143957213385414271263795057488584025304361374845051508621312"
def inputClause8569 : CNF.NClause := [(219,true),(226,true),(228,true),(235,true),(237,false),(244,true)]
theorem inputList8569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8569 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 7) (closed_mem 3 7) inputClause8569 (by decide) v hb
mask_input "8569|220855883097298041197912187592864814478435487109452369765200775161577472|28325307048660150144885624982430874318836282515836480438229511521165115392"
def inputClause8572 : CNF.NClause := [(219,true),(226,false),(228,true),(235,true),(237,true),(244,true)]
theorem inputList8572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8572 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 7) (closed_mem 3 7) inputClause8572 (by decide) v hb
mask_input "8572|107839786668602559178668060348078522694548577690162289924414440996864|28546055091970779583524358501963391054792023454368242645704787881885696000"
def inputClause8573 : CNF.NClause := [(219,false),(226,true),(228,true),(235,true),(237,true),(244,true)]
theorem inputList8573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8573 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 7) (closed_mem 3 7) inputClause8573 (by decide) v hb
mask_input "8573|842498333348457493583344221469363458551160763204392890034487820288|28546162089259114837626043586679517663951259451785169603601822261838872576"
def inputClause8587 : CNF.NClause := [(227,true),(228,true),(229,true),(230,true),(231,false),(247,true)]
theorem inputList8587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8587 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 10) (closed_mem 3 10) inputClause8587 (by decide) v hb
mask_input "8587|3450873173395281893717377931138512726225554486085193277581262111899648|226159659485233252263437440136904012381598775257409931508263326198685237248"
def inputClause8588 : CNF.NClause := [(227,true),(228,true),(229,true),(230,false),(231,true),(247,true)]
theorem inputList8588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8588 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 10) (closed_mem 3 10) inputClause8588 (by decide) v hb
mask_input "8588|1725436586697640946858688965569256363112777243042596638790631055949824|226161384921819949904384298825869581637961888034652974104902116829741187072"
def inputClause8589 : CNF.NClause := [(227,true),(228,true),(229,false),(230,true),(231,true),(247,true)]
theorem inputList8589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8589 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 10) (closed_mem 3 10) inputClause8589 (by decide) v hb
mask_input "8589|862718293348820473429344482784628181556388621521298319395315527974912|226162247640113298724857728170352366266143444423274495403221512145269161984"
def inputClause8592 : CNF.NClause := [(221,true),(224,true),(227,true),(235,true),(238,true),(245,false)]
theorem inputList8592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8592 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 11) (closed_mem 3 11) inputClause8592 (by decide) v hb
mask_input "8592|56539106072908298546665520023773392506479484700019806659891398441363832832|497171746482258342283428758596614886706376784939123514695591814557073408"
def inputClause8593 : CNF.NClause := [(221,true),(224,true),(227,true),(235,true),(238,false),(245,true)]
theorem inputList8593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8593 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 11) (closed_mem 3 11) inputClause8593 (by decide) v hb
mask_input "8593|441711766194596082395824375185729628956870974218904739530401550323154944|56594566053195960806553124407184277764228990510740025435056588705597751296"
def inputClause8594 : CNF.NClause := [(221,true),(224,true),(227,true),(235,false),(238,true),(245,true)]
theorem inputList8594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8594 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 11) (closed_mem 3 11) inputClause8594 (by decide) v hb
mask_input "8594|55213970774324510299478046898216203619608871777363092441300193790394368|56981063848616232378649470735471791189566252613181567082145690062130511872"
def inputClause8596 : CNF.NClause := [(221,true),(224,false),(227,true),(235,true),(238,true),(245,true)]
theorem inputList8596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8596 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 11) (closed_mem 3 11) inputClause8596 (by decide) v hb
mask_input "8596|26959946667150639794667015087019630673637144422540572481103610249216|57036250859443889738309154115354920373555187847814507634014509152310657024"
def inputClause8598 : CNF.NClause := [(219,true),(223,true),(227,true),(236,true),(240,true),(246,false)]
theorem inputList8598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8598 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 12) (closed_mem 3 12) inputClause8598 (by decide) v hb
mask_input "8598|113078212145816597093331040047546785012958969400039613319782796882727665664|1877505008372037479078001847511812059290886107318699942263186004048347136"
def inputClause8599 : CNF.NClause := [(219,true),(223,true),(227,true),(236,true),(240,false),(246,true)]
theorem inputList8599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8599 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 12) (closed_mem 3 12) inputClause8599 (by decide) v hb
mask_input "8599|1766847064778384329583297500742918515827483896875618958121606201292619776|113188870089410250242825744394315678556422371610482694303924376685483393024"
def inputClause8600 : CNF.NClause := [(219,true),(223,true),(227,true),(236,false),(240,true),(246,true)]
theorem inputList8600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8600 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 12) (closed_mem 3 12) inputClause8600 (by decide) v hb
mask_input "8600|110427941548649020598956093796432407239217743554726184882600387580788736|114845289212639985551810085801262164665010637763803587077163382499195224064"
def inputClause8602 : CNF.NClause := [(219,true),(223,false),(227,true),(236,true),(240,true),(246,true)]
theorem inputList8602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8602 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 12) (closed_mem 3 12) inputClause8602 (by decide) v hb
mask_input "8602|13479973333575319897333507543509815336818572211270286240551805124608|114955703674215300997089144561551053562434518688786101991759742334970888192"
def inputClause8603 : CNF.NClause := [(219,false),(223,true),(227,true),(236,true),(240,true),(246,true)]
theorem inputList8603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8603 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 12) (closed_mem 3 12) inputClause8603 (by decide) v hb
mask_input "8603|842498333348457493583344221469363458551160763204392890034487820288|114955716311690301223951548311714375602886396956197550057653092852288192512"
def inputClause8611 : CNF.NClause := [(218,true),(225,true),(227,true),(234,true),(241,false),(244,true)]
theorem inputList8611 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8611 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 14) (closed_mem 3 14) inputClause8611 (by decide) v hb
mask_input "8611|3533694129556768659166595001485837031654967793751237916243212402585239552|28297430042557149709109192497158785286038012432923191884087605370923515904"
def inputClause8612 : CNF.NClause := [(218,true),(225,true),(227,true),(234,false),(241,true),(244,true)]
theorem inputList8612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8612 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 14) (closed_mem 3 14) inputClause8612 (by decide) v hb
mask_input "8612|27606985387162255149739023449108101809804435888681546220650096895197184|31803517186726756113126048475195514215883175790785748254110167676613558272"
def inputClause8615 : CNF.NClause := [(218,false),(225,true),(227,true),(234,true),(241,true),(244,true)]
theorem inputList8615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8615 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 14) (closed_mem 3 14) inputClause8615 (by decide) v hb
mask_input "8615|421249166674228746791672110734681729275580381602196445017243910144|31831123750864751694047040706972511583011250951094048198134372756264845312"
def inputClause8624 : CNF.NClause := [(221,true),(223,true),(230,true),(232,false),(239,true),(244,true)]
theorem inputList8624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8624 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 16) (closed_mem 3 16) inputClause8624 (by decide) v hb
mask_input "8624|6901746346790563787434755862277025452451108972170386555162524223799296|29154718855396706048221139118108154154785768098906019493503093642140581888"
def inputClause8629 : CNF.NClause := [(219,true),(225,true),(231,true),(232,true),(238,false),(243,true)]
theorem inputList8629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8629 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 17) (closed_mem 3 17) inputClause8629 (by decide) v hb
mask_input "8629|441711766194596082395824375185729628956870974218904739530401550323154944|14145183900138928132084615057111159173423353663912815530343445638384975872"
def inputClause8630 : CNF.NClause := [(219,true),(225,true),(231,true),(232,false),(238,true),(243,true)]
theorem inputList8630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8630 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 17) (closed_mem 3 17) inputClause8630 (by decide) v hb
mask_input "8630|6901746346790563787434755862277025452451108972170386555162524223799296|14579993919986733650693004676434611776927773529159549883318684664484331520"
def inputClause8631 : CNF.NClause := [(219,true),(225,true),(231,false),(232,true),(238,true),(243,true)]
theorem inputList8631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8631 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 17) (closed_mem 3 17) inputClause8631 (by decide) v hb
mask_input "8631|3450873173395281893717377931138512726225554486085193277581262111899648|14583444793160128932586722054365750289653999083645635076596265926596231168"
def inputClause8633 : CNF.NClause := [(219,false),(225,true),(231,true),(232,true),(238,true),(243,true)]
theorem inputList8633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8633 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 17) (closed_mem 3 17) inputClause8633 (by decide) v hb
mask_input "8633|842498333348457493583344221469363458551160763204392890034487820288|14586894823835190866022945848952667333016766086970957065480957154220310528"
def inputClause8641 : CNF.NClause := [(218,true),(226,true),(229,true),(232,true),(240,false),(245,true)]
theorem inputList8641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8641 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 19) (closed_mem 3 19) inputClause8641 (by decide) v hb
mask_input "8641|1766847064778384329583297500742918515827483896875618958121606201292619776|56546978798584273207714309583850912973317916021771570109252325712800514048"
def inputClause8642 : CNF.NClause := [(218,true),(226,true),(229,true),(232,false),(240,true),(245,true)]
theorem inputList8642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8642 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 19) (closed_mem 3 19) inputClause8642 (by decide) v hb
mask_input "8642|6901746346790563787434755862277025452451108972170386555162524223799296|58306924117015866973510172328731554463692948809675018680818769389869334528"
def inputClause8644 : CNF.NClause := [(218,true),(226,false),(229,true),(232,true),(240,true),(245,true)]
theorem inputList8644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8644 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 19) (closed_mem 3 19) inputClause8644 (by decide) v hb
mask_input "8644|107839786668602559178668060348078522694548577690162289924414440996864|58313718023575988934738428416533483410622705370069498905084007499652136960"
def inputClause8647 : CNF.NClause := [(222,true),(223,true),(224,true),(225,true),(226,false),(247,true)]
theorem inputList8647 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8647 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 20) (closed_mem 3 20) inputClause8647 (by decide) v hb
mask_input "8647|107839786668602559178668060348078522694548577690162289924414440996864|226156525391433196001561310096400146349532964939370811166712397903993765888"
def inputClause8649 : CNF.NClause := [(222,true),(223,true),(224,false),(225,true),(226,true),(247,true)]
theorem inputList8649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8649 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 20) (closed_mem 3 20) inputClause8649 (by decide) v hb
mask_input "8649|26959946667150639794667015087019630673637144422540572481103610249216|226156606271273197453480694097445407408424985850804078788429841214824513536"
def inputClause8653 : CNF.NClause := [(221,true),(222,true),(228,true),(234,true),(240,false),(243,true)]
theorem inputList8653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8653 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 21) (closed_mem 3 21) inputClause8653 (by decide) v hb
mask_input "8653|1766847064778384329583297500742918515827483896875618958121606201292619776|14162824972740911483542756701764506174881956419133552313067877778853986304"
end Percolation.MaskChain
