import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause8826 : CNF.NClause := [(249,true),(257,true),(260,true),(263,true),(271,true),(276,false)]
theorem inputList8826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8826 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 19) (closed_mem 4 19) inputClause8826 (by decide) v hb
mask_input "8826|121416805764108066932466369176469931665150427440758720078238275608681517825325531136|3811181729782722422704192147224274179456808378956648725111613478298827810790178816"
def inputClause8828 : CNF.NClause := [(249,true),(257,true),(260,true),(263,false),(271,true),(276,true)]
theorem inputList8828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8828 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 19) (closed_mem 4 19) inputClause8828 (by decide) v hb
mask_input "8828|14821387422376473014217086081112052205218558037201992197050570753012880593911808|125213166106468412882156344237613093792402017261678166811152838516227332755521798144"
def inputClause8831 : CNF.NClause := [(249,false),(257,true),(260,true),(263,true),(271,true),(276,true)]
theorem inputList8831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8831 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 19) (closed_mem 4 19) inputClause8831 (by decide) v hb
mask_input "8831|904625697166532776746648320380374280103671755200316906558262375061821325312|125227986589265092188637784577045885464232955716043613603032982528717970574294384640"
def inputClause8833 : CNF.NClause := [(253,true),(254,true),(255,true),(256,true),(257,false),(278,true)]
theorem inputList8833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8833 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 20) (closed_mem 4 20) inputClause8833 (by decide) v hb
mask_input "8833|231584178474632390847141970017375815706539969331281128078915168015826259279872|485667440166599587697731895901476617950428934644256128389010676417696086138420199424"
def inputClause8834 : CNF.NClause := [(253,true),(254,true),(255,true),(256,false),(257,true),(278,true)]
theorem inputList8834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8834 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 20) (closed_mem 4 20) inputClause8834 (by decide) v hb
mask_input "8834|115792089237316195423570985008687907853269984665640564039457584007913129639936|485667555958688825013927319472461626638336787914240794029574715875280094051549839360"
def inputClause8835 : CNF.NClause := [(253,true),(254,true),(255,false),(256,true),(257,true),(278,true)]
theorem inputList8835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8835 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 20) (closed_mem 4 20) inputClause8835 (by decide) v hb
mask_input "8835|57896044618658097711785492504343953926634992332820282019728792003956564819968|485667613854733443672025031257954130982290714549233126849856735604072098008114659328"
def inputClause8836 : CNF.NClause := [(253,true),(254,false),(255,true),(256,true),(257,true),(278,true)]
theorem inputList8836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8836 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 20) (closed_mem 4 20) inputClause8836 (by decide) v hb
mask_input "8836|28948022309329048855892746252171976963317496166410141009864396001978282409984|485667642802755753001073887150700383154267677866729293259997745468468099986397069312"
def inputClause8843 : CNF.NClause := [(252,false),(253,true),(259,true),(265,true),(271,true),(274,true)]
theorem inputList8843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8843 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 21) (closed_mem 4 21) inputClause8843 (by decide) v hb
mask_input "8843|7237005577332262213973186563042994240829374041602535252466099000494570602496|34208702981569952910900851189459812078895739768487606320375537890823792704926777344"
def inputClause8844 : CNF.NClause := [(250,true),(253,true),(261,true),(264,true),(272,true),(276,false)]
theorem inputList8844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8844 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 22) (closed_mem 4 22) inputClause8844 (by decide) v hb
mask_input "8844|121416805764108066932466369176469931665150427440758720078238275608681517825325531136|7621914765219650245151117956881639693270685336722718093037574058459624958203002880"
def inputClause8847 : CNF.NClause := [(250,true),(253,true),(261,false),(264,true),(272,true),(276,true)]
theorem inputList8847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8847 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 22) (closed_mem 4 22) inputClause8847 (by decide) v hb
mask_input "8847|3705346855594118253554271520278013051304639509300498049262642688253220148477952|129035015182472123059363932861831293345369808137972137673226587024452889563380056064"
def inputClause8848 : CNF.NClause := [(250,true),(253,false),(261,true),(264,true),(272,true),(276,true)]
theorem inputList8848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8848 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 22) (closed_mem 4 22) inputClause8848 (by decide) v hb
mask_input "8848|14474011154664524427946373126085988481658748083205070504932198000989141204992|129038706055316562513093059186978445272432631118733354966205344734943141794387329024"
def inputClause8852 : CNF.NClause := [(251,true),(253,true),(260,true),(267,false),(269,true),(275,true)]
theorem inputList8852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8852 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 23) (closed_mem 4 23) inputClause8852 (by decide) v hb
mask_input "8852|237142198758023568227473377297792835283496928595231875152809132048206089502588928|61658842443027868128925390166152683787720455827950041795093136819125211117173866496"
def inputClause8853 : CNF.NClause := [(251,true),(253,true),(260,false),(267,true),(269,true),(275,true)]
theorem inputList8853 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8853 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 23) (closed_mem 4 23) inputClause8853 (by decide) v hb
mask_input "8853|1852673427797059126777135760139006525652319754650249024631321344126610074238976|61894131968358094638026086407690337616478300436790623421221314629829290596602216448"
def inputClause8855 : CNF.NClause := [(251,false),(253,true),(260,true),(267,true),(269,true),(275,true)]
theorem inputList8855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8855 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 23) (closed_mem 4 23) inputClause8855 (by decide) v hb
mask_input "8855|3618502788666131106986593281521497120414687020801267626233049500247285301248|61895981023283103031021756556857195101506832341858252868978319718123916959391154176"
def inputClause8857 : CNF.NClause := [(249,true),(253,true),(262,true),(266,true),(270,false),(277,true)]
theorem inputList8857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8857 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 24) (closed_mem 4 24) inputClause8857 (by decide) v hb
mask_input "8857|1897137590064188545819787018382342682267975428761855001222473056385648716020711424|242959608699943185716610788277650762240407974387253495495538892559224021186661842944"
def inputClause8858 : CNF.NClause := [(249,true),(253,true),(262,true),(266,false),(270,true),(277,true)]
theorem inputList8858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8858 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 24) (closed_mem 4 24) inputClause8858 (by decide) v hb
mask_input "8858|118571099379011784113736688648896417641748464297615937576404566024103044751294464|244738175190628362478316838607384208505034201351717734559184961049585566857931259904"
def inputClause8859 : CNF.NClause := [(249,true),(253,true),(262,false),(266,true),(270,true),(277,true)]
theorem inputList8859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8859 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 24) (closed_mem 4 24) inputClause8859 (by decide) v hb
mask_input "8859|7410693711188236507108543040556026102609279018600996098525285376506440296955904|244849335596296186025923466752992548896573340536996749500662840330233163462385598464"
def inputClause8860 : CNF.NClause := [(249,true),(253,false),(262,true),(266,true),(270,true),(277,true)]
theorem inputList8860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8860 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 24) (closed_mem 4 24) inputClause8860 (by decide) v hb
mask_input "8860|14474011154664524427946373126085988481658748083205070504932198000989141204992|244856731815996219597906147349659978836687468157267267291690860683411668913541349376"
def inputClause8861 : CNF.NClause := [(249,false),(253,true),(262,true),(266,true),(270,true),(277,true)]
theorem inputList8861 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8861 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 24) (closed_mem 4 24) inputClause8861 (by decide) v hb
mask_input "8861|904625697166532776746648320380374280103671755200316906558262375061821325312|244856745385381677095897798549384784542301669712343595296444459057347294840861229056"
def inputClause8863 : CNF.NClause := [(248,true),(249,true),(250,true),(251,true),(252,false),(278,true)]
theorem inputList8863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8863 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 25) (closed_mem 4 25) inputClause8863 (by decide) v hb
mask_input "8863|7237005577332262213973186563042994240829374041602535252466099000494570602496|485667229841124996478861302305742129513408810540573044315329901621693884264962064384"
def inputClause8868 : CNF.NClause := [(248,true),(257,true),(261,true),(265,true),(269,true),(277,false)]
theorem inputList8868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8868 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 26) (closed_mem 4 26) inputClause8868 (by decide) v hb
mask_input "8868|242833611528216133864932738352939863330300854881517440156476551217363035650651062272|1011791728068517498877551640330075129009013177844244848735233648192332457704423424"
def inputClause8869 : CNF.NClause := [(248,true),(257,true),(261,true),(265,true),(269,false),(277,true)]
theorem inputList8869 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8869 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 26) (closed_mem 4 26) inputClause8869 (by decide) v hb
mask_input "8869|948568795032094272909893509191171341133987714380927500611236528192824358010355712|242896834461252557090900396484078767118175880344980757504600548337362543750345129984"
def inputClause8870 : CNF.NClause := [(248,true),(257,true),(261,true),(265,false),(269,true),(277,true)]
theorem inputList8870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8870 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 26) (closed_mem 4 26) inputClause8870 (by decide) v hb
mask_input "8870|59285549689505892056868344324448208820874232148807968788202283012051522375647232|243786117706595145471753421648945490250488993827212877036423582582543316585979838464"
def inputClause8871 : CNF.NClause := [(248,true),(257,true),(261,false),(265,true),(269,true),(277,true)]
theorem inputList8871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8871 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 26) (closed_mem 4 26) inputClause8871 (by decide) v hb
mask_input "8871|3705346855594118253554271520278013051304639509300498049262642688253220148477952|243841697909429057245556735721749660446258563419852384507162522222867114888207007744"
def inputClause8872 : CNF.NClause := [(248,true),(257,false),(261,true),(265,true),(269,true),(277,true)]
theorem inputList8872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8872 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 26) (closed_mem 4 26) inputClause8872 (by decide) v hb
mask_input "8872|231584178474632390847141970017375815706539969331281128078915168015826259279872|243845171672106176731419442851299921083494161519392353724083705950387352282096205824"
def inputClause8876 : CNF.NClause := [(248,true),(255,true),(262,true),(264,false),(271,true),(275,true)]
theorem inputList8876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8876 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 27) (closed_mem 4 27) inputClause8876 (by decide) v hb
mask_input "8876|29642774844752946028434172162224104410437116074403984394101141506025761187823616|64510147104251066035743967326856871757354840543749881458103082210411754272476626944"
def inputClause8877 : CNF.NClause := [(248,true),(255,true),(262,false),(264,true),(271,true),(275,true)]
theorem inputList8877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8877 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 27) (closed_mem 4 27) inputClause8877 (by decide) v hb
mask_input "8877|7410693711188236507108543040556026102609279018600996098525285376506440296955904|64532379185384630745265292955978539835662668380805684446398658066541273593367494656"
def inputClause8881 : CNF.NClause := [(248,true),(256,true),(259,true),(267,true),(270,false),(276,true)]
theorem inputList8881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8881 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 28) (closed_mem 4 28) inputClause8881 (by decide) v hb
mask_input "8881|1897137590064188545819787018382342682267975428761855001222473056385648716020711424|121654990543982074929719043065956962881791743851051820318625893138116982663905542144"
def inputClause8883 : CNF.NClause := [(248,true),(256,true),(259,false),(267,true),(270,true),(276,true)]
theorem inputList8883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8883 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 28) (closed_mem 4 28) inputClause8883 (by decide) v hb
mask_input "8883|926336713898529563388567880069503262826159877325124512315660672063305037119488|123551201797332364945975441516459236060796893119936350195336050533830568074889134080"
def inputClause8884 : CNF.NClause := [(248,true),(256,false),(259,true),(267,true),(270,true),(276,true)]
theorem inputList8884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8884 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 28) (closed_mem 4 28) inputClause8884 (by decide) v hb
mask_input "8884|115792089237316195423570985008687907853269984665640564039457584007913129639936|123552012341957026159343406513354296876151866009829009679284326736918623466796613632"
def inputClause8886 : CNF.NClause := [(248,true),(254,true),(260,true),(266,true),(272,true),(274,false)]
theorem inputList8886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8886 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 29) (closed_mem 4 29) inputClause8886 (by decide) v hb
mask_input "8886|30354201441027016733116592294117482916287606860189680019559568902170379456331382784|7709003533398720938834906164008818515403405868431730201790391256438014028101451776"
def inputClause8887 : CNF.NClause := [(248,true),(254,true),(260,true),(266,true),(272,false),(274,true)]
theorem inputList8887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8887 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 29) (closed_mem 4 29) inputClause8887 (by decide) v hb
mask_input "8887|7588550360256754183279148073529370729071901715047420004889892225542594864082845696|30474654614168983488672350384596930702619111013573990216460067933065798620349988864"
def inputClause8888 : CNF.NClause := [(248,true),(254,true),(260,true),(266,false),(272,true),(274,true)]
theorem inputList8888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8888 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 29) (closed_mem 4 29) inputClause8888 (by decide) v hb
mask_input "8888|118571099379011784113736688648896417641748464297615937576404566024103044751294464|37944633875046725887837761769477405014049264264323794283773555592584290439681540096"
def inputClause8890 : CNF.NClause := [(248,true),(254,false),(260,true),(266,true),(272,true),(274,true)]
theorem inputList8890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8890 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 29) (closed_mem 4 29) inputClause8890 (by decide) v hb
mask_input "8890|28948022309329048855892746252171976963317496166410141009864396001978282409984|38063176026403428342902642565380049259714049411125243811208950294212391506150424576"
def inputClause8893 : CNF.NClause := [(248,true),(253,true),(258,true),(263,true),(268,false),(273,true)]
theorem inputList8893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8893 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 30) (closed_mem 4 30) inputClause8893 (by decide) v hb
mask_input "8893|474284397516047136454946754595585670566993857190463750305618264096412179005177856|15192400202616837352145023836777174538156056778654665369461951063503422781330030592"
def inputClause8894 : CNF.NClause := [(248,true),(253,true),(258,true),(263,false),(268,true),(273,true)]
theorem inputList8894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8894 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 30) (closed_mem 4 30) inputClause8894 (by decide) v hb
mask_input "8894|14821387422376473014217086081112052205218558037201992197050570753012880593911808|15651863212710508015585753505291648156517832077807927127570518756846822079741296640"
def inputClause8895 : CNF.NClause := [(248,true),(253,true),(258,false),(263,true),(268,true),(273,true)]
theorem inputList8895 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8895 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 30) (closed_mem 4 30) inputClause8895 (by decide) v hb
mask_input "8895|463168356949264781694283940034751631413079938662562256157830336031652518559744|15666221431775935223818276307432725457091637555906466557511411497263803307816648704"
def inputClause8896 : CNF.NClause := [(248,true),(253,false),(258,true),(263,true),(268,true),(273,true)]
theorem inputList8896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8896 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 30) (closed_mem 4 30) inputClause8896 (by decide) v hb
mask_input "8896|14474011154664524427946373126085988481658748083205070504932198000989141204992|15666670126121729824075542644999634122734568977097045914697064395401833971194003456"
def inputClause8899 : CNF.NClause := [(304,true),(305,true),(306,true),(307,true),(308,false),(309,true)]
theorem inputList8899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8899 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 0) (closed_mem 5 0) inputClause8899 (by decide) v hb
mask_input "8899|521481209941628438084722096232800809229175908778479680162851955034721612739414196782949728256|1531851054203533536873871157683852377110704232036784060478377617914494737422029203049914826752"
def inputClause8900 : CNF.NClause := [(304,true),(305,true),(306,true),(307,false),(308,true),(309,true)]
theorem inputList8900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause8900 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 0) (closed_mem 5 0) inputClause8900 (by decide) v hb
mask_input "8900|260740604970814219042361048116400404614587954389239840081425977517360806369707098391474864128|1792591659174347755916232205800252781725292186426023900559803595431855543791736301441389690880"
end Percolation.MaskChain
