import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause13857 : CNF.NClause := [(3,true),(1,true),(218,false)]
theorem inputList13857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13857 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13857
  have he : decodeClause inputClause13857 = containClause5 3 1 := by decide
  rw [he]
  exact input_contain 3 1 (by decide) v hb
mask_input "13857|421249166674228746791672110734681729275580381602196445017243910144|10"
def inputClause13858 : CNF.NClause := [(3,true),(2,true),(219,false)]
theorem inputList13858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13858 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13858
  have he : decodeClause inputClause13858 = containClause5 3 2 := by decide
  rw [he]
  exact input_contain 3 2 (by decide) v hb
mask_input "13858|842498333348457493583344221469363458551160763204392890034487820288|12"
def inputClause13859 : CNF.NClause := [(3,true),(4,true),(221,false)]
theorem inputList13859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13859 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13859 = (containClause5 3 4) := by decide
  rw [he]
  exact input_contain 3 4 (by decide) v hb
mask_input "13859|3369993333393829974333376885877453834204643052817571560137951281152|24"
def inputClause13860 : CNF.NClause := [(3,true),(5,true),(222,false)]
theorem inputList13860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13860 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13860
  have he : decodeClause inputClause13860 = containClause5 3 5 := by decide
  rw [he]
  exact input_contain 3 5 (by decide) v hb
mask_input "13860|6739986666787659948666753771754907668409286105635143120275902562304|40"
def inputClause13863 : CNF.NClause := [(3,true),(8,true),(225,false)]
theorem inputList13863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13863 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13863 = (containClause5 3 8) := by decide
  rw [he]
  exact input_contain 3 8 (by decide) v hb
mask_input "13863|53919893334301279589334030174039261347274288845081144962207220498432|264"
def inputClause13865 : CNF.NClause := [(3,true),(10,true),(227,false)]
theorem inputList13865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13865 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13865 = (containClause5 3 10) := by decide
  rw [he]
  exact input_contain 3 10 (by decide) v hb
mask_input "13865|215679573337205118357336120696157045389097155380324579848828881993728|1032"
def inputClause13866 : CNF.NClause := [(3,true),(11,true),(228,false)]
theorem inputList13866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13866 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13866 = (containClause5 3 11) := by decide
  rw [he]
  exact input_contain 3 11 (by decide) v hb
mask_input "13866|431359146674410236714672241392314090778194310760649159697657763987456|2056"
def inputClause13887 : CNF.NClause := [(4,true),(1,true),(249,false)]
theorem inputList13887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13887 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13887 = (containClause5 4 1) := by decide
  rw [he]
  exact input_contain 4 1 (by decide) v hb
mask_input "13887|904625697166532776746648320380374280103671755200316906558262375061821325312|18"
def inputClause13888 : CNF.NClause := [(4,true),(2,true),(250,false)]
theorem inputList13888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13888 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13888 = (containClause5 4 2) := by decide
  rw [he]
  exact input_contain 4 2 (by decide) v hb
mask_input "13888|1809251394333065553493296640760748560207343510400633813116524750123642650624|20"
def inputClause13889 : CNF.NClause := [(4,true),(3,true),(251,false)]
theorem inputList13889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13889 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13889 = (containClause5 4 3) := by decide
  rw [he]
  exact input_contain 4 3 (by decide) v hb
mask_input "13889|3618502788666131106986593281521497120414687020801267626233049500247285301248|24"
def inputClause13890 : CNF.NClause := [(4,true),(5,true),(253,false)]
theorem inputList13890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13890 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13890 = (containClause5 4 5) := by decide
  rw [he]
  exact input_contain 4 5 (by decide) v hb
mask_input "13890|14474011154664524427946373126085988481658748083205070504932198000989141204992|48"
def inputClause13891 : CNF.NClause := [(4,true),(6,true),(254,false)]
theorem inputList13891 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13891 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13891 = (containClause5 4 6) := by decide
  rw [he]
  exact input_contain 4 6 (by decide) v hb
mask_input "13891|28948022309329048855892746252171976963317496166410141009864396001978282409984|80"
def inputClause13892 : CNF.NClause := [(4,true),(7,true),(255,false)]
theorem inputList13892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13892 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13892 = (containClause5 4 7) := by decide
  rw [he]
  exact input_contain 4 7 (by decide) v hb
mask_input "13892|57896044618658097711785492504343953926634992332820282019728792003956564819968|144"
def inputClause13893 : CNF.NClause := [(4,true),(8,true),(256,false)]
theorem inputList13893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13893 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13893 = (containClause5 4 8) := by decide
  rw [he]
  exact input_contain 4 8 (by decide) v hb
mask_input "13893|115792089237316195423570985008687907853269984665640564039457584007913129639936|272"
def inputClause13894 : CNF.NClause := [(4,true),(9,true),(257,false)]
theorem inputList13894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13894 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13894 = (containClause5 4 9) := by decide
  rw [he]
  exact input_contain 4 9 (by decide) v hb
mask_input "13894|231584178474632390847141970017375815706539969331281128078915168015826259279872|528"
def inputClause13895 : CNF.NClause := [(4,true),(10,true),(258,false)]
theorem inputList13895 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13895 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13895 = (containClause5 4 10) := by decide
  rw [he]
  exact input_contain 4 10 (by decide) v hb
mask_input "13895|463168356949264781694283940034751631413079938662562256157830336031652518559744|1040"
def inputClause13896 : CNF.NClause := [(4,true),(11,true),(259,false)]
theorem inputList13896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13896 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13896 = (containClause5 4 11) := by decide
  rw [he]
  exact input_contain 4 11 (by decide) v hb
mask_input "13896|926336713898529563388567880069503262826159877325124512315660672063305037119488|2064"
def inputClause13897 : CNF.NClause := [(4,true),(12,true),(260,false)]
theorem inputList13897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13897 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13897 = (containClause5 4 12) := by decide
  rw [he]
  exact input_contain 4 12 (by decide) v hb
mask_input "13897|1852673427797059126777135760139006525652319754650249024631321344126610074238976|4112"
def inputClause13898 : CNF.NClause := [(4,true),(13,true),(261,false)]
theorem inputList13898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13898 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13898 = (containClause5 4 13) := by decide
  rw [he]
  exact input_contain 4 13 (by decide) v hb
mask_input "13898|3705346855594118253554271520278013051304639509300498049262642688253220148477952|8208"
def inputClause13899 : CNF.NClause := [(4,true),(14,true),(262,false)]
theorem inputList13899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13899 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13899 = (containClause5 4 14) := by decide
  rw [he]
  exact input_contain 4 14 (by decide) v hb
mask_input "13899|7410693711188236507108543040556026102609279018600996098525285376506440296955904|16400"
def inputClause13900 : CNF.NClause := [(4,true),(15,true),(263,false)]
theorem inputList13900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13900 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13900 = (containClause5 4 15) := by decide
  rw [he]
  exact input_contain 4 15 (by decide) v hb
mask_input "13900|14821387422376473014217086081112052205218558037201992197050570753012880593911808|32784"
def inputClause13901 : CNF.NClause := [(4,true),(16,true),(264,false)]
theorem inputList13901 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13901 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13901 = (containClause5 4 16) := by decide
  rw [he]
  exact input_contain 4 16 (by decide) v hb
mask_input "13901|29642774844752946028434172162224104410437116074403984394101141506025761187823616|65552"
def inputClause13902 : CNF.NClause := [(4,true),(17,true),(265,false)]
theorem inputList13902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13902 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13902 = (containClause5 4 17) := by decide
  rw [he]
  exact input_contain 4 17 (by decide) v hb
mask_input "13902|59285549689505892056868344324448208820874232148807968788202283012051522375647232|131088"
def inputClause13903 : CNF.NClause := [(4,true),(18,true),(266,false)]
theorem inputList13903 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13903 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13903 = (containClause5 4 18) := by decide
  rw [he]
  exact input_contain 4 18 (by decide) v hb
mask_input "13903|118571099379011784113736688648896417641748464297615937576404566024103044751294464|262160"
def inputClause13904 : CNF.NClause := [(4,true),(19,true),(267,false)]
theorem inputList13904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13904 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13904 = (containClause5 4 19) := by decide
  rw [he]
  exact input_contain 4 19 (by decide) v hb
mask_input "13904|237142198758023568227473377297792835283496928595231875152809132048206089502588928|524304"
def inputClause13905 : CNF.NClause := [(4,true),(20,true),(268,false)]
theorem inputList13905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13905 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13905 = (containClause5 4 20) := by decide
  rw [he]
  exact input_contain 4 20 (by decide) v hb
mask_input "13905|474284397516047136454946754595585670566993857190463750305618264096412179005177856|1048592"
def inputClause13906 : CNF.NClause := [(4,true),(21,true),(269,false)]
theorem inputList13906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13906 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13906 = (containClause5 4 21) := by decide
  rw [he]
  exact input_contain 4 21 (by decide) v hb
mask_input "13906|948568795032094272909893509191171341133987714380927500611236528192824358010355712|2097168"
def inputClause13907 : CNF.NClause := [(4,true),(22,true),(270,false)]
theorem inputList13907 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13907 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13907 = (containClause5 4 22) := by decide
  rw [he]
  exact input_contain 4 22 (by decide) v hb
mask_input "13907|1897137590064188545819787018382342682267975428761855001222473056385648716020711424|4194320"
def inputClause13908 : CNF.NClause := [(4,true),(23,true),(271,false)]
theorem inputList13908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13908 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13908 = (containClause5 4 23) := by decide
  rw [he]
  exact input_contain 4 23 (by decide) v hb
mask_input "13908|3794275180128377091639574036764685364535950857523710002444946112771297432041422848|8388624"
def inputClause13909 : CNF.NClause := [(4,true),(24,true),(272,false)]
theorem inputList13909 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13909 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13909 = (containClause5 4 24) := by decide
  rw [he]
  exact input_contain 4 24 (by decide) v hb
mask_input "13909|7588550360256754183279148073529370729071901715047420004889892225542594864082845696|16777232"
def inputClause13911 : CNF.NClause := [(4,true),(26,true),(274,false)]
theorem inputList13911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13911 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13911 = (containClause5 4 26) := by decide
  rw [he]
  exact input_contain 4 26 (by decide) v hb
mask_input "13911|30354201441027016733116592294117482916287606860189680019559568902170379456331382784|67108880"
def inputClause13912 : CNF.NClause := [(4,true),(27,true),(275,false)]
theorem inputList13912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13912 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13912 = (containClause5 4 27) := by decide
  rw [he]
  exact input_contain 4 27 (by decide) v hb
mask_input "13912|60708402882054033466233184588234965832575213720379360039119137804340758912662765568|134217744"
def inputClause13913 : CNF.NClause := [(4,true),(28,true),(276,false)]
theorem inputList13913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13913 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13913 = (containClause5 4 28) := by decide
  rw [he]
  exact input_contain 4 28 (by decide) v hb
mask_input "13913|121416805764108066932466369176469931665150427440758720078238275608681517825325531136|268435472"
def inputClause13914 : CNF.NClause := [(4,true),(29,true),(277,false)]
theorem inputList13914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13914 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13914 = (containClause5 4 29) := by decide
  rw [he]
  exact input_contain 4 29 (by decide) v hb
mask_input "13914|242833611528216133864932738352939863330300854881517440156476551217363035650651062272|536870928"
def inputClause13919 : CNF.NClause := [(5,true),(3,true),(282,false)]
theorem inputList13919 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13919 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13919
  have he : decodeClause inputClause13919 = containClause5 5 3 := by decide
  rw [he]
  exact input_contain 5 3 (by decide) v hb
mask_input "13919|7770675568902916283677847627294075626569627356208558085007249638955617140820833992704|40"
def inputClause13920 : CNF.NClause := [(5,true),(4,true),(283,false)]
theorem inputList13920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13920 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13920 = (containClause5 5 4) := by decide
  rw [he]
  exact input_contain 5 4 (by decide) v hb
mask_input "13920|15541351137805832567355695254588151253139254712417116170014499277911234281641667985408|48"
def inputClause13930 : CNF.NClause := [(5,true),(15,true),(294,false)]
theorem inputList13930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13930 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13930
  have he : decodeClause inputClause13930 = containClause5 5 15 := by decide
  rw [he]
  exact input_contain 5 15 (by decide) v hb
mask_input "13930|31828687130226345097944463881396533766429193651030253916189694521162207808802136034115584|32800"
def inputClause13932 : CNF.NClause := [(5,true),(17,true),(296,false)]
theorem inputList13932 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13932 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13932 = (containClause5 5 17) := by decide
  rw [he]
  exact input_contain 5 17 (by decide) v hb
mask_input "13932|127314748520905380391777855525586135065716774604121015664758778084648831235208544136462336|131104"
def inputClause13935 : CNF.NClause := [(5,true),(20,true),(299,false)]
theorem inputList13935 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13935 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13935 = (containClause5 5 20) := by decide
  rw [he]
  exact input_contain 5 20 (by decide) v hb
mask_input "13935|1018517988167243043134222844204689080525734196832968125318070224677190649881668353091698688|1048608"
def inputClause13938 : CNF.NClause := [(5,true),(23,true),(302,false)]
theorem inputList13938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13938 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13938
  have he : decodeClause inputClause13938 = containClause5 5 23 := by decide
  rw [he]
  exact input_contain 5 23 (by decide) v hb
mask_input "13938|8148143905337944345073782753637512644205873574663745002544561797417525199053346824733589504|8388640"
end Percolation.MaskChain
