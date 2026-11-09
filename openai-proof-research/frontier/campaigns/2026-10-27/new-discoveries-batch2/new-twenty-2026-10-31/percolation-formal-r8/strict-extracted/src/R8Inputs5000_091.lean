import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause14417 : CNF.NClause := [(21,true),(22,true),(797,false)]
theorem inputList14417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14417 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14417
  have he : decodeClause inputClause14417 = containClause5 21 22 := by decide
  rw [he]
  exact input_contain 21 22 (by decide) v hb
mask_input "14417|833501804109981784259981473840157224643094790289488520049532226470504654727204008940179025108944286342866238824179155055736100206764920635045419506541353755761894697439251819807884785738976753091120627016985825247711343504684557661395484672|6291456"
def inputClause14418 : CNF.NClause := [(21,true),(23,true),(798,false)]
theorem inputList14418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14418 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14418 = (containClause5 21 23) := by decide
  rw [he]
  exact input_contain 21 23 (by decide) v hb
mask_input "14418|1667003608219963568519962947680314449286189580578977040099064452941009309454408017880358050217888572685732477648358310111472200413529841270090839013082707511523789394878503639615769571477953506182241254033971650495422687009369115322790969344|10485760"
def inputClause14419 : CNF.NClause := [(21,true),(24,true),(799,false)]
theorem inputList14419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14419 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14419
  have he : decodeClause inputClause14419 = containClause5 21 24 := by decide
  rw [he]
  exact input_contain 21 24 (by decide) v hb
mask_input "14419|3334007216439927137039925895360628898572379161157954080198128905882018618908816035760716100435777145371464955296716620222944400827059682540181678026165415023047578789757007279231539142955907012364482508067943300990845374018738230645581938688|18874368"
def inputClause14421 : CNF.NClause := [(21,true),(26,true),(801,false)]
theorem inputList14421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14421 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14421 = (containClause5 21 26) := by decide
  rw [he]
  exact input_contain 21 26 (by decide) v hb
mask_input "14421|13336028865759708548159703581442515594289516644631816320792515623528074475635264143042864401743108581485859821186866480891777603308238730160726712104661660092190315159028029116926156571823628049457930032271773203963381496074952922582327754752|69206016"
def inputClause14422 : CNF.NClause := [(21,true),(27,true),(802,false)]
theorem inputList14422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14422 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14422
  have he : decodeClause inputClause14422 = containClause5 21 27 := by decide
  rw [he]
  exact input_contain 21 27 (by decide) v hb
mask_input "14422|26672057731519417096319407162885031188579033289263632641585031247056148951270528286085728803486217162971719642373732961783555206616477460321453424209323320184380630318056058233852313143647256098915860064543546407926762992149905845164655509504|136314880"
def inputClause14423 : CNF.NClause := [(21,true),(28,true),(803,false)]
theorem inputList14423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14423 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14423
  have he : decodeClause inputClause14423 = containClause5 21 28 := by decide
  rw [he]
  exact input_contain 21 28 (by decide) v hb
mask_input "14423|53344115463038834192638814325770062377158066578527265283170062494112297902541056572171457606972434325943439284747465923567110413232954920642906848418646640368761260636112116467704626287294512197831720129087092815853525984299811690329311019008|270532608"
def inputClause14424 : CNF.NClause := [(21,true),(29,true),(804,false)]
theorem inputList14424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14424 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14424 = (containClause5 21 29) := by decide
  rw [he]
  exact input_contain 21 29 (by decide) v hb
mask_input "14424|106688230926077668385277628651540124754316133157054530566340124988224595805082113144342915213944868651886878569494931847134220826465909841285813696837293280737522521272224232935409252574589024395663440258174185631707051968599623380658622038016|538968064"
def inputClause14429 : CNF.NClause := [(22,true),(3,true),(809,false)]
theorem inputList14429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14429 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14429 = (containClause5 22 3) := by decide
  rw [he]
  exact input_contain 22 3 (by decide) v hb
mask_input "14429|3414023389634485388328884116849283992138116261025744978122883999623187065762627620618973286846235796860380114223837819108295066446909114921146038298793384983600720680711175453933096082386848780661230088261573940214625662995187948181075905216512|4194312"
def inputClause14432 : CNF.NClause := [(22,true),(6,true),(812,false)]
theorem inputList14432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14432 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14432
  have he : decodeClause inputClause14432 = containClause5 22 6 := by decide
  rw [he]
  exact input_contain 22 6 (by decide) v hb
mask_input "14432|27312187117075883106631072934794271937104930088205959824983071996985496526101020964951786294769886374883040913790702552866360531575272919369168306390347079868805765445689403631464768659094790245289840706092591521717005303961503585448607241732096|4194368"
def inputClause14433 : CNF.NClause := [(22,true),(7,true),(813,false)]
theorem inputList14433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14433 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14433 = (containClause5 22 7) := by decide
  rw [he]
  exact input_contain 22 7 (by decide) v hb
mask_input "14433|54624374234151766213262145869588543874209860176411919649966143993970993052202041929903572589539772749766081827581405105732721063150545838738336612780694159737611530891378807262929537318189580490579681412185183043434010607923007170897214483464192|4194432"
def inputClause14435 : CNF.NClause := [(22,true),(9,true),(815,false)]
theorem inputList14435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14435 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14435 = (containClause5 22 9) := by decide
  rw [he]
  exact input_contain 22 9 (by decide) v hb
mask_input "14435|218497496936607064853048583478354175496839440705647678599864575975883972208808167719614290358159090999064327310325620422930884252602183354953346451122776638950446123565515229051718149272758321962318725648740732173736042431692028683588857933856768|4194816"
def inputClause14438 : CNF.NClause := [(22,true),(12,true),(818,false)]
theorem inputList14438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14438 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14438 = (containClause5 22 12) := by decide
  rw [he]
  exact input_contain 22 12 (by decide) v hb
mask_input "14438|1747979975492856518824388667826833403974715525645181428798916607807071777670465341756914322865272727992514618482604963383447074020817466839626771608982213111603568988524121832413745194182066575698549805189925857389888339453536229468710863470854144|4198400"
def inputClause14439 : CNF.NClause := [(22,true),(13,true),(819,false)]
theorem inputList14439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14439 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14439 = (containClause5 22 13) := by decide
  rw [he]
  exact input_contain 22 13 (by decide) v hb
mask_input "14439|3495959950985713037648777335653666807949431051290362857597833215614143555340930683513828645730545455985029236965209926766894148041634933679253543217964426223207137977048243664827490388364133151397099610379851714779776678907072458937421726941708288|4202496"
def inputClause14441 : CNF.NClause := [(22,true),(15,true),(821,false)]
theorem inputList14441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14441 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14441 = (containClause5 22 15) := by decide
  rw [he]
  exact input_contain 22 15 (by decide) v hb
mask_input "14441|13983839803942852150595109342614667231797724205161451430391332862456574221363722734055314582922181823940116947860839707067576592166539734717014172871857704892828551908192974659309961553456532605588398441519406859119106715628289835749686907766833152|4227072"
def inputClause14442 : CNF.NClause := [(22,true),(16,true),(822,false)]
theorem inputList14442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14442 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14442 = (containClause5 22 16) := by decide
  rw [he]
  exact input_contain 22 16 (by decide) v hb
mask_input "14442|27967679607885704301190218685229334463595448410322902860782665724913148442727445468110629165844363647880233895721679414135153184333079469434028345743715409785657103816385949318619923106913065211176796883038813718238213431256579671499373815533666304|4259840"
def inputClause14443 : CNF.NClause := [(22,true),(17,true),(823,false)]
theorem inputList14443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14443 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14443 = (containClause5 22 17) := by decide
  rw [he]
  exact input_contain 22 17 (by decide) v hb
mask_input "14443|55935359215771408602380437370458668927190896820645805721565331449826296885454890936221258331688727295760467791443358828270306368666158938868056691487430819571314207632771898637239846213826130422353593766077627436476426862513159342998747631067332608|4325376"
def inputClause14444 : CNF.NClause := [(22,true),(18,true),(824,false)]
theorem inputList14444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14444 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14444 = (containClause5 22 18) := by decide
  rw [he]
  exact input_contain 22 18 (by decide) v hb
mask_input "14444|111870718431542817204760874740917337854381793641291611443130662899652593770909781872442516663377454591520935582886717656540612737332317877736113382974861639142628415265543797274479692427652260844707187532155254872952853725026318685997495262134665216|4456448"
def inputClause14445 : CNF.NClause := [(22,true),(19,true),(825,false)]
theorem inputList14445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14445 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14445
  have he : decodeClause inputClause14445 = containClause5 22 19 := by decide
  rw [he]
  exact input_contain 22 19 (by decide) v hb
mask_input "14445|223741436863085634409521749481834675708763587282583222886261325799305187541819563744885033326754909183041871165773435313081225474664635755472226765949723278285256830531087594548959384855304521689414375064310509745905707450052637371994990524269330432|4718592"
def inputClause14446 : CNF.NClause := [(22,true),(20,true),(826,false)]
theorem inputList14446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14446 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14446
  have he : decodeClause inputClause14446 = containClause5 22 20 := by decide
  rw [he]
  exact input_contain 22 20 (by decide) v hb
mask_input "14446|447482873726171268819043498963669351417527174565166445772522651598610375083639127489770066653509818366083742331546870626162450949329271510944453531899446556570513661062175189097918769710609043378828750128621019491811414900105274743989981048538660864|5242880"
def inputClause14447 : CNF.NClause := [(22,true),(21,true),(827,false)]
theorem inputList14447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14447 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14447
  have he : decodeClause inputClause14447 = containClause5 22 21 := by decide
  rw [he]
  exact input_contain 22 21 (by decide) v hb
mask_input "14447|894965747452342537638086997927338702835054349130332891545045303197220750167278254979540133307019636732167484663093741252324901898658543021888907063798893113141027322124350378195837539421218086757657500257242038983622829800210549487979962097077321728|6291456"
def inputClause14448 : CNF.NClause := [(22,true),(23,true),(829,false)]
theorem inputList14448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14448 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14448 = (containClause5 22 23) := by decide
  rw [he]
  exact input_contain 22 23 (by decide) v hb
mask_input "14448|3579862989809370150552347991709354811340217396521331566180181212788883000669113019918160533228078546928669938652374965009299607594634172087555628255195572452564109288497401512783350157684872347030630001028968155934491319200842197951919848388309286912|12582912"
def inputClause14449 : CNF.NClause := [(22,true),(24,true),(830,false)]
theorem inputList14449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14449 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14449
  have he : decodeClause inputClause14449 = containClause5 22 24 := by decide
  rw [he]
  exact input_contain 22 24 (by decide) v hb
mask_input "14449|7159725979618740301104695983418709622680434793042663132360362425577766001338226039836321066456157093857339877304749930018599215189268344175111256510391144905128218576994803025566700315369744694061260002057936311868982638401684395903839696776618573824|20971520"
def inputClause14451 : CNF.NClause := [(22,true),(26,true),(832,false)]
theorem inputList14451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14451 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14451 = (containClause5 22 26) := by decide
  rw [he]
  exact input_contain 22 26 (by decide) v hb
mask_input "14451|28638903918474961204418783933674838490721739172170652529441449702311064005352904159345284265824628375429359509218999720074396860757073376700445026041564579620512874307979212102266801261478978776245040008231745247475930553606737583615358787106474295296|71303168"
def inputClause14452 : CNF.NClause := [(22,true),(27,true),(833,false)]
theorem inputList14452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14452 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14452 = (containClause5 22 27) := by decide
  rw [he]
  exact input_contain 22 27 (by decide) v hb
mask_input "14452|57277807836949922408837567867349676981443478344341305058882899404622128010705808318690568531649256750858719018437999440148793721514146753400890052083129159241025748615958424204533602522957957552490080016463490494951861107213475167230717574212948590592|138412032"
def inputClause14453 : CNF.NClause := [(22,true),(28,true),(834,false)]
theorem inputList14453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14453 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14453 = (containClause5 22 28) := by decide
  rw [he]
  exact input_contain 22 28 (by decide) v hb
mask_input "14453|114555615673899844817675135734699353962886956688682610117765798809244256021411616637381137063298513501717438036875998880297587443028293506801780104166258318482051497231916848409067205045915915104980160032926980989903722214426950334461435148425897181184|272629760"
def inputClause14454 : CNF.NClause := [(22,true),(29,true),(835,false)]
theorem inputList14454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14454 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause14454
  have he : decodeClause inputClause14454 = containClause5 22 29 := by decide
  rw [he]
  exact input_contain 22 29 (by decide) v hb
mask_input "14454|229111231347799689635350271469398707925773913377365220235531597618488512042823233274762274126597027003434876073751997760595174886056587013603560208332516636964102994463833696818134410091831830209960320065853961979807444428853900668922870296851794362368|541065216"
def inputClause14459 : CNF.NClause := [(23,true),(3,true),(840,false)]
theorem inputList14459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14459 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14459 = (containClause5 23 3) := by decide
  rw [he]
  exact input_contain 23 3 (by decide) v hb
mask_input "14459|7331559403129590068331208687020758653624765228075687047537011123791632385370343464792392772051104864109916034360063928339045596353810784435313926666640532382851295822842678298180301122938618566718730242107326783353838221723324821405531849499257419595776|8388616"
def inputClause14462 : CNF.NClause := [(23,true),(6,true),(843,false)]
theorem inputList14462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14462 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14462 = (containClause5 23 6) := by decide
  rw [he]
  exact input_contain 23 6 (by decide) v hb
mask_input "14462|58652475225036720546649669496166069228998121824605496380296088990333059082962747718339142176408838912879328274880511426712364770830486275482511413333124259062810366582741426385442408983508948533749841936858614266830705773786598571244254795994059356766208|8388672"
def inputClause14463 : CNF.NClause := [(23,true),(7,true),(844,false)]
theorem inputList14463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14463 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14463 = (containClause5 23 7) := by decide
  rw [he]
  exact input_contain 23 7 (by decide) v hb
mask_input "14463|117304950450073441093299338992332138457996243649210992760592177980666118165925495436678284352817677825758656549761022853424729541660972550965022826666248518125620733165482852770884817967017897067499683873717228533661411547573197142488509591988118713532416|8388736"
def inputClause14465 : CNF.NClause := [(23,true),(9,true),(846,false)]
theorem inputList14465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14465 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14465 = (containClause5 23 9) := by decide
  rw [he]
  exact input_contain 23 9 (by decide) v hb
mask_input "14465|469219801800293764373197355969328553831984974596843971042368711922664472663701981746713137411270711303034626199044091413698918166643890203860091306664994072502482932661931411083539271868071588269998735494868914134645646190292788569954038367952474854129664|8389120"
def inputClause14468 : CNF.NClause := [(23,true),(12,true),(849,false)]
theorem inputList14468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14468 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14468 = (containClause5 23 12) := by decide
  rw [he]
  exact input_contain 23 12 (by decide) v hb
mask_input "14468|3753758414402350114985578847754628430655879796774751768338949695381315781309615853973705099290165690424277009592352731309591345333151121630880730453319952580019863461295451288668314174944572706159989883958951313077165169522342308559632306943619798833037312|8392704"
def inputClause14469 : CNF.NClause := [(23,true),(13,true),(850,false)]
theorem inputList14469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14469 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14469 = (containClause5 23 13) := by decide
  rw [he]
  exact input_contain 23 13 (by decide) v hb
mask_input "14469|7507516828804700229971157695509256861311759593549503536677899390762631562619231707947410198580331380848554019184705462619182690666302243261761460906639905160039726922590902577336628349889145412319979767917902626154330339044684617119264613887239597666074624|8396800"
def inputClause14471 : CNF.NClause := [(23,true),(15,true),(852,false)]
theorem inputList14471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14471 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14471 = (containClause5 23 15) := by decide
  rw [he]
  exact input_contain 23 15 (by decide) v hb
mask_input "14471|30030067315218800919884630782037027445247038374198014146711597563050526250476926831789640794321325523394216076738821850476730762665208973047045843626559620640158907690363610309346513399556581649279919071671610504617321356178738468477058455548958390664298496|8421376"
def inputClause14472 : CNF.NClause := [(23,true),(16,true),(853,false)]
theorem inputList14472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14472 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14472 = (containClause5 23 16) := by decide
  rw [he]
  exact input_contain 23 16 (by decide) v hb
mask_input "14472|60060134630437601839769261564074054890494076748396028293423195126101052500953853663579281588642651046788432153477643700953461525330417946094091687253119241280317815380727220618693026799113163298559838143343221009234642712357476936954116911097916781328596992|8454144"
def inputClause14473 : CNF.NClause := [(23,true),(17,true),(854,false)]
theorem inputList14473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14473 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14473 = (containClause5 23 17) := by decide
  rw [he]
  exact input_contain 23 17 (by decide) v hb
mask_input "14473|120120269260875203679538523128148109780988153496792056586846390252202105001907707327158563177285302093576864306955287401906923050660835892188183374506238482560635630761454441237386053598226326597119676286686442018469285424714953873908233822195833562657193984|8519680"
def inputClause14474 : CNF.NClause := [(23,true),(18,true),(855,false)]
theorem inputList14474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14474 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14474 = (containClause5 23 18) := by decide
  rw [he]
  exact input_contain 23 18 (by decide) v hb
mask_input "14474|240240538521750407359077046256296219561976306993584113173692780504404210003815414654317126354570604187153728613910574803813846101321671784376366749012476965121271261522908882474772107196452653194239352573372884036938570849429907747816467644391667125314387968|8650752"
def inputClause14475 : CNF.NClause := [(23,true),(19,true),(856,false)]
theorem inputList14475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14475 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14475 = (containClause5 23 19) := by decide
  rw [he]
  exact input_contain 23 19 (by decide) v hb
mask_input "14475|480481077043500814718154092512592439123952613987168226347385561008808420007630829308634252709141208374307457227821149607627692202643343568752733498024953930242542523045817764949544214392905306388478705146745768073877141698859815495632935288783334250628775936|8912896"
def inputClause14476 : CNF.NClause := [(23,true),(20,true),(857,false)]
theorem inputList14476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14476 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14476 = (containClause5 23 20) := by decide
  rw [he]
  exact input_contain 23 20 (by decide) v hb
mask_input "14476|960962154087001629436308185025184878247905227974336452694771122017616840015261658617268505418282416748614914455642299215255384405286687137505466996049907860485085046091635529899088428785810612776957410293491536147754283397719630991265870577566668501257551872|9437184"
def inputClause14477 : CNF.NClause := [(23,true),(21,true),(858,false)]
theorem inputList14477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14477 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14477 = (containClause5 23 21) := by decide
  rw [he]
  exact input_contain 23 21 (by decide) v hb
mask_input "14477|1921924308174003258872616370050369756495810455948672905389542244035233680030523317234537010836564833497229828911284598430510768810573374275010933992099815720970170092183271059798176857571621225553914820586983072295508566795439261982531741155133337002515103744|10485760"
def inputClause14478 : CNF.NClause := [(23,true),(22,true),(859,false)]
theorem inputList14478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause14478 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause14478 = (containClause5 23 22) := by decide
  rw [he]
  exact input_contain 23 22 (by decide) v hb
mask_input "14478|3843848616348006517745232740100739512991620911897345810779084488070467360061046634469074021673129666994459657822569196861021537621146748550021867984199631441940340184366542119596353715143242451107829641173966144591017133590878523965063482310266674005030207488|12582912"
end Percolation.MaskChain
