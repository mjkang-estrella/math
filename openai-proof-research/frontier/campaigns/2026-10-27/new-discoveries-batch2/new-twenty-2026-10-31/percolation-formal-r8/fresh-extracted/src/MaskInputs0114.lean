import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause13775 : CNF.NClause := [(0,true),(10,true),(134,false)]
theorem inputList13775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13775 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13775 = (containClause5 0 10) := by decide
  rw [he]
  exact input_contain 0 10 (by decide) v hb
mask_input "13775|21778071482940061661655974875633165533184|1025"
def inputClause13776 : CNF.NClause := [(0,true),(11,true),(135,false)]
theorem inputList13776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13776 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13776 = (containClause5 0 11) := by decide
  rw [he]
  exact input_contain 0 11 (by decide) v hb
mask_input "13776|43556142965880123323311949751266331066368|2049"
def inputClause13777 : CNF.NClause := [(0,true),(12,true),(136,false)]
theorem inputList13777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13777 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13777 = (containClause5 0 12) := by decide
  rw [he]
  exact input_contain 0 12 (by decide) v hb
mask_input "13777|87112285931760246646623899502532662132736|4097"
def inputClause13778 : CNF.NClause := [(0,true),(13,true),(137,false)]
theorem inputList13778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13778 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13778 = (containClause5 0 13) := by decide
  rw [he]
  exact input_contain 0 13 (by decide) v hb
mask_input "13778|174224571863520493293247799005065324265472|8193"
def inputClause13779 : CNF.NClause := [(0,true),(14,true),(138,false)]
theorem inputList13779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13779 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13779 = (containClause5 0 14) := by decide
  rw [he]
  exact input_contain 0 14 (by decide) v hb
mask_input "13779|348449143727040986586495598010130648530944|16385"
def inputClause13780 : CNF.NClause := [(0,true),(15,true),(139,false)]
theorem inputList13780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13780 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13780 = (containClause5 0 15) := by decide
  rw [he]
  exact input_contain 0 15 (by decide) v hb
mask_input "13780|696898287454081973172991196020261297061888|32769"
def inputClause13781 : CNF.NClause := [(0,true),(16,true),(140,false)]
theorem inputList13781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13781 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13781 = (containClause5 0 16) := by decide
  rw [he]
  exact input_contain 0 16 (by decide) v hb
mask_input "13781|1393796574908163946345982392040522594123776|65537"
def inputClause13782 : CNF.NClause := [(0,true),(17,true),(141,false)]
theorem inputList13782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13782 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13782 = (containClause5 0 17) := by decide
  rw [he]
  exact input_contain 0 17 (by decide) v hb
mask_input "13782|2787593149816327892691964784081045188247552|131073"
def inputClause13783 : CNF.NClause := [(0,true),(18,true),(142,false)]
theorem inputList13783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13783 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13783 = (containClause5 0 18) := by decide
  rw [he]
  exact input_contain 0 18 (by decide) v hb
mask_input "13783|5575186299632655785383929568162090376495104|262145"
def inputClause13784 : CNF.NClause := [(0,true),(19,true),(143,false)]
theorem inputList13784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13784 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13784 = (containClause5 0 19) := by decide
  rw [he]
  exact input_contain 0 19 (by decide) v hb
mask_input "13784|11150372599265311570767859136324180752990208|524289"
def inputClause13785 : CNF.NClause := [(0,true),(20,true),(144,false)]
theorem inputList13785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13785 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13785 = (containClause5 0 20) := by decide
  rw [he]
  exact input_contain 0 20 (by decide) v hb
mask_input "13785|22300745198530623141535718272648361505980416|1048577"
def inputClause13786 : CNF.NClause := [(0,true),(21,true),(145,false)]
theorem inputList13786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13786 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13786 = (containClause5 0 21) := by decide
  rw [he]
  exact input_contain 0 21 (by decide) v hb
mask_input "13786|44601490397061246283071436545296723011960832|2097153"
def inputClause13787 : CNF.NClause := [(0,true),(22,true),(146,false)]
theorem inputList13787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13787 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13787 = (containClause5 0 22) := by decide
  rw [he]
  exact input_contain 0 22 (by decide) v hb
mask_input "13787|89202980794122492566142873090593446023921664|4194305"
def inputClause13788 : CNF.NClause := [(0,true),(23,true),(147,false)]
theorem inputList13788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13788 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13788 = (containClause5 0 23) := by decide
  rw [he]
  exact input_contain 0 23 (by decide) v hb
mask_input "13788|178405961588244985132285746181186892047843328|8388609"
def inputClause13789 : CNF.NClause := [(0,true),(24,true),(148,false)]
theorem inputList13789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13789 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13789 = (containClause5 0 24) := by decide
  rw [he]
  exact input_contain 0 24 (by decide) v hb
mask_input "13789|356811923176489970264571492362373784095686656|16777217"
def inputClause13790 : CNF.NClause := [(0,true),(25,true),(149,false)]
theorem inputList13790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13790 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13790 = (containClause5 0 25) := by decide
  rw [he]
  exact input_contain 0 25 (by decide) v hb
mask_input "13790|713623846352979940529142984724747568191373312|33554433"
def inputClause13791 : CNF.NClause := [(0,true),(26,true),(150,false)]
theorem inputList13791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13791 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13791 = (containClause5 0 26) := by decide
  rw [he]
  exact input_contain 0 26 (by decide) v hb
mask_input "13791|1427247692705959881058285969449495136382746624|67108865"
def inputClause13792 : CNF.NClause := [(0,true),(27,true),(151,false)]
theorem inputList13792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13792 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13792 = (containClause5 0 27) := by decide
  rw [he]
  exact input_contain 0 27 (by decide) v hb
mask_input "13792|2854495385411919762116571938898990272765493248|134217729"
def inputClause13793 : CNF.NClause := [(0,true),(28,true),(152,false)]
theorem inputList13793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13793 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13793 = (containClause5 0 28) := by decide
  rw [he]
  exact input_contain 0 28 (by decide) v hb
mask_input "13793|5708990770823839524233143877797980545530986496|268435457"
def inputClause13794 : CNF.NClause := [(0,true),(29,true),(153,false)]
theorem inputList13794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13794 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13794 = (containClause5 0 29) := by decide
  rw [he]
  exact input_contain 0 29 (by decide) v hb
mask_input "13794|11417981541647679048466287755595961091061972992|536870913"
def inputClause13795 : CNF.NClause := [(0,true),(30,true),(154,false)]
theorem inputList13795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13795 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13795 = (containClause5 0 30) := by decide
  rw [he]
  exact input_contain 0 30 (by decide) v hb
mask_input "13795|22835963083295358096932575511191922182123945984|1073741825"
def inputClause13796 : CNF.NClause := [(1,true),(0,true),(155,false)]
theorem inputList13796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13796 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13796 = (containClause5 1 0) := by decide
  rw [he]
  exact input_contain 1 0 (by decide) v hb
mask_input "13796|45671926166590716193865151022383844364247891968|3"
def inputClause13820 : CNF.NClause := [(1,true),(25,true),(180,false)]
theorem inputList13820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13820 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13820 = (containClause5 1 25) := by decide
  rw [he]
  exact input_contain 1 25 (by decide) v hb
mask_input "13820|1532495540865888858358347027150309183618739122183602176|33554434"
def inputClause13825 : CNF.NClause := [(1,true),(30,true),(185,false)]
theorem inputList13825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13825 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13825 = (containClause5 1 30) := by decide
  rw [he]
  exact input_contain 1 30 (by decide) v hb
mask_input "13825|49039857307708443467467104868809893875799651909875269632|1073741826"
def inputClause13826 : CNF.NClause := [(2,true),(0,true),(186,false)]
theorem inputList13826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13826 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13826
  have he : decodeClause inputClause13826 = containClause5 2 0 := by decide
  rw [he]
  exact input_contain 2 0 (by decide) v hb
mask_input "13826|98079714615416886934934209737619787751599303819750539264|5"
def inputClause13850 : CNF.NClause := [(2,true),(25,true),(211,false)]
theorem inputList13850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13850 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13850 = (containClause5 2 25) := by decide
  rw [he]
  exact input_contain 2 25 (by decide) v hb
mask_input "13850|3291009114642412084309938365114701009965471731267159726697218048|33554436"
def inputClause13855 : CNF.NClause := [(2,true),(30,true),(216,false)]
theorem inputList13855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13855 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13855 = (containClause5 2 30) := by decide
  rw [he]
  exact input_contain 2 30 (by decide) v hb
mask_input "13855|105312291668557186697918027683670432318895095400549111254310977536|1073741828"
def inputClause13856 : CNF.NClause := [(3,true),(0,true),(217,false)]
theorem inputList13856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13856 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13856
  have he : decodeClause inputClause13856 = containClause5 3 0 := by decide
  rw [he]
  exact input_contain 3 0 (by decide) v hb
mask_input "13856|210624583337114373395836055367340864637790190801098222508621955072|9"
def inputClause13880 : CNF.NClause := [(3,true),(25,true),(242,false)]
theorem inputList13880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13880 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13880 = (containClause5 3 25) := by decide
  rw [he]
  exact input_contain 3 25 (by decide) v hb
mask_input "13880|7067388259113537318333190002971674063309935587502475832486424805170479104|33554440"
def inputClause13885 : CNF.NClause := [(3,true),(30,true),(247,false)]
theorem inputList13885 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13885 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13885 = (containClause5 3 30) := by decide
  rw [he]
  exact input_contain 3 30 (by decide) v hb
mask_input "13885|226156424291633194186662080095093570025917938800079226639565593765455331328|1073741832"
def inputClause13886 : CNF.NClause := [(4,true),(0,true),(248,false)]
theorem inputList13886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13886 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13886 = (containClause5 4 0) := by decide
  rw [he]
  exact input_contain 4 0 (by decide) v hb
mask_input "13886|452312848583266388373324160190187140051835877600158453279131187530910662656|17"
def inputClause13910 : CNF.NClause := [(4,true),(25,true),(273,false)]
theorem inputList13910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13910 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13910 = (containClause5 4 25) := by decide
  rw [he]
  exact input_contain 4 25 (by decide) v hb
mask_input "13910|15177100720513508366558296147058741458143803430094840009779784451085189728165691392|33554448"
def inputClause13915 : CNF.NClause := [(4,true),(30,true),(278,false)]
theorem inputList13915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13915 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13915 = (containClause5 4 30) := by decide
  rw [he]
  exact input_contain 4 30 (by decide) v hb
mask_input "13915|485667223056432267729865476705879726660601709763034880312953102434726071301302124544|1073741840"
def inputClause13916 : CNF.NClause := [(5,true),(0,true),(279,false)]
theorem inputList13916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13916 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13916
  have he : decodeClause inputClause13916 = containClause5 5 0 := by decide
  rw [he]
  exact input_contain 5 0 (by decide) v hb
mask_input "13916|971334446112864535459730953411759453321203419526069760625906204869452142602604249088|33"
def inputClause13940 : CNF.NClause := [(5,true),(25,true),(304,false)]
theorem inputList13940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13940 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13940
  have he : decodeClause inputClause13940 = containClause5 5 25 := by decide
  rw [he]
  exact input_contain 5 25 (by decide) v hb
mask_input "13940|32592575621351777380295131014550050576823494298654980010178247189670100796213387298934358016|33554464"
def inputClause13945 : CNF.NClause := [(5,true),(30,true),(309,false)]
theorem inputList13945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13945 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13945 = (containClause5 5 30) := by decide
  rw [he]
  exact input_contain 5 30 (by decide) v hb
mask_input "13945|1042962419883256876169444192465601618458351817556959360325703910069443225478828393565899456512|1073741856"
def inputClause13946 : CNF.NClause := [(6,true),(0,true),(310,false)]
theorem inputList13946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13946 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13946 = (containClause5 6 0) := by decide
  rw [he]
  exact input_contain 6 0 (by decide) v hb
mask_input "13946|2085924839766513752338888384931203236916703635113918720651407820138886450957656787131798913024|65"
def inputClause13970 : CNF.NClause := [(6,true),(25,true),(335,false)]
theorem inputList13970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13970 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13970 = (containClause5 6 25) := by decide
  rw [he]
  exact input_contain 6 25 (by decide) v hb
mask_input "13970|69992023193056381579920071267763883691301421788582797965624659405118495974380029543152421664737722368|33554496"
def inputClause13975 : CNF.NClause := [(6,true),(30,true),(340,false)]
theorem inputList13975 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13975 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode
  have he : decodeClause inputClause13975 = (containClause5 6 30) := by decide
  rw [he]
  exact input_contain 6 30 (by decide) v hb
mask_input "13975|2239744742177804210557442280568444278121645497234649534899989100963791871180160945380877493271607115776|1073741888"
def inputClause13976 : CNF.NClause := [(7,true),(0,true),(341,false)]
theorem inputList13976 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause13976 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  apply holds_decode v inputClause13976
  have he : decodeClause inputClause13976 = containClause5 7 0 := by decide
  rw [he]
  exact input_contain 7 0 (by decide) v hb
mask_input "13976|4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986543214231552|129"
end Percolation.MaskChain
