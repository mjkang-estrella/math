import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause1972 : CNF.NClause := [(92,true),(0,true),(5,true),(10,false),(15,false),(20,true),(25,true)]
theorem inputList1972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1972 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) inputClause1972 (by decide) v hb
mask_input "1972|33792|4951760157141521099631099937"
def inputClause1974 : CNF.NClause := [(92,true),(0,true),(5,false),(10,true),(15,false),(20,true),(25,true)]
theorem inputList1974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1974 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) inputClause1974 (by decide) v hb
mask_input "1974|32800|4951760157141521099631100929"
def inputClause1976 : CNF.NClause := [(92,false),(0,true),(5,true),(10,true),(15,false),(20,true),(25,true)]
theorem inputList1976 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1976 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) inputClause1976 (by decide) v hb
mask_input "1976|4951760157141521099596529664|34604065"
def inputClause1978 : CNF.NClause := [(92,true),(0,true),(5,false),(10,false),(15,true),(20,true),(25,true)]
theorem inputList1978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1978 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) inputClause1978 (by decide) v hb
mask_input "1978|1056|4951760157141521099631132673"
def inputClause1980 : CNF.NClause := [(92,false),(0,true),(5,true),(10,false),(15,true),(20,true),(25,true)]
theorem inputList1980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1980 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) inputClause1980 (by decide) v hb
mask_input "1980|4951760157141521099596497920|34635809"
def inputClause1982 : CNF.NClause := [(92,false),(0,true),(5,false),(10,true),(15,true),(20,true),(25,true)]
theorem inputList1982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1982 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) inputClause1982 (by decide) v hb
mask_input "1982|4951760157141521099596496928|34636801"
def inputClause1985 : CNF.NClause := [(93,true),(56,false),(57,false),(58,false),(59,false),(60,false),(61,false)]
theorem inputList1985 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1985 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause1985 (by decide) v hb
mask_input "1985|4539628424389459968|9903520314283042199192993792"
def inputClause1986 : CNF.NClause := [(93,true),(56,true),(57,false),(58,false),(59,false),(60,false),(61,false)]
theorem inputList1986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1986 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause1986 (by decide) v hb
mask_input "1986|4467570830351532032|9903520314355099793230921728"
def inputClause1987 : CNF.NClause := [(93,true),(56,false),(57,true),(58,false),(59,false),(60,false),(61,false)]
theorem inputList1987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1987 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause1987 (by decide) v hb
mask_input "1987|4395513236313604096|9903520314427157387268849664"
def inputClause1988 : CNF.NClause := [(93,true),(56,true),(57,true),(58,false),(59,false),(60,false),(61,false)]
theorem inputList1988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1988 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause1988 (by decide) v hb
mask_input "1988|4323455642275676160|9903520314499214981306777600"
def inputClause1989 : CNF.NClause := [(93,true),(56,false),(57,false),(58,true),(59,false),(60,false),(61,false)]
theorem inputList1989 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1989 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause1989 (by decide) v hb
mask_input "1989|4251398048237748224|9903520314571272575344705536"
def inputClause1990 : CNF.NClause := [(93,true),(56,true),(57,false),(58,true),(59,false),(60,false),(61,false)]
theorem inputList1990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1990 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause1990 (by decide) v hb
mask_input "1990|4179340454199820288|9903520314643330169382633472"
def inputClause1991 : CNF.NClause := [(93,true),(56,false),(57,true),(58,true),(59,false),(60,false),(61,false)]
theorem inputList1991 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1991 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause1991 (by decide) v hb
mask_input "1991|4107282860161892352|9903520314715387763420561408"
def inputClause1992 : CNF.NClause := [(93,true),(56,true),(57,true),(58,true),(59,false),(60,false),(61,false)]
theorem inputList1992 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1992 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause1992 (by decide) v hb
mask_input "1992|4035225266123964416|9903520314787445357458489344"
def inputClause1993 : CNF.NClause := [(93,true),(56,false),(57,false),(58,false),(59,true),(60,false),(61,false)]
theorem inputList1993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1993 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause1993 (by decide) v hb
mask_input "1993|3963167672086036480|9903520314859502951496417280"
def inputClause1994 : CNF.NClause := [(93,true),(56,true),(57,false),(58,false),(59,true),(60,false),(61,false)]
theorem inputList1994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1994 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause1994 (by decide) v hb
mask_input "1994|3891110078048108544|9903520314931560545534345216"
def inputClause1995 : CNF.NClause := [(93,true),(56,false),(57,true),(58,false),(59,true),(60,false),(61,false)]
theorem inputList1995 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1995 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause1995 (by decide) v hb
mask_input "1995|3819052484010180608|9903520315003618139572273152"
def inputClause1996 : CNF.NClause := [(93,true),(56,true),(57,true),(58,false),(59,true),(60,false),(61,false)]
theorem inputList1996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1996 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause1996 (by decide) v hb
mask_input "1996|3746994889972252672|9903520315075675733610201088"
def inputClause1997 : CNF.NClause := [(93,true),(56,false),(57,false),(58,true),(59,true),(60,false),(61,false)]
theorem inputList1997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1997 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause1997 (by decide) v hb
mask_input "1997|3674937295934324736|9903520315147733327648129024"
def inputClause1998 : CNF.NClause := [(93,true),(56,true),(57,false),(58,true),(59,true),(60,false),(61,false)]
theorem inputList1998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1998 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause1998 (by decide) v hb
mask_input "1998|3602879701896396800|9903520315219790921686056960"
def inputClause1999 : CNF.NClause := [(93,true),(56,false),(57,true),(58,true),(59,true),(60,false),(61,false)]
theorem inputList1999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1999 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause1999 (by decide) v hb
mask_input "1999|3530822107858468864|9903520315291848515723984896"
def inputClause2000 : CNF.NClause := [(93,true),(56,true),(57,true),(58,true),(59,true),(60,false),(61,false)]
theorem inputList2000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2000 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2000 (by decide) v hb
mask_input "2000|3458764513820540928|9903520315363906109761912832"
def inputClause2001 : CNF.NClause := [(93,true),(56,false),(57,false),(58,false),(59,false),(60,true),(61,false)]
theorem inputList2001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2001 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2001 (by decide) v hb
mask_input "2001|3386706919782612992|9903520315435963703799840768"
def inputClause2002 : CNF.NClause := [(93,true),(56,true),(57,false),(58,false),(59,false),(60,true),(61,false)]
theorem inputList2002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2002 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2002 (by decide) v hb
mask_input "2002|3314649325744685056|9903520315508021297837768704"
def inputClause2004 : CNF.NClause := [(93,true),(56,true),(57,true),(58,false),(59,false),(60,true),(61,false)]
theorem inputList2004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2004 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2004 (by decide) v hb
mask_input "2004|3170534137668829184|9903520315652136485913624576"
def inputClause2005 : CNF.NClause := [(93,true),(56,false),(57,false),(58,true),(59,false),(60,true),(61,false)]
theorem inputList2005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2005 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2005 (by decide) v hb
mask_input "2005|3098476543630901248|9903520315724194079951552512"
def inputClause2006 : CNF.NClause := [(93,true),(56,true),(57,false),(58,true),(59,false),(60,true),(61,false)]
theorem inputList2006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2006 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2006 (by decide) v hb
mask_input "2006|3026418949592973312|9903520315796251673989480448"
def inputClause2009 : CNF.NClause := [(93,true),(56,false),(57,false),(58,false),(59,true),(60,true),(61,false)]
theorem inputList2009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2009 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2009 (by decide) v hb
mask_input "2009|2810246167479189504|9903520316012424456103264256"
def inputClause2010 : CNF.NClause := [(93,true),(56,true),(57,false),(58,false),(59,true),(60,true),(61,false)]
theorem inputList2010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2010 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2010 (by decide) v hb
mask_input "2010|2738188573441261568|9903520316084482050141192192"
def inputClause2013 : CNF.NClause := [(93,true),(56,false),(57,false),(58,true),(59,true),(60,true),(61,false)]
theorem inputList2013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2013 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2013 (by decide) v hb
mask_input "2013|2522015791327477760|9903520316300654832254976000"
def inputClause2014 : CNF.NClause := [(93,true),(56,true),(57,false),(58,true),(59,true),(60,true),(61,false)]
theorem inputList2014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2014 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2014 (by decide) v hb
mask_input "2014|2449958197289549824|9903520316372712426292903936"
def inputClause2016 : CNF.NClause := [(93,false),(56,true),(57,true),(58,true),(59,true),(60,true),(61,false)]
theorem inputList2016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2016 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2016 (by decide) v hb
mask_input "2016|9903520316588885208406687744|2233785415175766016"
def inputClause2017 : CNF.NClause := [(93,true),(56,false),(57,false),(58,false),(59,false),(60,false),(61,true)]
theorem inputList2017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2017 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2017 (by decide) v hb
mask_input "2017|2233785415175766016|9903520316588885208406687744"
def inputClause2018 : CNF.NClause := [(93,true),(56,true),(57,false),(58,false),(59,false),(60,false),(61,true)]
theorem inputList2018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2018 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2018 (by decide) v hb
mask_input "2018|2161727821137838080|9903520316660942802444615680"
def inputClause2019 : CNF.NClause := [(93,true),(56,false),(57,true),(58,false),(59,false),(60,false),(61,true)]
theorem inputList2019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2019 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2019 (by decide) v hb
mask_input "2019|2089670227099910144|9903520316733000396482543616"
def inputClause2020 : CNF.NClause := [(93,true),(56,true),(57,true),(58,false),(59,false),(60,false),(61,true)]
theorem inputList2020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2020 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2020 (by decide) v hb
mask_input "2020|2017612633061982208|9903520316805057990520471552"
def inputClause2021 : CNF.NClause := [(93,true),(56,false),(57,false),(58,true),(59,false),(60,false),(61,true)]
theorem inputList2021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2021 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2021 (by decide) v hb
mask_input "2021|1945555039024054272|9903520316877115584558399488"
def inputClause2022 : CNF.NClause := [(93,true),(56,true),(57,false),(58,true),(59,false),(60,false),(61,true)]
theorem inputList2022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2022 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2022 (by decide) v hb
mask_input "2022|1873497444986126336|9903520316949173178596327424"
def inputClause2023 : CNF.NClause := [(93,true),(56,false),(57,true),(58,true),(59,false),(60,false),(61,true)]
theorem inputList2023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2023 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2023 (by decide) v hb
mask_input "2023|1801439850948198400|9903520317021230772634255360"
def inputClause2024 : CNF.NClause := [(93,true),(56,true),(57,true),(58,true),(59,false),(60,false),(61,true)]
theorem inputList2024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2024 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 0) 0) (activationX_mem 0) inputClause2024 (by decide) v hb
mask_input "2024|1729382256910270464|9903520317093288366672183296"
end Percolation.MaskChain
