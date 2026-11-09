import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause6196 : CNF.NClause := [(48,false),(17,true),(64,true),(70,false),(76,false),(77,true),(83,true),(88,false)]
theorem inputList6196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6196 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6196 (by decide) v hb
mask_input "6196|309561748276973175436214272|9822540731112935754170368"
def inputClause6197 : CNF.NClause := [(48,false),(17,false),(64,false),(70,true),(76,false),(77,true),(83,true),(88,false)]
theorem inputList6197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6197 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6197 (by decide) v hb
mask_input "6197|309560586132096531734593536|9823702875989579455791104"
def inputClause6198 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,false),(77,true),(83,true),(88,false)]
theorem inputList6198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6198 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6198 (by decide) v hb
mask_input "6198|309560586132096531734462464|9823702875989579455922176"
def inputClause6199 : CNF.NClause := [(48,false),(17,false),(64,true),(70,true),(76,false),(77,true),(83,true),(88,false)]
theorem inputList6199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6199 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6199 (by decide) v hb
mask_input "6199|309560567685352458025041920|9823721322733653165342720"
def inputClause6200 : CNF.NClause := [(48,false),(17,true),(64,true),(70,true),(76,false),(77,true),(83,true),(88,false)]
theorem inputList6200 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6200 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6200 (by decide) v hb
mask_input "6200|309560567685352458024910848|9823721322733653165473792"
def inputClause6201 : CNF.NClause := [(48,false),(17,false),(64,false),(70,false),(76,true),(77,true),(83,true),(88,false)]
theorem inputList6201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6201 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6201 (by decide) v hb
mask_input "6201|309486208859991334822477824|9898080148094776367906816"
def inputClause6203 : CNF.NClause := [(48,false),(17,false),(64,true),(70,false),(76,true),(77,true),(83,true),(88,false)]
theorem inputList6203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6203 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6203 (by decide) v hb
mask_input "6203|309486190413247261112926208|9898098594838850077458432"
def inputClause6204 : CNF.NClause := [(48,false),(17,true),(64,true),(70,false),(76,true),(77,true),(83,true),(88,false)]
theorem inputList6204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6204 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6204 (by decide) v hb
mask_input "6204|309486190413247261112795136|9898098594838850077589504"
def inputClause6205 : CNF.NClause := [(48,false),(17,false),(64,false),(70,true),(76,true),(77,true),(83,true),(88,false)]
theorem inputList6205 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6205 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6205 (by decide) v hb
mask_input "6205|309485028268370617411174400|9899260739715493779210240"
def inputClause6206 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,true),(77,true),(83,true),(88,false)]
theorem inputList6206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6206 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6206 (by decide) v hb
mask_input "6206|309485028268370617411043328|9899260739715493779341312"
def inputClause6207 : CNF.NClause := [(48,false),(17,false),(64,true),(70,true),(76,true),(77,true),(83,true),(88,false)]
theorem inputList6207 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6207 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6207 (by decide) v hb
mask_input "6207|309485009821626543701622784|9899279186459567488761856"
def inputClause6208 : CNF.NClause := [(48,false),(17,true),(64,true),(70,true),(76,true),(77,true),(83,true),(88,false)]
theorem inputList6208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6208 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6208 (by decide) v hb
mask_input "6208|309485009821626543701491712|9899279186459567488892928"
def inputClause6209 : CNF.NClause := [(48,false),(17,false),(64,false),(70,false),(76,false),(77,false),(83,false),(88,true)]
theorem inputList6209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6209 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6209 (by decide) v hb
mask_input "6209|9899279186741042465603584|309485009821345068724781056"
def inputClause6210 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,false),(77,false),(83,false),(88,true)]
theorem inputList6210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6210 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6210 (by decide) v hb
mask_input "6210|9899279186741042465472512|309485009821345068724912128"
def inputClause6211 : CNF.NClause := [(48,false),(17,false),(64,true),(70,false),(76,false),(77,false),(83,false),(88,true)]
theorem inputList6211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6211 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6211 (by decide) v hb
mask_input "6211|9899260739996968756051968|309485028268089142434332672"
def inputClause6212 : CNF.NClause := [(48,false),(17,true),(64,true),(70,false),(76,false),(77,false),(83,false),(88,true)]
theorem inputList6212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6212 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6212 (by decide) v hb
mask_input "6212|9899260739996968755920896|309485028268089142434463744"
def inputClause6213 : CNF.NClause := [(48,false),(17,false),(64,false),(70,true),(76,false),(77,false),(83,false),(88,true)]
theorem inputList6213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6213 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6213 (by decide) v hb
mask_input "6213|9898098595120325054300160|309486190412965786136084480"
def inputClause6214 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,false),(77,false),(83,false),(88,true)]
theorem inputList6214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6214 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6214 (by decide) v hb
mask_input "6214|9898098595120325054169088|309486190412965786136215552"
def inputClause6215 : CNF.NClause := [(48,false),(17,false),(64,true),(70,true),(76,false),(77,false),(83,false),(88,true)]
theorem inputList6215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6215 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6215 (by decide) v hb
mask_input "6215|9898080148376251344748544|309486208859709859845636096"
def inputClause6216 : CNF.NClause := [(48,false),(17,true),(64,true),(70,true),(76,false),(77,false),(83,false),(88,true)]
theorem inputList6216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6216 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6216 (by decide) v hb
mask_input "6216|9898080148376251344617472|309486208859709859845767168"
def inputClause6217 : CNF.NClause := [(48,false),(17,false),(64,false),(70,false),(76,true),(77,false),(83,false),(88,true)]
theorem inputList6217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6217 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6217 (by decide) v hb
mask_input "6217|9823721323015128142184448|309560567685070983048200192"
def inputClause6219 : CNF.NClause := [(48,false),(17,false),(64,true),(70,false),(76,true),(77,false),(83,false),(88,true)]
theorem inputList6219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6219 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6219 (by decide) v hb
mask_input "6219|9823702876271054432632832|309560586131815056757751808"
def inputClause6220 : CNF.NClause := [(48,false),(17,true),(64,true),(70,false),(76,true),(77,false),(83,false),(88,true)]
theorem inputList6220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6220 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6220 (by decide) v hb
mask_input "6220|9823702876271054432501760|309560586131815056757882880"
def inputClause6221 : CNF.NClause := [(48,false),(17,false),(64,false),(70,true),(76,true),(77,false),(83,false),(88,true)]
theorem inputList6221 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6221 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6221 (by decide) v hb
mask_input "6221|9822540731394410730881024|309561748276691700459503616"
def inputClause6222 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,true),(77,false),(83,false),(88,true)]
theorem inputList6222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6222 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6222 (by decide) v hb
mask_input "6222|9822540731394410730749952|309561748276691700459634688"
def inputClause6224 : CNF.NClause := [(48,false),(17,true),(64,true),(70,true),(76,true),(77,false),(83,false),(88,true)]
theorem inputList6224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6224 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6224 (by decide) v hb
mask_input "6224|9822522284650337021198336|309561766723435774169186304"
def inputClause6225 : CNF.NClause := [(48,false),(17,false),(64,false),(70,false),(76,false),(77,true),(83,false),(88,true)]
theorem inputList6225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6225 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6225 (by decide) v hb
mask_input "6225|9748163459289213818765312|309636125548796897371619328"
def inputClause6226 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(76,false),(77,true),(83,false),(88,true)]
theorem inputList6226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6226 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6226 (by decide) v hb
mask_input "6226|9748163459289213818634240|309636125548796897371750400"
def inputClause6227 : CNF.NClause := [(48,false),(17,false),(64,true),(70,false),(76,false),(77,true),(83,false),(88,true)]
theorem inputList6227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6227 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6227 (by decide) v hb
mask_input "6227|9748145012545140109213696|309636143995540971081170944"
def inputClause6228 : CNF.NClause := [(48,false),(17,true),(64,true),(70,false),(76,false),(77,true),(83,false),(88,true)]
theorem inputList6228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6228 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6228 (by decide) v hb
mask_input "6228|9748145012545140109082624|309636143995540971081302016"
def inputClause6229 : CNF.NClause := [(48,false),(17,false),(64,false),(70,true),(76,false),(77,true),(83,false),(88,true)]
theorem inputList6229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6229 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6229 (by decide) v hb
mask_input "6229|9746982867668496407461888|309637306140417614782922752"
def inputClause6230 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,false),(77,true),(83,false),(88,true)]
theorem inputList6230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6230 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6230 (by decide) v hb
mask_input "6230|9746982867668496407330816|309637306140417614783053824"
def inputClause6231 : CNF.NClause := [(48,false),(17,false),(64,true),(70,true),(76,false),(77,true),(83,false),(88,true)]
theorem inputList6231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6231 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6231 (by decide) v hb
mask_input "6231|9746964420924422697910272|309637324587161688492474368"
def inputClause6232 : CNF.NClause := [(48,false),(17,true),(64,true),(70,true),(76,false),(77,true),(83,false),(88,true)]
theorem inputList6232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6232 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6232 (by decide) v hb
mask_input "6232|9746964420924422697779200|309637324587161688492605440"
def inputClause6233 : CNF.NClause := [(48,false),(17,false),(64,false),(70,false),(76,true),(77,true),(83,false),(88,true)]
theorem inputList6233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6233 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6233 (by decide) v hb
mask_input "6233|9672605595563299495346176|309711683412522811695038464"
def inputClause6235 : CNF.NClause := [(48,false),(17,false),(64,true),(70,false),(76,true),(77,true),(83,false),(88,true)]
theorem inputList6235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6235 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6235 (by decide) v hb
mask_input "6235|9672587148819225785794560|309711701859266885404590080"
def inputClause6236 : CNF.NClause := [(48,false),(17,true),(64,true),(70,false),(76,true),(77,true),(83,false),(88,true)]
theorem inputList6236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6236 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6236 (by decide) v hb
mask_input "6236|9672587148819225785663488|309711701859266885404721152"
def inputClause6237 : CNF.NClause := [(48,false),(17,false),(64,false),(70,true),(76,true),(77,true),(83,false),(88,true)]
theorem inputList6237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6237 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6237 (by decide) v hb
mask_input "6237|9671425003942582084042752|309712864004143529106341888"
def inputClause6238 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,true),(77,true),(83,false),(88,true)]
theorem inputList6238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6238 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6238 (by decide) v hb
mask_input "6238|9671425003942582083911680|309712864004143529106472960"
def inputClause6239 : CNF.NClause := [(48,false),(17,false),(64,true),(70,true),(76,true),(77,true),(83,false),(88,true)]
theorem inputList6239 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6239 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6239 (by decide) v hb
mask_input "6239|9671406557198508374491136|309712882450887602815893504"
end Percolation.MaskChain
