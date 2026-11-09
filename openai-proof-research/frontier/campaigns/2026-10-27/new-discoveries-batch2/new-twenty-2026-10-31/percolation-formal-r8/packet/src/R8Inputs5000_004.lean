import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause3440 : CNF.NClause := [(115,false),(33,true),(36,true),(44,true),(47,true),(55,false),(59,true)]
theorem inputList3440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3440 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3440 (by decide) v hb
mask_input "3440|41538374868278621064272767652724736|576619159287234560"
def inputClause3448 : CNF.NClause := [(115,false),(33,true),(36,true),(44,true),(47,false),(55,true),(59,true)]
theorem inputList3448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3448 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3448 (by decide) v hb
mask_input "3448|41538374868278621028384708122116096|612507218817843200"
def inputClause3452 : CNF.NClause := [(115,false),(33,true),(36,true),(44,false),(47,true),(55,true),(59,true)]
theorem inputList3452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3452 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3452 (by decide) v hb
mask_input "3452|41538374868278621028261562819805184|612630364120154112"
def inputClause3454 : CNF.NClause := [(115,false),(33,true),(36,false),(44,true),(47,true),(55,true),(59,true)]
theorem inputList3454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3454 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3454 (by decide) v hb
mask_input "3454|41538374868278621028244039353237504|612647887586721792"
def inputClause3455 : CNF.NClause := [(115,false),(33,false),(36,true),(44,true),(47,true),(55,true),(59,true)]
theorem inputList3455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3455 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 22) 22) (activationX_mem 22) inputClause3455 (by decide) v hb
mask_input "3455|41538374868278621028243979223695360|612647947716263936"
def inputClause3504 : CNF.NClause := [(116,false),(34,true),(36,true),(43,true),(50,true),(52,false),(58,true)]
theorem inputList3504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3504 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3504 (by decide) v hb
mask_input "3504|83076749736557242060991540894892032|289365158050922496"
def inputClause3512 : CNF.NClause := [(116,false),(34,true),(36,true),(43,true),(50,false),(52,true),(58,true)]
theorem inputList3512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3512 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3512 (by decide) v hb
mask_input "3512|83076749736557242057613841174364160|292742857771450368"
def inputClause3516 : CNF.NClause := [(116,false),(34,true),(36,true),(43,false),(50,true),(52,true),(58,true)]
theorem inputList3516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3516 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3516 (by decide) v hb
mask_input "3516|83076749736557242056496737360543744|293859961585270784"
def inputClause3518 : CNF.NClause := [(116,false),(34,true),(36,false),(43,true),(50,true),(52,true),(58,true)]
theorem inputList3518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3518 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3518 (by decide) v hb
mask_input "3518|83076749736557242056488009986998272|293868688958816256"
def inputClause3519 : CNF.NClause := [(116,false),(34,false),(36,true),(43,true),(50,true),(52,true),(58,true)]
theorem inputList3519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3519 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 23) 23) (activationX_mem 23) inputClause3519 (by decide) v hb
mask_input "3519|83076749736557242056487958447390720|293868740498423808"
def inputClause3552 : CNF.NClause := [(117,false),(32,true),(36,true),(45,true),(49,true),(53,true),(60,false)]
theorem inputList3552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3552 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3552 (by decide) v hb
mask_input "3552|166153499473114485265897387141890048|9605406594695168"
def inputClause3576 : CNF.NClause := [(117,false),(32,true),(36,true),(45,true),(49,false),(53,true),(60,true)]
theorem inputList3576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3576 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3576 (by decide) v hb
mask_input "3576|166153499473114484113538832488464384|1161963961248120832"
def inputClause3580 : CNF.NClause := [(117,false),(32,true),(36,true),(45,false),(49,true),(53,true),(60,true)]
theorem inputList3580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3580 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3580 (by decide) v hb
mask_input "3580|166153499473114484113011066907131904|1162491726829453312"
def inputClause3583 : CNF.NClause := [(117,false),(32,false),(36,true),(45,true),(49,true),(53,true),(60,true)]
theorem inputList3583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3583 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 24) 24) (activationX_mem 24) inputClause3583 (by decide) v hb
mask_input "3583|166153499473114484112975886830010368|1162526906906574848"
def inputClause3632 : CNF.NClause := [(118,false),(31,true),(32,true),(33,true),(34,true),(35,false),(61,true)]
theorem inputList3632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3632 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3632 (by decide) v hb
mask_input "3632|332306998946228968225951799429824512|2305843041425948672"
def inputClause3640 : CNF.NClause := [(118,false),(31,true),(32,true),(33,true),(34,false),(35,true),(61,true)]
theorem inputList3640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3640 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3640 (by decide) v hb
mask_input "3640|332306998946228968225951782249955328|2305843058605817856"
def inputClause3644 : CNF.NClause := [(118,false),(31,true),(32,true),(33,false),(34,true),(35,true),(61,true)]
theorem inputList3644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3644 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3644 (by decide) v hb
mask_input "3644|332306998946228968225951773660020736|2305843067195752448"
def inputClause3646 : CNF.NClause := [(118,false),(31,true),(32,false),(33,true),(34,true),(35,true),(61,true)]
theorem inputList3646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3646 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 25) 25) (activationX_mem 25) inputClause3646 (by decide) v hb
mask_input "3646|332306998946228968225951769365053440|2305843071490719744"
def inputClause3760 : CNF.NClause := [(120,false),(31,true),(38,true),(45,true),(47,true),(54,false),(58,true)]
theorem inputList3760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3760 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3760 (by decide) v hb
mask_input "3760|1329227995784915872921821458789826560|288406575037546496"
def inputClause3768 : CNF.NClause := [(120,false),(31,true),(38,true),(45,true),(47,false),(54,true),(58,true)]
theorem inputList3768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3768 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3768 (by decide) v hb
mask_input "3768|1329227995784915872903947797768699904|306280236058673152"
def inputClause3772 : CNF.NClause := [(120,false),(31,true),(38,true),(45,false),(47,true),(54,true),(58,true)]
theorem inputList3772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3772 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3772 (by decide) v hb
mask_input "3772|1329227995784915872903842244652433408|306385789174939648"
def inputClause3774 : CNF.NClause := [(120,false),(31,true),(38,false),(45,true),(47,true),(54,true),(58,true)]
theorem inputList3774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3774 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3774 (by decide) v hb
mask_input "3774|1329227995784915872903807335158251520|306420698669121536"
def inputClause3836 : CNF.NClause := [(121,false),(31,true),(39,true),(42,false),(50,true),(53,true),(59,true)]
theorem inputList3836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3836 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3836 (by decide) v hb
mask_input "3836|2658455991569831745807618518607200256|586594403368304640"
def inputClause3860 : CNF.NClause := [(122,true),(31,true),(37,true),(43,false),(49,false),(55,true),(57,false)]
theorem inputList3860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3860 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3860 (by decide) v hb
mask_input "3860|144686934122299392|5316911983139663491651257177726779392"
def inputClause3900 : CNF.NClause := [(122,false),(31,true),(37,true),(43,false),(49,true),(55,true),(57,true)]
theorem inputList3900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3900 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3900 (by decide) v hb
mask_input "3900|5316911983139663491615237037214400512|180707074634678272"
def inputClause3902 : CNF.NClause := [(122,false),(31,true),(37,false),(43,true),(49,true),(55,true),(57,true)]
theorem inputList3902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3902 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3902 (by decide) v hb
mask_input "3902|5316911983139663491615228378560331776|180715733288747008"
def inputClause3952 : CNF.NClause := [(123,false),(31,true),(36,true),(41,true),(46,true),(51,false),(56,true)]
theorem inputList3952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3952 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3952 (by decide) v hb
mask_input "3952|10633823966279326983232708282056441856|72130232672321536"
def inputClause3960 : CNF.NClause := [(123,false),(31,true),(36,true),(41,true),(46,false),(51,true),(56,true)]
theorem inputList3960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3960 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3960 (by decide) v hb
mask_input "3960|10633823966279326983230526850986934272|74311663741829120"
def inputClause3964 : CNF.NClause := [(123,false),(31,true),(36,true),(41,false),(46,true),(51,true),(56,true)]
theorem inputList3964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3964 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3964 (by decide) v hb
mask_input "3964|10633823966279326983230458681266012160|74379833462751232"
def inputClause3966 : CNF.NClause := [(123,false),(31,true),(36,false),(41,true),(46,true),(51,true),(56,true)]
theorem inputList3966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3966 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3966 (by decide) v hb
mask_input "3966|10633823966279326983230456550962233344|74381963766530048"
def inputClause4097 : CNF.NClause := [(32,true),(1,false),(66,false),(71,false),(76,false),(81,false),(86,false),(87,false)]
theorem inputList4097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4097 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4097 (by decide) v hb
mask_input "4097|234609601839181703877230594|4294967296"
def inputClause4098 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,false),(81,false),(86,false),(87,false)]
theorem inputList4098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4098 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4098 (by decide) v hb
mask_input "4098|234609601839181708172197888|2"
def inputClause4099 : CNF.NClause := [(32,false),(1,false),(66,true),(71,false),(76,false),(81,false),(86,false),(87,false)]
theorem inputList4099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4099 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4099 (by decide) v hb
mask_input "4099|234609528052205413333991426|73786976294838206464"
def inputClause4100 : CNF.NClause := [(32,false),(1,true),(66,true),(71,false),(76,false),(81,false),(86,false),(87,false)]
theorem inputList4100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4100 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4100 (by decide) v hb
mask_input "4100|234609528052205413333991424|73786976294838206466"
def inputClause4101 : CNF.NClause := [(32,false),(1,false),(66,false),(71,true),(76,false),(81,false),(86,false),(87,false)]
theorem inputList4101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4101 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4101 (by decide) v hb
mask_input "4101|234607240655940273349591042|2361183241434822606848"
def inputClause4102 : CNF.NClause := [(32,false),(1,true),(66,false),(71,true),(76,false),(81,false),(86,false),(87,false)]
theorem inputList4102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4102 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4102 (by decide) v hb
mask_input "4102|234607240655940273349591040|2361183241434822606850"
def inputClause4103 : CNF.NClause := [(32,false),(1,false),(66,true),(71,true),(76,false),(81,false),(86,false),(87,false)]
theorem inputList4103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4103 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4103 (by decide) v hb
mask_input "4103|234607166868963978511384578|2434970217729660813312"
def inputClause4104 : CNF.NClause := [(32,false),(1,true),(66,true),(71,true),(76,false),(81,false),(86,false),(87,false)]
theorem inputList4104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4104 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4104 (by decide) v hb
mask_input "4104|234607166868963978511384576|2434970217729660813314"
def inputClause4105 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,true),(81,false),(86,false),(87,false)]
theorem inputList4105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4105 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4105 (by decide) v hb
mask_input "4105|234534043975455793848778754|75557863725914323419136"
def inputClause4106 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,true),(81,false),(86,false),(87,false)]
theorem inputList4106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4106 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4106 (by decide) v hb
mask_input "4106|234534043975455793848778752|75557863725914323419138"
end Percolation.MaskChain
