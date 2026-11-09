import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause3695 : CNF.NClause := [(119,true),(31,false),(40,true),(44,true),(48,true),(52,false),(60,true)]
theorem inputList3695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3695 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3695 (by decide) v hb
mask_input "3695|4503601774854144|664613997892457937605125201421402112"
def inputClause3696 : CNF.NClause := [(119,false),(31,true),(40,true),(44,true),(48,true),(52,false),(60,true)]
theorem inputList3696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3696 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3696 (by decide) v hb
mask_input "3696|664613997892457936456407129767542784|1153221673428713472"
def inputClause3697 : CNF.NClause := [(119,true),(31,false),(40,false),(44,false),(48,false),(52,true),(60,true)]
theorem inputList3697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3697 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3697 (by decide) v hb
mask_input "3697|300168821866496|664613997892457937609328634374389760"
def inputClause3698 : CNF.NClause := [(119,true),(31,true),(40,false),(44,false),(48,false),(52,true),(60,true)]
theorem inputList3698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3698 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3698 (by decide) v hb
mask_input "3698|300166674382848|664613997892457937609328636521873408"
def inputClause3699 : CNF.NClause := [(119,true),(31,false),(40,true),(44,false),(48,false),(52,true),(60,true)]
theorem inputList3699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3699 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3699 (by decide) v hb
mask_input "3699|299069310238720|664613997892457937609329733886017536"
def inputClause3700 : CNF.NClause := [(119,true),(31,true),(40,true),(44,false),(48,false),(52,true),(60,true)]
theorem inputList3700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3700 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3700 (by decide) v hb
mask_input "3700|299067162755072|664613997892457937609329736033501184"
def inputClause3701 : CNF.NClause := [(119,true),(31,false),(40,false),(44,true),(48,false),(52,true),(60,true)]
theorem inputList3701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3701 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3701 (by decide) v hb
mask_input "3701|282576635822080|664613997892457937609346226560434176"
def inputClause3702 : CNF.NClause := [(119,true),(31,true),(40,false),(44,true),(48,false),(52,true),(60,true)]
theorem inputList3702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3702 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3702 (by decide) v hb
mask_input "3702|282574488338432|664613997892457937609346228707917824"
def inputClause3704 : CNF.NClause := [(119,false),(31,true),(40,true),(44,true),(48,false),(52,true),(60,true)]
theorem inputList3704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3704 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3704 (by decide) v hb
mask_input "3704|664613997892457936452185005116882944|1157443798079373312"
def inputClause3705 : CNF.NClause := [(119,true),(31,false),(40,false),(44,false),(48,true),(52,true),(60,true)]
theorem inputList3705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3705 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3705 (by decide) v hb
mask_input "3705|18693845155840|664613997892457937609610109351100416"
def inputClause3706 : CNF.NClause := [(119,true),(31,true),(40,false),(44,false),(48,true),(52,true),(60,true)]
theorem inputList3706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3706 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3706 (by decide) v hb
mask_input "3706|18691697672192|664613997892457937609610111498584064"
def inputClause3707 : CNF.NClause := [(119,true),(31,false),(40,true),(44,false),(48,true),(52,true),(60,true)]
theorem inputList3707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3707 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3707 (by decide) v hb
mask_input "3707|17594333528064|664613997892457937609611208862728192"
def inputClause3708 : CNF.NClause := [(119,false),(31,true),(40,true),(44,false),(48,true),(52,true),(60,true)]
theorem inputList3708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3708 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3708 (by decide) v hb
mask_input "3708|664613997892457936451921122326216704|1157707680870039552"
def inputClause3710 : CNF.NClause := [(119,false),(31,true),(40,false),(44,true),(48,true),(52,true),(60,true)]
theorem inputList3710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3710 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3710 (by decide) v hb
mask_input "3710|664613997892457936451904629651800064|1157724173544456192"
def inputClause3712 : CNF.NClause := [(119,false),(31,true),(40,true),(44,true),(48,true),(52,true),(60,true)]
theorem inputList3712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3712 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3712 (by decide) v hb
mask_input "3712|664613997892457936451903530140172288|1157725273056083968"
def inputClause3713 : CNF.NClause := [(120,true),(31,false),(38,false),(45,false),(47,false),(54,false),(58,false)]
theorem inputList3713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3713 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3713 (by decide) v hb
mask_input "3713|306420973547028480|1329227995784915872903807060280344576"
def inputClause3714 : CNF.NClause := [(120,true),(31,true),(38,false),(45,false),(47,false),(54,false),(58,false)]
theorem inputList3714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3714 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3714 (by decide) v hb
mask_input "3714|306420971399544832|1329227995784915872903807062427828224"
def inputClause3715 : CNF.NClause := [(120,true),(31,false),(38,true),(45,false),(47,false),(54,false),(58,false)]
theorem inputList3715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3715 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3715 (by decide) v hb
mask_input "3715|306420698669121536|1329227995784915872903807335158251520"
def inputClause3716 : CNF.NClause := [(120,true),(31,true),(38,true),(45,false),(47,false),(54,false),(58,false)]
theorem inputList3716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3716 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3716 (by decide) v hb
mask_input "3716|306420696521637888|1329227995784915872903807337305735168"
def inputClause3717 : CNF.NClause := [(120,true),(31,false),(38,false),(45,true),(47,false),(54,false),(58,false)]
theorem inputList3717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3717 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3717 (by decide) v hb
mask_input "3717|306385789174939648|1329227995784915872903842244652433408"
def inputClause3718 : CNF.NClause := [(120,true),(31,true),(38,false),(45,true),(47,false),(54,false),(58,false)]
theorem inputList3718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3718 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3718 (by decide) v hb
mask_input "3718|306385787027456000|1329227995784915872903842246799917056"
def inputClause3719 : CNF.NClause := [(120,true),(31,false),(38,true),(45,true),(47,false),(54,false),(58,false)]
theorem inputList3719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3719 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3719 (by decide) v hb
mask_input "3719|306385514297032704|1329227995784915872903842519530340352"
def inputClause3720 : CNF.NClause := [(120,true),(31,true),(38,true),(45,true),(47,false),(54,false),(58,false)]
theorem inputList3720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3720 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3720 (by decide) v hb
mask_input "3720|306385512149549056|1329227995784915872903842521677824000"
def inputClause3721 : CNF.NClause := [(120,true),(31,false),(38,false),(45,false),(47,true),(54,false),(58,false)]
theorem inputList3721 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3721 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3721 (by decide) v hb
mask_input "3721|306280236058673152|1329227995784915872903947797768699904"
def inputClause3722 : CNF.NClause := [(120,true),(31,true),(38,false),(45,false),(47,true),(54,false),(58,false)]
theorem inputList3722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3722 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3722 (by decide) v hb
mask_input "3722|306280233911189504|1329227995784915872903947799916183552"
def inputClause3723 : CNF.NClause := [(120,true),(31,false),(38,true),(45,false),(47,true),(54,false),(58,false)]
theorem inputList3723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3723 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3723 (by decide) v hb
mask_input "3723|306279961180766208|1329227995784915872903948072646606848"
def inputClause3724 : CNF.NClause := [(120,true),(31,true),(38,true),(45,false),(47,true),(54,false),(58,false)]
theorem inputList3724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3724 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3724 (by decide) v hb
mask_input "3724|306279959033282560|1329227995784915872903948074794090496"
def inputClause3725 : CNF.NClause := [(120,true),(31,false),(38,false),(45,true),(47,true),(54,false),(58,false)]
theorem inputList3725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3725 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3725 (by decide) v hb
mask_input "3725|306245051686584320|1329227995784915872903982982140788736"
def inputClause3726 : CNF.NClause := [(120,true),(31,true),(38,false),(45,true),(47,true),(54,false),(58,false)]
theorem inputList3726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3726 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3726 (by decide) v hb
mask_input "3726|306245049539100672|1329227995784915872903982984288272384"
def inputClause3727 : CNF.NClause := [(120,true),(31,false),(38,true),(45,true),(47,true),(54,false),(58,false)]
theorem inputList3727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3727 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3727 (by decide) v hb
mask_input "3727|306244776808677376|1329227995784915872903983257018695680"
def inputClause3728 : CNF.NClause := [(120,true),(31,true),(38,true),(45,true),(47,true),(54,false),(58,false)]
theorem inputList3728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3728 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3728 (by decide) v hb
mask_input "3728|306244774661193728|1329227995784915872903983259166179328"
def inputClause3729 : CNF.NClause := [(120,true),(31,false),(38,false),(45,false),(47,false),(54,true),(58,false)]
theorem inputList3729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3729 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3729 (by decide) v hb
mask_input "3729|288406575037546496|1329227995784915872921821458789826560"
def inputClause3730 : CNF.NClause := [(120,true),(31,true),(38,false),(45,false),(47,false),(54,true),(58,false)]
theorem inputList3730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3730 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3730 (by decide) v hb
mask_input "3730|288406572890062848|1329227995784915872921821460937310208"
def inputClause3731 : CNF.NClause := [(120,true),(31,false),(38,true),(45,false),(47,false),(54,true),(58,false)]
theorem inputList3731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3731 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3731 (by decide) v hb
mask_input "3731|288406300159639552|1329227995784915872921821733667733504"
def inputClause3732 : CNF.NClause := [(120,true),(31,true),(38,true),(45,false),(47,false),(54,true),(58,false)]
theorem inputList3732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3732 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3732 (by decide) v hb
mask_input "3732|288406298012155904|1329227995784915872921821735815217152"
def inputClause3733 : CNF.NClause := [(120,true),(31,false),(38,false),(45,true),(47,false),(54,true),(58,false)]
theorem inputList3733 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3733 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3733 (by decide) v hb
mask_input "3733|288371390665457664|1329227995784915872921856643161915392"
def inputClause3734 : CNF.NClause := [(120,true),(31,true),(38,false),(45,true),(47,false),(54,true),(58,false)]
theorem inputList3734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3734 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3734 (by decide) v hb
mask_input "3734|288371388517974016|1329227995784915872921856645309399040"
def inputClause3736 : CNF.NClause := [(120,true),(31,true),(38,true),(45,true),(47,false),(54,true),(58,false)]
theorem inputList3736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3736 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3736 (by decide) v hb
mask_input "3736|288371113640067072|1329227995784915872921856920187305984"
def inputClause3737 : CNF.NClause := [(120,true),(31,false),(38,false),(45,false),(47,true),(54,true),(58,false)]
theorem inputList3737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3737 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3737 (by decide) v hb
mask_input "3737|288265837549191168|1329227995784915872921962196278181888"
def inputClause3738 : CNF.NClause := [(120,true),(31,true),(38,false),(45,false),(47,true),(54,true),(58,false)]
theorem inputList3738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3738 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3738 (by decide) v hb
mask_input "3738|288265835401707520|1329227995784915872921962198425665536"
end Percolation.MaskChain
