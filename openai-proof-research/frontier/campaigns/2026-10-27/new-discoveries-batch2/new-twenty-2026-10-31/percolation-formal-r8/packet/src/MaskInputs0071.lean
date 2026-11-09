import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause3654 : CNF.NClause := [(119,true),(31,true),(40,false),(44,true),(48,false),(52,false),(60,false)]
theorem inputList3654 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3654 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3654 (by decide) v hb
mask_input "3654|1157707678722555904|664613997892457936451921124473700352"
def inputClause3655 : CNF.NClause := [(119,true),(31,false),(40,true),(44,true),(48,false),(52,false),(60,false)]
theorem inputList3655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3655 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3655 (by decide) v hb
mask_input "3655|1157706581358411776|664613997892457936451922221837844480"
def inputClause3656 : CNF.NClause := [(119,true),(31,true),(40,true),(44,true),(48,false),(52,false),(60,false)]
theorem inputList3656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3656 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3656 (by decide) v hb
mask_input "3656|1157706579210928128|664613997892457936451922223985328128"
def inputClause3657 : CNF.NClause := [(119,true),(31,false),(40,false),(44,false),(48,true),(52,false),(60,false)]
theorem inputList3657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3657 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3657 (by decide) v hb
mask_input "3657|1157443798079373312|664613997892457936452185005116882944"
def inputClause3658 : CNF.NClause := [(119,true),(31,true),(40,false),(44,false),(48,true),(52,false),(60,false)]
theorem inputList3658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3658 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3658 (by decide) v hb
mask_input "3658|1157443795931889664|664613997892457936452185007264366592"
def inputClause3659 : CNF.NClause := [(119,true),(31,false),(40,true),(44,false),(48,true),(52,false),(60,false)]
theorem inputList3659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3659 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3659 (by decide) v hb
mask_input "3659|1157442698567745536|664613997892457936452186104628510720"
def inputClause3660 : CNF.NClause := [(119,true),(31,true),(40,true),(44,false),(48,true),(52,false),(60,false)]
theorem inputList3660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3660 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3660 (by decide) v hb
mask_input "3660|1157442696420261888|664613997892457936452186106775994368"
def inputClause3661 : CNF.NClause := [(119,true),(31,false),(40,false),(44,true),(48,true),(52,false),(60,false)]
theorem inputList3661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3661 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3661 (by decide) v hb
mask_input "3661|1157426205893328896|664613997892457936452202597302927360"
def inputClause3662 : CNF.NClause := [(119,true),(31,true),(40,false),(44,true),(48,true),(52,false),(60,false)]
theorem inputList3662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3662 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3662 (by decide) v hb
mask_input "3662|1157426203745845248|664613997892457936452202599450411008"
def inputClause3663 : CNF.NClause := [(119,true),(31,false),(40,true),(44,true),(48,true),(52,false),(60,false)]
theorem inputList3663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3663 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3663 (by decide) v hb
mask_input "3663|1157425106381701120|664613997892457936452203696814555136"
def inputClause3664 : CNF.NClause := [(119,true),(31,true),(40,true),(44,true),(48,true),(52,false),(60,false)]
theorem inputList3664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3664 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3664 (by decide) v hb
mask_input "3664|1157425104234217472|664613997892457936452203698962038784"
def inputClause3665 : CNF.NClause := [(119,true),(31,false),(40,false),(44,false),(48,false),(52,true),(60,false)]
theorem inputList3665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3665 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3665 (by decide) v hb
mask_input "3665|1153221673428713472|664613997892457936456407129767542784"
def inputClause3666 : CNF.NClause := [(119,true),(31,true),(40,false),(44,false),(48,false),(52,true),(60,false)]
theorem inputList3666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3666 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3666 (by decide) v hb
mask_input "3666|1153221671281229824|664613997892457936456407131915026432"
def inputClause3667 : CNF.NClause := [(119,true),(31,false),(40,true),(44,false),(48,false),(52,true),(60,false)]
theorem inputList3667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3667 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3667 (by decide) v hb
mask_input "3667|1153220573917085696|664613997892457936456408229279170560"
def inputClause3668 : CNF.NClause := [(119,true),(31,true),(40,true),(44,false),(48,false),(52,true),(60,false)]
theorem inputList3668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3668 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3668 (by decide) v hb
mask_input "3668|1153220571769602048|664613997892457936456408231426654208"
def inputClause3669 : CNF.NClause := [(119,true),(31,false),(40,false),(44,true),(48,false),(52,true),(60,false)]
theorem inputList3669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3669 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3669 (by decide) v hb
mask_input "3669|1153204081242669056|664613997892457936456424721953587200"
def inputClause3670 : CNF.NClause := [(119,true),(31,true),(40,false),(44,true),(48,false),(52,true),(60,false)]
theorem inputList3670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3670 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3670 (by decide) v hb
mask_input "3670|1153204079095185408|664613997892457936456424724101070848"
def inputClause3672 : CNF.NClause := [(119,true),(31,true),(40,true),(44,true),(48,false),(52,true),(60,false)]
theorem inputList3672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3672 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3672 (by decide) v hb
mask_input "3672|1153202979583557632|664613997892457936456425823612698624"
def inputClause3673 : CNF.NClause := [(119,true),(31,false),(40,false),(44,false),(48,true),(52,true),(60,false)]
theorem inputList3673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3673 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3673 (by decide) v hb
mask_input "3673|1152940198452002816|664613997892457936456688604744253440"
def inputClause3674 : CNF.NClause := [(119,true),(31,true),(40,false),(44,false),(48,true),(52,true),(60,false)]
theorem inputList3674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3674 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3674 (by decide) v hb
mask_input "3674|1152940196304519168|664613997892457936456688606891737088"
def inputClause3675 : CNF.NClause := [(119,true),(31,false),(40,true),(44,false),(48,true),(52,true),(60,false)]
theorem inputList3675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3675 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3675 (by decide) v hb
mask_input "3675|1152939098940375040|664613997892457936456689704255881216"
def inputClause3676 : CNF.NClause := [(119,true),(31,true),(40,true),(44,false),(48,true),(52,true),(60,false)]
theorem inputList3676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3676 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3676 (by decide) v hb
mask_input "3676|1152939096792891392|664613997892457936456689706403364864"
def inputClause3677 : CNF.NClause := [(119,true),(31,false),(40,false),(44,true),(48,true),(52,true),(60,false)]
theorem inputList3677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3677 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3677 (by decide) v hb
mask_input "3677|1152922606265958400|664613997892457936456706196930297856"
def inputClause3678 : CNF.NClause := [(119,true),(31,true),(40,false),(44,true),(48,true),(52,true),(60,false)]
theorem inputList3678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3678 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3678 (by decide) v hb
mask_input "3678|1152922604118474752|664613997892457936456706199077781504"
def inputClause3679 : CNF.NClause := [(119,true),(31,false),(40,true),(44,true),(48,true),(52,true),(60,false)]
theorem inputList3679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3679 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3679 (by decide) v hb
mask_input "3679|1152921506754330624|664613997892457936456707296441925632"
def inputClause3680 : CNF.NClause := [(119,false),(31,true),(40,true),(44,true),(48,true),(52,true),(60,false)]
theorem inputList3680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3680 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3680 (by decide) v hb
mask_input "3680|664613997892457937604825034747019264|4803768449236992"
def inputClause3681 : CNF.NClause := [(119,true),(31,false),(40,false),(44,false),(48,false),(52,false),(60,true)]
theorem inputList3681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3681 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3681 (by decide) v hb
mask_input "3681|4803768449236992|664613997892457937604825034747019264"
def inputClause3682 : CNF.NClause := [(119,true),(31,true),(40,false),(44,false),(48,false),(52,false),(60,true)]
theorem inputList3682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3682 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3682 (by decide) v hb
mask_input "3682|4803766301753344|664613997892457937604825036894502912"
def inputClause3683 : CNF.NClause := [(119,true),(31,false),(40,true),(44,false),(48,false),(52,false),(60,true)]
theorem inputList3683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3683 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3683 (by decide) v hb
mask_input "3683|4802668937609216|664613997892457937604826134258647040"
def inputClause3684 : CNF.NClause := [(119,true),(31,true),(40,true),(44,false),(48,false),(52,false),(60,true)]
theorem inputList3684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3684 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3684 (by decide) v hb
mask_input "3684|4802666790125568|664613997892457937604826136406130688"
def inputClause3685 : CNF.NClause := [(119,true),(31,false),(40,false),(44,true),(48,false),(52,false),(60,true)]
theorem inputList3685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3685 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3685 (by decide) v hb
mask_input "3685|4786176263192576|664613997892457937604842626933063680"
def inputClause3686 : CNF.NClause := [(119,true),(31,true),(40,false),(44,true),(48,false),(52,false),(60,true)]
theorem inputList3686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3686 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3686 (by decide) v hb
mask_input "3686|4786174115708928|664613997892457937604842629080547328"
def inputClause3687 : CNF.NClause := [(119,true),(31,false),(40,true),(44,true),(48,false),(52,false),(60,true)]
theorem inputList3687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3687 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3687 (by decide) v hb
mask_input "3687|4785076751564800|664613997892457937604843726444691456"
def inputClause3688 : CNF.NClause := [(119,true),(31,true),(40,true),(44,true),(48,false),(52,false),(60,true)]
theorem inputList3688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3688 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3688 (by decide) v hb
mask_input "3688|4785074604081152|664613997892457937604843728592175104"
def inputClause3689 : CNF.NClause := [(119,true),(31,false),(40,false),(44,false),(48,true),(52,false),(60,true)]
theorem inputList3689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3689 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3689 (by decide) v hb
mask_input "3689|4522293472526336|664613997892457937605106509723729920"
def inputClause3690 : CNF.NClause := [(119,true),(31,true),(40,false),(44,false),(48,true),(52,false),(60,true)]
theorem inputList3690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3690 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3690 (by decide) v hb
mask_input "3690|4522291325042688|664613997892457937605106511871213568"
def inputClause3691 : CNF.NClause := [(119,true),(31,false),(40,true),(44,false),(48,true),(52,false),(60,true)]
theorem inputList3691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3691 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3691 (by decide) v hb
mask_input "3691|4521193960898560|664613997892457937605107609235357696"
def inputClause3692 : CNF.NClause := [(119,true),(31,true),(40,true),(44,false),(48,true),(52,false),(60,true)]
theorem inputList3692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3692 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3692 (by decide) v hb
mask_input "3692|4521191813414912|664613997892457937605107611382841344"
def inputClause3693 : CNF.NClause := [(119,true),(31,false),(40,false),(44,true),(48,true),(52,false),(60,true)]
theorem inputList3693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3693 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3693 (by decide) v hb
mask_input "3693|4504701286481920|664613997892457937605124101909774336"
def inputClause3694 : CNF.NClause := [(119,true),(31,true),(40,false),(44,true),(48,true),(52,false),(60,true)]
theorem inputList3694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3694 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 26) 26) (activationX_mem 26) inputClause3694 (by decide) v hb
mask_input "3694|4504699138998272|664613997892457937605124104057257984"
end Percolation.MaskChain
