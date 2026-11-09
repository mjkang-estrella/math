import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause3739 : CNF.NClause := [(120,true),(31,false),(38,true),(45,false),(47,true),(54,true),(58,false)]
theorem inputList3739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3739 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3739 (by decide) v hb
mask_input "3739|288265562671284224|1329227995784915872921962471156088832"
def inputClause3740 : CNF.NClause := [(120,true),(31,true),(38,true),(45,false),(47,true),(54,true),(58,false)]
theorem inputList3740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3740 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3740 (by decide) v hb
mask_input "3740|288265560523800576|1329227995784915872921962473303572480"
def inputClause3741 : CNF.NClause := [(120,true),(31,false),(38,false),(45,true),(47,true),(54,true),(58,false)]
theorem inputList3741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3741 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3741 (by decide) v hb
mask_input "3741|288230653177102336|1329227995784915872921997380650270720"
def inputClause3742 : CNF.NClause := [(120,true),(31,true),(38,false),(45,true),(47,true),(54,true),(58,false)]
theorem inputList3742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3742 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3742 (by decide) v hb
mask_input "3742|288230651029618688|1329227995784915872921997382797754368"
def inputClause3744 : CNF.NClause := [(120,false),(31,true),(38,true),(45,true),(47,true),(54,true),(58,false)]
theorem inputList3744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3744 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3744 (by decide) v hb
mask_input "3744|1329227995784915873192037436432056320|18190597395316736"
def inputClause3745 : CNF.NClause := [(120,true),(31,false),(38,false),(45,false),(47,false),(54,false),(58,true)]
theorem inputList3745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3745 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3745 (by decide) v hb
mask_input "3745|18190597395316736|1329227995784915873192037436432056320"
def inputClause3746 : CNF.NClause := [(120,true),(31,true),(38,false),(45,false),(47,false),(54,false),(58,true)]
theorem inputList3746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3746 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3746 (by decide) v hb
mask_input "3746|18190595247833088|1329227995784915873192037438579539968"
def inputClause3747 : CNF.NClause := [(120,true),(31,false),(38,true),(45,false),(47,false),(54,false),(58,true)]
theorem inputList3747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3747 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3747 (by decide) v hb
mask_input "3747|18190322517409792|1329227995784915873192037711309963264"
def inputClause3748 : CNF.NClause := [(120,true),(31,true),(38,true),(45,false),(47,false),(54,false),(58,true)]
theorem inputList3748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3748 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3748 (by decide) v hb
mask_input "3748|18190320369926144|1329227995784915873192037713457446912"
def inputClause3750 : CNF.NClause := [(120,true),(31,true),(38,false),(45,true),(47,false),(54,false),(58,true)]
theorem inputList3750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3750 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3750 (by decide) v hb
mask_input "3750|18155410875744256|1329227995784915873192072622951628800"
def inputClause3752 : CNF.NClause := [(120,true),(31,true),(38,true),(45,true),(47,false),(54,false),(58,true)]
theorem inputList3752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3752 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3752 (by decide) v hb
mask_input "3752|18155135997837312|1329227995784915873192072897829535744"
def inputClause3753 : CNF.NClause := [(120,true),(31,false),(38,false),(45,false),(47,true),(54,false),(58,true)]
theorem inputList3753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3753 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3753 (by decide) v hb
mask_input "3753|18049859906961408|1329227995784915873192178173920411648"
def inputClause3754 : CNF.NClause := [(120,true),(31,true),(38,false),(45,false),(47,true),(54,false),(58,true)]
theorem inputList3754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3754 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3754 (by decide) v hb
mask_input "3754|18049857759477760|1329227995784915873192178176067895296"
def inputClause3755 : CNF.NClause := [(120,true),(31,false),(38,true),(45,false),(47,true),(54,false),(58,true)]
theorem inputList3755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3755 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3755 (by decide) v hb
mask_input "3755|18049585029054464|1329227995784915873192178448798318592"
def inputClause3756 : CNF.NClause := [(120,true),(31,true),(38,true),(45,false),(47,true),(54,false),(58,true)]
theorem inputList3756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3756 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3756 (by decide) v hb
mask_input "3756|18049582881570816|1329227995784915873192178450945802240"
def inputClause3757 : CNF.NClause := [(120,true),(31,false),(38,false),(45,true),(47,true),(54,false),(58,true)]
theorem inputList3757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3757 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3757 (by decide) v hb
mask_input "3757|18014675534872576|1329227995784915873192213358292500480"
def inputClause3758 : CNF.NClause := [(120,true),(31,true),(38,false),(45,true),(47,true),(54,false),(58,true)]
theorem inputList3758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3758 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3758 (by decide) v hb
mask_input "3758|18014673387388928|1329227995784915873192213360439984128"
def inputClause3761 : CNF.NClause := [(120,true),(31,false),(38,false),(45,false),(47,false),(54,true),(58,true)]
theorem inputList3761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3761 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3761 (by decide) v hb
mask_input "3761|176198885834752|1329227995784915873210051834941538304"
def inputClause3762 : CNF.NClause := [(120,true),(31,true),(38,false),(45,false),(47,false),(54,true),(58,true)]
theorem inputList3762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3762 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3762 (by decide) v hb
mask_input "3762|176196738351104|1329227995784915873210051837089021952"
def inputClause3763 : CNF.NClause := [(120,true),(31,false),(38,true),(45,false),(47,false),(54,true),(58,true)]
theorem inputList3763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3763 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3763 (by decide) v hb
mask_input "3763|175924007927808|1329227995784915873210052109819445248"
def inputClause3764 : CNF.NClause := [(120,true),(31,true),(38,true),(45,false),(47,false),(54,true),(58,true)]
theorem inputList3764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3764 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3764 (by decide) v hb
mask_input "3764|175921860444160|1329227995784915873210052111966928896"
def inputClause3765 : CNF.NClause := [(120,true),(31,false),(38,false),(45,true),(47,false),(54,true),(58,true)]
theorem inputList3765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3765 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3765 (by decide) v hb
mask_input "3765|141014513745920|1329227995784915873210087019313627136"
def inputClause3766 : CNF.NClause := [(120,true),(31,true),(38,false),(45,true),(47,false),(54,true),(58,true)]
theorem inputList3766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3766 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3766 (by decide) v hb
mask_input "3766|141012366262272|1329227995784915873210087021461110784"
def inputClause3769 : CNF.NClause := [(120,true),(31,false),(38,false),(45,false),(47,true),(54,true),(58,true)]
theorem inputList3769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3769 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3769 (by decide) v hb
mask_input "3769|35461397479424|1329227995784915873210192572429893632"
def inputClause3770 : CNF.NClause := [(120,true),(31,true),(38,false),(45,false),(47,true),(54,true),(58,true)]
theorem inputList3770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3770 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3770 (by decide) v hb
mask_input "3770|35459249995776|1329227995784915873210192574577377280"
def inputClause3776 : CNF.NClause := [(120,false),(31,true),(38,true),(45,true),(47,true),(54,true),(58,true)]
theorem inputList3776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3776 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 27) 27) (activationX_mem 27) inputClause3776 (by decide) v hb
mask_input "3776|1329227995784915872903807060280344576|306420973547028480"
def inputClause3777 : CNF.NClause := [(121,true),(31,false),(39,false),(42,false),(50,false),(53,false),(59,false)]
theorem inputList3777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3777 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3777 (by decide) v hb
mask_input "3777|586598801414815744|2658455991569831745807614120560689152"
def inputClause3778 : CNF.NClause := [(121,true),(31,true),(39,false),(42,false),(50,false),(53,false),(59,false)]
theorem inputList3778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3778 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3778 (by decide) v hb
mask_input "3778|586598799267332096|2658455991569831745807614122708172800"
def inputClause3779 : CNF.NClause := [(121,true),(31,false),(39,true),(42,false),(50,false),(53,false),(59,false)]
theorem inputList3779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3779 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3779 (by decide) v hb
mask_input "3779|586598251659001856|2658455991569831745807614670316503040"
def inputClause3780 : CNF.NClause := [(121,true),(31,true),(39,true),(42,false),(50,false),(53,false),(59,false)]
theorem inputList3780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3780 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3780 (by decide) v hb
mask_input "3780|586598249511518208|2658455991569831745807614672463986688"
def inputClause3781 : CNF.NClause := [(121,true),(31,false),(39,false),(42,true),(50,false),(53,false),(59,false)]
theorem inputList3781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3781 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3781 (by decide) v hb
mask_input "3781|586594403368304640|2658455991569831745807618518607200256"
def inputClause3782 : CNF.NClause := [(121,true),(31,true),(39,false),(42,true),(50,false),(53,false),(59,false)]
theorem inputList3782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3782 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3782 (by decide) v hb
mask_input "3782|586594401220820992|2658455991569831745807618520754683904"
def inputClause3783 : CNF.NClause := [(121,true),(31,false),(39,true),(42,true),(50,false),(53,false),(59,false)]
theorem inputList3783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3783 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3783 (by decide) v hb
mask_input "3783|586593853612490752|2658455991569831745807619068363014144"
def inputClause3784 : CNF.NClause := [(121,true),(31,true),(39,true),(42,true),(50,false),(53,false),(59,false)]
theorem inputList3784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3784 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3784 (by decide) v hb
mask_input "3784|586593851465007104|2658455991569831745807619070510497792"
def inputClause3785 : CNF.NClause := [(121,true),(31,false),(39,false),(42,false),(50,true),(53,false),(59,false)]
theorem inputList3785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3785 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3785 (by decide) v hb
mask_input "3785|585472901507973120|2658455991569831745808740020467531776"
def inputClause3786 : CNF.NClause := [(121,true),(31,true),(39,false),(42,false),(50,true),(53,false),(59,false)]
theorem inputList3786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3786 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3786 (by decide) v hb
mask_input "3786|585472899360489472|2658455991569831745808740022615015424"
def inputClause3787 : CNF.NClause := [(121,true),(31,false),(39,true),(42,false),(50,true),(53,false),(59,false)]
theorem inputList3787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3787 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3787 (by decide) v hb
mask_input "3787|585472351752159232|2658455991569831745808740570223345664"
def inputClause3788 : CNF.NClause := [(121,true),(31,true),(39,true),(42,false),(50,true),(53,false),(59,false)]
theorem inputList3788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3788 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3788 (by decide) v hb
mask_input "3788|585472349604675584|2658455991569831745808740572370829312"
def inputClause3789 : CNF.NClause := [(121,true),(31,false),(39,false),(42,true),(50,true),(53,false),(59,false)]
theorem inputList3789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3789 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3789 (by decide) v hb
mask_input "3789|585468503461462016|2658455991569831745808744418514042880"
def inputClause3790 : CNF.NClause := [(121,true),(31,true),(39,false),(42,true),(50,true),(53,false),(59,false)]
theorem inputList3790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3790 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 28) 28) (activationX_mem 28) inputClause3790 (by decide) v hb
mask_input "3790|585468501313978368|2658455991569831745808744420661526528"
end Percolation.MaskChain
