import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause920 : CNF.NClause := [(76,true),(1,true),(8,true),(10,true),(17,false),(24,true),(27,false)]
theorem inputList920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause920 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause920 (by decide) v hb
mask_input "920|134348800|75557863725914340197634"
def inputClause921 : CNF.NClause := [(76,true),(1,false),(8,false),(10,false),(17,true),(24,true),(27,false)]
theorem inputList921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause921 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause921 (by decide) v hb
mask_input "921|134219010|75557863725914340327424"
def inputClause922 : CNF.NClause := [(76,true),(1,true),(8,false),(10,false),(17,true),(24,true),(27,false)]
theorem inputList922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause922 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause922 (by decide) v hb
mask_input "922|134219008|75557863725914340327426"
def inputClause923 : CNF.NClause := [(76,true),(1,false),(8,true),(10,false),(17,true),(24,true),(27,false)]
theorem inputList923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause923 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause923 (by decide) v hb
mask_input "923|134218754|75557863725914340327680"
def inputClause924 : CNF.NClause := [(76,true),(1,true),(8,true),(10,false),(17,true),(24,true),(27,false)]
theorem inputList924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause924 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause924 (by decide) v hb
mask_input "924|134218752|75557863725914340327682"
def inputClause925 : CNF.NClause := [(76,true),(1,false),(8,false),(10,true),(17,true),(24,true),(27,false)]
theorem inputList925 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause925 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause925 (by decide) v hb
mask_input "925|134217986|75557863725914340328448"
def inputClause926 : CNF.NClause := [(76,true),(1,true),(8,false),(10,true),(17,true),(24,true),(27,false)]
theorem inputList926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause926 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause926 (by decide) v hb
mask_input "926|134217984|75557863725914340328450"
def inputClause927 : CNF.NClause := [(76,true),(1,false),(8,true),(10,true),(17,true),(24,true),(27,false)]
theorem inputList927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause927 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause927 (by decide) v hb
mask_input "927|134217730|75557863725914340328704"
def inputClause928 : CNF.NClause := [(76,false),(1,true),(8,true),(10,true),(17,true),(24,true),(27,false)]
theorem inputList928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause928 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause928 (by decide) v hb
mask_input "928|75557863725914457636864|16909570"
def inputClause929 : CNF.NClause := [(76,true),(1,false),(8,false),(10,false),(17,false),(24,false),(27,true)]
theorem inputList929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause929 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause929 (by decide) v hb
mask_input "929|16909570|75557863725914457636864"
def inputClause930 : CNF.NClause := [(76,true),(1,true),(8,false),(10,false),(17,false),(24,false),(27,true)]
theorem inputList930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause930 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause930 (by decide) v hb
mask_input "930|16909568|75557863725914457636866"
def inputClause931 : CNF.NClause := [(76,true),(1,false),(8,true),(10,false),(17,false),(24,false),(27,true)]
theorem inputList931 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause931 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause931 (by decide) v hb
mask_input "931|16909314|75557863725914457637120"
def inputClause932 : CNF.NClause := [(76,true),(1,true),(8,true),(10,false),(17,false),(24,false),(27,true)]
theorem inputList932 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause932 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause932 (by decide) v hb
mask_input "932|16909312|75557863725914457637122"
def inputClause933 : CNF.NClause := [(76,true),(1,false),(8,false),(10,true),(17,false),(24,false),(27,true)]
theorem inputList933 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause933 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause933 (by decide) v hb
mask_input "933|16908546|75557863725914457637888"
def inputClause934 : CNF.NClause := [(76,true),(1,true),(8,false),(10,true),(17,false),(24,false),(27,true)]
theorem inputList934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause934 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause934 (by decide) v hb
mask_input "934|16908544|75557863725914457637890"
def inputClause935 : CNF.NClause := [(76,true),(1,false),(8,true),(10,true),(17,false),(24,false),(27,true)]
theorem inputList935 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause935 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause935 (by decide) v hb
mask_input "935|16908290|75557863725914457638144"
def inputClause936 : CNF.NClause := [(76,true),(1,true),(8,true),(10,true),(17,false),(24,false),(27,true)]
theorem inputList936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause936 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause936 (by decide) v hb
mask_input "936|16908288|75557863725914457638146"
def inputClause937 : CNF.NClause := [(76,true),(1,false),(8,false),(10,false),(17,true),(24,false),(27,true)]
theorem inputList937 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause937 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause937 (by decide) v hb
mask_input "937|16778498|75557863725914457767936"
def inputClause938 : CNF.NClause := [(76,true),(1,true),(8,false),(10,false),(17,true),(24,false),(27,true)]
theorem inputList938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause938 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause938 (by decide) v hb
mask_input "938|16778496|75557863725914457767938"
def inputClause939 : CNF.NClause := [(76,true),(1,false),(8,true),(10,false),(17,true),(24,false),(27,true)]
theorem inputList939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause939 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause939 (by decide) v hb
mask_input "939|16778242|75557863725914457768192"
def inputClause940 : CNF.NClause := [(76,true),(1,true),(8,true),(10,false),(17,true),(24,false),(27,true)]
theorem inputList940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause940 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause940 (by decide) v hb
mask_input "940|16778240|75557863725914457768194"
def inputClause941 : CNF.NClause := [(76,true),(1,false),(8,false),(10,true),(17,true),(24,false),(27,true)]
theorem inputList941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause941 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause941 (by decide) v hb
mask_input "941|16777474|75557863725914457768960"
def inputClause942 : CNF.NClause := [(76,true),(1,true),(8,false),(10,true),(17,true),(24,false),(27,true)]
theorem inputList942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause942 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause942 (by decide) v hb
mask_input "942|16777472|75557863725914457768962"
def inputClause943 : CNF.NClause := [(76,true),(1,false),(8,true),(10,true),(17,true),(24,false),(27,true)]
theorem inputList943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause943 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause943 (by decide) v hb
mask_input "943|16777218|75557863725914457769216"
def inputClause945 : CNF.NClause := [(76,true),(1,false),(8,false),(10,false),(17,false),(24,true),(27,true)]
theorem inputList945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause945 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause945 (by decide) v hb
mask_input "945|132354|75557863725914474414080"
def inputClause946 : CNF.NClause := [(76,true),(1,true),(8,false),(10,false),(17,false),(24,true),(27,true)]
theorem inputList946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause946 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause946 (by decide) v hb
mask_input "946|132352|75557863725914474414082"
def inputClause947 : CNF.NClause := [(76,true),(1,false),(8,true),(10,false),(17,false),(24,true),(27,true)]
theorem inputList947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause947 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause947 (by decide) v hb
mask_input "947|132098|75557863725914474414336"
def inputClause948 : CNF.NClause := [(76,true),(1,true),(8,true),(10,false),(17,false),(24,true),(27,true)]
theorem inputList948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause948 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause948 (by decide) v hb
mask_input "948|132096|75557863725914474414338"
def inputClause949 : CNF.NClause := [(76,true),(1,false),(8,false),(10,true),(17,false),(24,true),(27,true)]
theorem inputList949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause949 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause949 (by decide) v hb
mask_input "949|131330|75557863725914474415104"
def inputClause950 : CNF.NClause := [(76,true),(1,true),(8,false),(10,true),(17,false),(24,true),(27,true)]
theorem inputList950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause950 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause950 (by decide) v hb
mask_input "950|131328|75557863725914474415106"
def inputClause951 : CNF.NClause := [(76,true),(1,false),(8,true),(10,true),(17,false),(24,true),(27,true)]
theorem inputList951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause951 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause951 (by decide) v hb
mask_input "951|131074|75557863725914474415360"
def inputClause953 : CNF.NClause := [(76,true),(1,false),(8,false),(10,false),(17,true),(24,true),(27,true)]
theorem inputList953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause953 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause953 (by decide) v hb
mask_input "953|1282|75557863725914474545152"
def inputClause954 : CNF.NClause := [(76,true),(1,true),(8,false),(10,false),(17,true),(24,true),(27,true)]
theorem inputList954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause954 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause954 (by decide) v hb
mask_input "954|1280|75557863725914474545154"
def inputClause955 : CNF.NClause := [(76,true),(1,false),(8,true),(10,false),(17,true),(24,true),(27,true)]
theorem inputList955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause955 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause955 (by decide) v hb
mask_input "955|1026|75557863725914474545408"
def inputClause957 : CNF.NClause := [(76,true),(1,false),(8,false),(10,true),(17,true),(24,true),(27,true)]
theorem inputList957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause957 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause957 (by decide) v hb
mask_input "957|258|75557863725914474546176"
def inputClause960 : CNF.NClause := [(76,false),(1,true),(8,true),(10,true),(17,true),(24,true),(27,true)]
theorem inputList960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause960 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause960 (by decide) v hb
mask_input "960|75557863725914323419136|151127298"
def inputClause993 : CNF.NClause := [(77,true),(15,false),(16,false),(17,false),(18,false),(19,false),(30,true)]
theorem inputList993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause993 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) inputClause993 (by decide) v hb
mask_input "993|1015808|151115727451829720580096"
def inputClause994 : CNF.NClause := [(77,true),(15,true),(16,false),(17,false),(18,false),(19,false),(30,true)]
theorem inputList994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause994 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) inputClause994 (by decide) v hb
mask_input "994|983040|151115727451829720612864"
def inputClause995 : CNF.NClause := [(77,true),(15,false),(16,true),(17,false),(18,false),(19,false),(30,true)]
theorem inputList995 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause995 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) inputClause995 (by decide) v hb
mask_input "995|950272|151115727451829720645632"
def inputClause996 : CNF.NClause := [(77,true),(15,true),(16,true),(17,false),(18,false),(19,false),(30,true)]
theorem inputList996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause996 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 15) 15) (activationA_mem 15) inputClause996 (by decide) v hb
mask_input "996|917504|151115727451829720678400"
end Percolation.MaskChain
