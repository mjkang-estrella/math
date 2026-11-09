import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause2856 : CNF.NClause := [(106,true),(34,true),(40,true),(41,true),(47,false),(53,false),(57,true)]
theorem inputList2856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2856 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2856 (by decide) v hb
mask_input "2856|9147936743096320|81129638414606825814292795752448"
def inputClause2857 : CNF.NClause := [(106,true),(34,false),(40,false),(41,false),(47,true),(53,false),(57,true)]
theorem inputList2857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2857 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2857 (by decide) v hb
mask_input "2857|9010514969493504|81129638414606825951714569355264"
def inputClause2858 : CNF.NClause := [(106,true),(34,true),(40,false),(41,false),(47,true),(53,false),(57,true)]
theorem inputList2858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2858 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2858 (by decide) v hb
mask_input "2858|9010497789624320|81129638414606825951731749224448"
def inputClause2859 : CNF.NClause := [(106,true),(34,false),(40,true),(41,false),(47,true),(53,false),(57,true)]
theorem inputList2859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2859 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2859 (by decide) v hb
mask_input "2859|9009415457865728|81129638414606825952814080983040"
def inputClause2860 : CNF.NClause := [(106,true),(34,true),(40,true),(41,false),(47,true),(53,false),(57,true)]
theorem inputList2860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2860 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2860 (by decide) v hb
mask_input "2860|9009398277996544|81129638414606825952831260852224"
def inputClause2861 : CNF.NClause := [(106,true),(34,false),(40,false),(41,true),(47,true),(53,false),(57,true)]
theorem inputList2861 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2861 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2861 (by decide) v hb
mask_input "2861|9008315946237952|81129638414606825953913592610816"
def inputClause2862 : CNF.NClause := [(106,true),(34,true),(40,false),(41,true),(47,true),(53,false),(57,true)]
theorem inputList2862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2862 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2862 (by decide) v hb
mask_input "2862|9008298766368768|81129638414606825953930772480000"
def inputClause2863 : CNF.NClause := [(106,true),(34,false),(40,true),(41,true),(47,true),(53,false),(57,true)]
theorem inputList2863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2863 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2863 (by decide) v hb
mask_input "2863|9007216434610176|81129638414606825955013104238592"
def inputClause2865 : CNF.NClause := [(106,true),(34,false),(40,false),(41,false),(47,false),(53,true),(57,true)]
theorem inputList2865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2865 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2865 (by decide) v hb
mask_input "2865|144053203107840|81129638414606834818176335740928"
def inputClause2866 : CNF.NClause := [(106,true),(34,true),(40,false),(41,false),(47,false),(53,true),(57,true)]
theorem inputList2866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2866 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2866 (by decide) v hb
mask_input "2866|144036023238656|81129638414606834818193515610112"
def inputClause2867 : CNF.NClause := [(106,true),(34,false),(40,true),(41,false),(47,false),(53,true),(57,true)]
theorem inputList2867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2867 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2867 (by decide) v hb
mask_input "2867|142953691480064|81129638414606834819275847368704"
def inputClause2868 : CNF.NClause := [(106,true),(34,true),(40,true),(41,false),(47,false),(53,true),(57,true)]
theorem inputList2868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2868 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2868 (by decide) v hb
mask_input "2868|142936511610880|81129638414606834819293027237888"
def inputClause2869 : CNF.NClause := [(106,true),(34,false),(40,false),(41,true),(47,false),(53,true),(57,true)]
theorem inputList2869 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2869 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2869 (by decide) v hb
mask_input "2869|141854179852288|81129638414606834820375358996480"
def inputClause2870 : CNF.NClause := [(106,true),(34,true),(40,false),(41,true),(47,false),(53,true),(57,true)]
theorem inputList2870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2870 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2870 (by decide) v hb
mask_input "2870|141836999983104|81129638414606834820392538865664"
def inputClause2871 : CNF.NClause := [(106,true),(34,false),(40,true),(41,true),(47,false),(53,true),(57,true)]
theorem inputList2871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2871 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2871 (by decide) v hb
mask_input "2871|140754668224512|81129638414606834821474870624256"
def inputClause2873 : CNF.NClause := [(106,true),(34,false),(40,false),(41,false),(47,true),(53,true),(57,true)]
theorem inputList2873 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2873 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2873 (by decide) v hb
mask_input "2873|3315714752512|81129638414606834958913824096256"
def inputClause2874 : CNF.NClause := [(106,true),(34,true),(40,false),(41,false),(47,true),(53,true),(57,true)]
theorem inputList2874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2874 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2874 (by decide) v hb
mask_input "2874|3298534883328|81129638414606834958931003965440"
def inputClause2875 : CNF.NClause := [(106,true),(34,false),(40,true),(41,false),(47,true),(53,true),(57,true)]
theorem inputList2875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2875 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2875 (by decide) v hb
mask_input "2875|2216203124736|81129638414606834960013335724032"
def inputClause2877 : CNF.NClause := [(106,true),(34,false),(40,false),(41,true),(47,true),(53,true),(57,true)]
theorem inputList2877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2877 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2877 (by decide) v hb
mask_input "2877|1116691496960|81129638414606834961112847351808"
def inputClause2880 : CNF.NClause := [(106,false),(34,true),(40,true),(41,true),(47,true),(53,true),(57,true)]
theorem inputList2880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2880 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2880 (by decide) v hb
mask_input "2880|81129638414606681695789005144064|153266440533704704"
def inputClause2881 : CNF.NClause := [(107,true),(32,false),(39,false),(41,false),(48,false),(55,false),(58,false)]
theorem inputList2881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2881 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2881 (by decide) v hb
mask_input "2881|324543401221423104|162259276829213363391578010288128"
def inputClause2882 : CNF.NClause := [(107,true),(32,true),(39,false),(41,false),(48,false),(55,false),(58,false)]
theorem inputList2882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2882 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2882 (by decide) v hb
mask_input "2882|324543396926455808|162259276829213363391582305255424"
def inputClause2883 : CNF.NClause := [(107,true),(32,false),(39,true),(41,false),(48,false),(55,false),(58,false)]
theorem inputList2883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2883 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2883 (by decide) v hb
mask_input "2883|324542851465609216|162259276829213363392127766102016"
def inputClause2884 : CNF.NClause := [(107,true),(32,true),(39,true),(41,false),(48,false),(55,false),(58,false)]
theorem inputList2884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2884 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2884 (by decide) v hb
mask_input "2884|324542847170641920|162259276829213363392132061069312"
def inputClause2885 : CNF.NClause := [(107,true),(32,false),(39,false),(41,true),(48,false),(55,false),(58,false)]
theorem inputList2885 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2885 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2885 (by decide) v hb
mask_input "2885|324541202198167552|162259276829213363393777033543680"
def inputClause2886 : CNF.NClause := [(107,true),(32,true),(39,false),(41,true),(48,false),(55,false),(58,false)]
theorem inputList2886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2886 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2886 (by decide) v hb
mask_input "2886|324541197903200256|162259276829213363393781328510976"
def inputClause2887 : CNF.NClause := [(107,true),(32,false),(39,true),(41,true),(48,false),(55,false),(58,false)]
theorem inputList2887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2887 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2887 (by decide) v hb
mask_input "2887|324540652442353664|162259276829213363394326789357568"
def inputClause2888 : CNF.NClause := [(107,true),(32,true),(39,true),(41,true),(48,false),(55,false),(58,false)]
theorem inputList2888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2888 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2888 (by decide) v hb
mask_input "2888|324540648147386368|162259276829213363394331084324864"
def inputClause2889 : CNF.NClause := [(107,true),(32,false),(39,false),(41,false),(48,true),(55,false),(58,false)]
theorem inputList2889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2889 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2889 (by decide) v hb
mask_input "2889|324261926244712448|162259276829213363673052986998784"
def inputClause2890 : CNF.NClause := [(107,true),(32,true),(39,false),(41,false),(48,true),(55,false),(58,false)]
theorem inputList2890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2890 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2890 (by decide) v hb
mask_input "2890|324261921949745152|162259276829213363673057281966080"
def inputClause2891 : CNF.NClause := [(107,true),(32,false),(39,true),(41,false),(48,true),(55,false),(58,false)]
theorem inputList2891 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2891 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2891 (by decide) v hb
mask_input "2891|324261376488898560|162259276829213363673602742812672"
def inputClause2892 : CNF.NClause := [(107,true),(32,true),(39,true),(41,false),(48,true),(55,false),(58,false)]
theorem inputList2892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2892 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2892 (by decide) v hb
mask_input "2892|324261372193931264|162259276829213363673607037779968"
def inputClause2893 : CNF.NClause := [(107,true),(32,false),(39,false),(41,true),(48,true),(55,false),(58,false)]
theorem inputList2893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2893 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2893 (by decide) v hb
mask_input "2893|324259727221456896|162259276829213363675252010254336"
def inputClause2894 : CNF.NClause := [(107,true),(32,true),(39,false),(41,true),(48,true),(55,false),(58,false)]
theorem inputList2894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2894 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2894 (by decide) v hb
mask_input "2894|324259722926489600|162259276829213363675256305221632"
def inputClause2895 : CNF.NClause := [(107,true),(32,false),(39,true),(41,true),(48,true),(55,false),(58,false)]
theorem inputList2895 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2895 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2895 (by decide) v hb
mask_input "2895|324259177465643008|162259276829213363675801766068224"
def inputClause2896 : CNF.NClause := [(107,true),(32,true),(39,true),(41,true),(48,true),(55,false),(58,false)]
theorem inputList2896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2896 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2896 (by decide) v hb
mask_input "2896|324259173170675712|162259276829213363675806061035520"
def inputClause2897 : CNF.NClause := [(107,true),(32,false),(39,false),(41,false),(48,false),(55,true),(58,false)]
theorem inputList2897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2897 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2897 (by decide) v hb
mask_input "2897|288514604202459136|162259276829213399420375029252096"
def inputClause2898 : CNF.NClause := [(107,true),(32,true),(39,false),(41,false),(48,false),(55,true),(58,false)]
theorem inputList2898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2898 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2898 (by decide) v hb
mask_input "2898|288514599907491840|162259276829213399420379324219392"
def inputClause2899 : CNF.NClause := [(107,true),(32,false),(39,true),(41,false),(48,false),(55,true),(58,false)]
theorem inputList2899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2899 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2899 (by decide) v hb
mask_input "2899|288514054446645248|162259276829213399420924785065984"
def inputClause2900 : CNF.NClause := [(107,true),(32,true),(39,true),(41,false),(48,false),(55,true),(58,false)]
theorem inputList2900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2900 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2900 (by decide) v hb
mask_input "2900|288514050151677952|162259276829213399420929080033280"
end Percolation.MaskChain
