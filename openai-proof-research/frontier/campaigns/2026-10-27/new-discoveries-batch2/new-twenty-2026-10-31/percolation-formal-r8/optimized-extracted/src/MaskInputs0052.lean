import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause2816 : CNF.NClause := [(105,false),(33,true),(37,true),(41,true),(50,true),(54,true),(60,true)]
theorem inputList2816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2816 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) inputClause2816 (by decide) v hb
mask_input "2816|40564819207303340847894502572032|1172064148075315200"
def inputClause2817 : CNF.NClause := [(106,true),(34,false),(40,false),(41,false),(47,false),(53,false),(57,false)]
theorem inputList2817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2817 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2817 (by decide) v hb
mask_input "2817|153266440533704704|81129638414606681695789005144064"
def inputClause2818 : CNF.NClause := [(106,true),(34,true),(40,false),(41,false),(47,false),(53,false),(57,false)]
theorem inputList2818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2818 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2818 (by decide) v hb
mask_input "2818|153266423353835520|81129638414606681695806185013248"
def inputClause2819 : CNF.NClause := [(106,true),(34,false),(40,true),(41,false),(47,false),(53,false),(57,false)]
theorem inputList2819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2819 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2819 (by decide) v hb
mask_input "2819|153265341022076928|81129638414606681696888516771840"
def inputClause2820 : CNF.NClause := [(106,true),(34,true),(40,true),(41,false),(47,false),(53,false),(57,false)]
theorem inputList2820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2820 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2820 (by decide) v hb
mask_input "2820|153265323842207744|81129638414606681696905696641024"
def inputClause2821 : CNF.NClause := [(106,true),(34,false),(40,false),(41,true),(47,false),(53,false),(57,false)]
theorem inputList2821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2821 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2821 (by decide) v hb
mask_input "2821|153264241510449152|81129638414606681697988028399616"
def inputClause2822 : CNF.NClause := [(106,true),(34,true),(40,false),(41,true),(47,false),(53,false),(57,false)]
theorem inputList2822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2822 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2822 (by decide) v hb
mask_input "2822|153264224330579968|81129638414606681698005208268800"
def inputClause2823 : CNF.NClause := [(106,true),(34,false),(40,true),(41,true),(47,false),(53,false),(57,false)]
theorem inputList2823 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2823 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2823 (by decide) v hb
mask_input "2823|153263141998821376|81129638414606681699087540027392"
def inputClause2824 : CNF.NClause := [(106,true),(34,true),(40,true),(41,true),(47,false),(53,false),(57,false)]
theorem inputList2824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2824 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2824 (by decide) v hb
mask_input "2824|153263124818952192|81129638414606681699104719896576"
def inputClause2825 : CNF.NClause := [(106,true),(34,false),(40,false),(41,false),(47,true),(53,false),(57,false)]
theorem inputList2825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2825 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2825 (by decide) v hb
mask_input "2825|153125703045349376|81129638414606681836526493499392"
def inputClause2826 : CNF.NClause := [(106,true),(34,true),(40,false),(41,false),(47,true),(53,false),(57,false)]
theorem inputList2826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2826 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2826 (by decide) v hb
mask_input "2826|153125685865480192|81129638414606681836543673368576"
def inputClause2827 : CNF.NClause := [(106,true),(34,false),(40,true),(41,false),(47,true),(53,false),(57,false)]
theorem inputList2827 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2827 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2827 (by decide) v hb
mask_input "2827|153124603533721600|81129638414606681837626005127168"
def inputClause2828 : CNF.NClause := [(106,true),(34,true),(40,true),(41,false),(47,true),(53,false),(57,false)]
theorem inputList2828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2828 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2828 (by decide) v hb
mask_input "2828|153124586353852416|81129638414606681837643184996352"
def inputClause2829 : CNF.NClause := [(106,true),(34,false),(40,false),(41,true),(47,true),(53,false),(57,false)]
theorem inputList2829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2829 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2829 (by decide) v hb
mask_input "2829|153123504022093824|81129638414606681838725516754944"
def inputClause2830 : CNF.NClause := [(106,true),(34,true),(40,false),(41,true),(47,true),(53,false),(57,false)]
theorem inputList2830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2830 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2830 (by decide) v hb
mask_input "2830|153123486842224640|81129638414606681838742696624128"
def inputClause2831 : CNF.NClause := [(106,true),(34,false),(40,true),(41,true),(47,true),(53,false),(57,false)]
theorem inputList2831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2831 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2831 (by decide) v hb
mask_input "2831|153122404510466048|81129638414606681839825028382720"
def inputClause2832 : CNF.NClause := [(106,true),(34,true),(40,true),(41,true),(47,true),(53,false),(57,false)]
theorem inputList2832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2832 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2832 (by decide) v hb
mask_input "2832|153122387330596864|81129638414606681839842208251904"
def inputClause2833 : CNF.NClause := [(106,true),(34,false),(40,false),(41,false),(47,false),(53,true),(57,false)]
theorem inputList2833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2833 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2833 (by decide) v hb
mask_input "2833|144259241278963712|81129638414606690702988259885056"
def inputClause2834 : CNF.NClause := [(106,true),(34,true),(40,false),(41,false),(47,false),(53,true),(57,false)]
theorem inputList2834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2834 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2834 (by decide) v hb
mask_input "2834|144259224099094528|81129638414606690703005439754240"
def inputClause2835 : CNF.NClause := [(106,true),(34,false),(40,true),(41,false),(47,false),(53,true),(57,false)]
theorem inputList2835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2835 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2835 (by decide) v hb
mask_input "2835|144258141767335936|81129638414606690704087771512832"
def inputClause2836 : CNF.NClause := [(106,true),(34,true),(40,true),(41,false),(47,false),(53,true),(57,false)]
theorem inputList2836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2836 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2836 (by decide) v hb
mask_input "2836|144258124587466752|81129638414606690704104951382016"
def inputClause2837 : CNF.NClause := [(106,true),(34,false),(40,false),(41,true),(47,false),(53,true),(57,false)]
theorem inputList2837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2837 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2837 (by decide) v hb
mask_input "2837|144257042255708160|81129638414606690705187283140608"
def inputClause2838 : CNF.NClause := [(106,true),(34,true),(40,false),(41,true),(47,false),(53,true),(57,false)]
theorem inputList2838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2838 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2838 (by decide) v hb
mask_input "2838|144257025075838976|81129638414606690705204463009792"
def inputClause2839 : CNF.NClause := [(106,true),(34,false),(40,true),(41,true),(47,false),(53,true),(57,false)]
theorem inputList2839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2839 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2839 (by decide) v hb
mask_input "2839|144255942744080384|81129638414606690706286794768384"
def inputClause2840 : CNF.NClause := [(106,true),(34,true),(40,true),(41,true),(47,false),(53,true),(57,false)]
theorem inputList2840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2840 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2840 (by decide) v hb
mask_input "2840|144255925564211200|81129638414606690706303974637568"
def inputClause2841 : CNF.NClause := [(106,true),(34,false),(40,false),(41,false),(47,true),(53,true),(57,false)]
theorem inputList2841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2841 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2841 (by decide) v hb
mask_input "2841|144118503790608384|81129638414606690843725748240384"
def inputClause2842 : CNF.NClause := [(106,true),(34,true),(40,false),(41,false),(47,true),(53,true),(57,false)]
theorem inputList2842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2842 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2842 (by decide) v hb
mask_input "2842|144118486610739200|81129638414606690843742928109568"
def inputClause2843 : CNF.NClause := [(106,true),(34,false),(40,true),(41,false),(47,true),(53,true),(57,false)]
theorem inputList2843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2843 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2843 (by decide) v hb
mask_input "2843|144117404278980608|81129638414606690844825259868160"
def inputClause2844 : CNF.NClause := [(106,true),(34,true),(40,true),(41,false),(47,true),(53,true),(57,false)]
theorem inputList2844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2844 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2844 (by decide) v hb
mask_input "2844|144117387099111424|81129638414606690844842439737344"
def inputClause2845 : CNF.NClause := [(106,true),(34,false),(40,false),(41,true),(47,true),(53,true),(57,false)]
theorem inputList2845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2845 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2845 (by decide) v hb
mask_input "2845|144116304767352832|81129638414606690845924771495936"
def inputClause2846 : CNF.NClause := [(106,true),(34,true),(40,false),(41,true),(47,true),(53,true),(57,false)]
theorem inputList2846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2846 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2846 (by decide) v hb
mask_input "2846|144116287587483648|81129638414606690845941951365120"
def inputClause2847 : CNF.NClause := [(106,true),(34,false),(40,true),(41,true),(47,true),(53,true),(57,false)]
theorem inputList2847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2847 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2847 (by decide) v hb
mask_input "2847|144115205255725056|81129638414606690847024283123712"
def inputClause2848 : CNF.NClause := [(106,false),(34,true),(40,true),(41,true),(47,true),(53,true),(57,false)]
theorem inputList2848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2848 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2848 (by decide) v hb
mask_input "2848|81129638414606825810977080999936|9151252457848832"
def inputClause2849 : CNF.NClause := [(106,true),(34,false),(40,false),(41,false),(47,false),(53,false),(57,true)]
theorem inputList2849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2849 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2849 (by decide) v hb
mask_input "2849|9151252457848832|81129638414606825810977080999936"
def inputClause2850 : CNF.NClause := [(106,true),(34,true),(40,false),(41,false),(47,false),(53,false),(57,true)]
theorem inputList2850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2850 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2850 (by decide) v hb
mask_input "2850|9151235277979648|81129638414606825810994260869120"
def inputClause2851 : CNF.NClause := [(106,true),(34,false),(40,true),(41,false),(47,false),(53,false),(57,true)]
theorem inputList2851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2851 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2851 (by decide) v hb
mask_input "2851|9150152946221056|81129638414606825812076592627712"
def inputClause2852 : CNF.NClause := [(106,true),(34,true),(40,true),(41,false),(47,false),(53,false),(57,true)]
theorem inputList2852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2852 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2852 (by decide) v hb
mask_input "2852|9150135766351872|81129638414606825812093772496896"
def inputClause2853 : CNF.NClause := [(106,true),(34,false),(40,false),(41,true),(47,false),(53,false),(57,true)]
theorem inputList2853 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2853 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2853 (by decide) v hb
mask_input "2853|9149053434593280|81129638414606825813176104255488"
def inputClause2854 : CNF.NClause := [(106,true),(34,true),(40,false),(41,true),(47,false),(53,false),(57,true)]
theorem inputList2854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2854 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2854 (by decide) v hb
mask_input "2854|9149036254724096|81129638414606825813193284124672"
def inputClause2855 : CNF.NClause := [(106,true),(34,false),(40,true),(41,true),(47,false),(53,false),(57,true)]
theorem inputList2855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2855 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) inputClause2855 (by decide) v hb
mask_input "2855|9147953922965504|81129638414606825814275615883264"
end Percolation.MaskChain
