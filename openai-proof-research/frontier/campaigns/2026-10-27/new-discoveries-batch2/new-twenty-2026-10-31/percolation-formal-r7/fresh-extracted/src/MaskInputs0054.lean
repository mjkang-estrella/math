import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause2901 : CNF.NClause := [(107,true),(32,false),(39,false),(41,true),(48,false),(55,true),(58,false)]
theorem inputList2901 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2901 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2901 (by decide) v hb
mask_input "2901|288512405179203584|162259276829213399422574052507648"
def inputClause2902 : CNF.NClause := [(107,true),(32,true),(39,false),(41,true),(48,false),(55,true),(58,false)]
theorem inputList2902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2902 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2902 (by decide) v hb
mask_input "2902|288512400884236288|162259276829213399422578347474944"
def inputClause2903 : CNF.NClause := [(107,true),(32,false),(39,true),(41,true),(48,false),(55,true),(58,false)]
theorem inputList2903 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2903 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2903 (by decide) v hb
mask_input "2903|288511855423389696|162259276829213399423123808321536"
def inputClause2904 : CNF.NClause := [(107,true),(32,true),(39,true),(41,true),(48,false),(55,true),(58,false)]
theorem inputList2904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2904 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2904 (by decide) v hb
mask_input "2904|288511851128422400|162259276829213399423128103288832"
def inputClause2905 : CNF.NClause := [(107,true),(32,false),(39,false),(41,false),(48,true),(55,true),(58,false)]
theorem inputList2905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2905 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2905 (by decide) v hb
mask_input "2905|288233129225748480|162259276829213399701850005962752"
def inputClause2906 : CNF.NClause := [(107,true),(32,true),(39,false),(41,false),(48,true),(55,true),(58,false)]
theorem inputList2906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2906 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2906 (by decide) v hb
mask_input "2906|288233124930781184|162259276829213399701854300930048"
def inputClause2907 : CNF.NClause := [(107,true),(32,false),(39,true),(41,false),(48,true),(55,true),(58,false)]
theorem inputList2907 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2907 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2907 (by decide) v hb
mask_input "2907|288232579469934592|162259276829213399702399761776640"
def inputClause2908 : CNF.NClause := [(107,true),(32,true),(39,true),(41,false),(48,true),(55,true),(58,false)]
theorem inputList2908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2908 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2908 (by decide) v hb
mask_input "2908|288232575174967296|162259276829213399702404056743936"
def inputClause2909 : CNF.NClause := [(107,true),(32,false),(39,false),(41,true),(48,true),(55,true),(58,false)]
theorem inputList2909 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2909 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2909 (by decide) v hb
mask_input "2909|288230930202492928|162259276829213399704049029218304"
def inputClause2910 : CNF.NClause := [(107,true),(32,true),(39,false),(41,true),(48,true),(55,true),(58,false)]
theorem inputList2910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2910 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2910 (by decide) v hb
mask_input "2910|288230925907525632|162259276829213399704053324185600"
def inputClause2911 : CNF.NClause := [(107,true),(32,false),(39,true),(41,true),(48,true),(55,true),(58,false)]
theorem inputList2911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2911 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2911 (by decide) v hb
mask_input "2911|288230380446679040|162259276829213399704598785032192"
def inputClause2912 : CNF.NClause := [(107,false),(32,true),(39,true),(41,true),(48,true),(55,true),(58,false)]
theorem inputList2912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2912 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2912 (by decide) v hb
mask_input "2912|162259276829213651621954161999872|36313025069711360"
def inputClause2913 : CNF.NClause := [(107,true),(32,false),(39,false),(41,false),(48,false),(55,false),(58,true)]
theorem inputList2913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2913 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2913 (by decide) v hb
mask_input "2913|36313025069711360|162259276829213651621954161999872"
def inputClause2914 : CNF.NClause := [(107,true),(32,true),(39,false),(41,false),(48,false),(55,false),(58,true)]
theorem inputList2914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2914 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2914 (by decide) v hb
mask_input "2914|36313020774744064|162259276829213651621958456967168"
def inputClause2915 : CNF.NClause := [(107,true),(32,false),(39,true),(41,false),(48,false),(55,false),(58,true)]
theorem inputList2915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2915 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2915 (by decide) v hb
mask_input "2915|36312475313897472|162259276829213651622503917813760"
def inputClause2916 : CNF.NClause := [(107,true),(32,true),(39,true),(41,false),(48,false),(55,false),(58,true)]
theorem inputList2916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2916 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2916 (by decide) v hb
mask_input "2916|36312471018930176|162259276829213651622508212781056"
def inputClause2917 : CNF.NClause := [(107,true),(32,false),(39,false),(41,true),(48,false),(55,false),(58,true)]
theorem inputList2917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2917 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2917 (by decide) v hb
mask_input "2917|36310826046455808|162259276829213651624153185255424"
def inputClause2918 : CNF.NClause := [(107,true),(32,true),(39,false),(41,true),(48,false),(55,false),(58,true)]
theorem inputList2918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2918 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2918 (by decide) v hb
mask_input "2918|36310821751488512|162259276829213651624157480222720"
def inputClause2919 : CNF.NClause := [(107,true),(32,false),(39,true),(41,true),(48,false),(55,false),(58,true)]
theorem inputList2919 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2919 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2919 (by decide) v hb
mask_input "2919|36310276290641920|162259276829213651624702941069312"
def inputClause2920 : CNF.NClause := [(107,true),(32,true),(39,true),(41,true),(48,false),(55,false),(58,true)]
theorem inputList2920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2920 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2920 (by decide) v hb
mask_input "2920|36310271995674624|162259276829213651624707236036608"
def inputClause2921 : CNF.NClause := [(107,true),(32,false),(39,false),(41,false),(48,true),(55,false),(58,true)]
theorem inputList2921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2921 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2921 (by decide) v hb
mask_input "2921|36031550093000704|162259276829213651903429138710528"
def inputClause2922 : CNF.NClause := [(107,true),(32,true),(39,false),(41,false),(48,true),(55,false),(58,true)]
theorem inputList2922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2922 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2922 (by decide) v hb
mask_input "2922|36031545798033408|162259276829213651903433433677824"
def inputClause2923 : CNF.NClause := [(107,true),(32,false),(39,true),(41,false),(48,true),(55,false),(58,true)]
theorem inputList2923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2923 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2923 (by decide) v hb
mask_input "2923|36031000337186816|162259276829213651903978894524416"
def inputClause2924 : CNF.NClause := [(107,true),(32,true),(39,true),(41,false),(48,true),(55,false),(58,true)]
theorem inputList2924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2924 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2924 (by decide) v hb
mask_input "2924|36030996042219520|162259276829213651903983189491712"
def inputClause2925 : CNF.NClause := [(107,true),(32,false),(39,false),(41,true),(48,true),(55,false),(58,true)]
theorem inputList2925 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2925 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2925 (by decide) v hb
mask_input "2925|36029351069745152|162259276829213651905628161966080"
def inputClause2926 : CNF.NClause := [(107,true),(32,true),(39,false),(41,true),(48,true),(55,false),(58,true)]
theorem inputList2926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2926 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2926 (by decide) v hb
mask_input "2926|36029346774777856|162259276829213651905632456933376"
def inputClause2927 : CNF.NClause := [(107,true),(32,false),(39,true),(41,true),(48,true),(55,false),(58,true)]
theorem inputList2927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2927 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2927 (by decide) v hb
mask_input "2927|36028801313931264|162259276829213651906177917779968"
def inputClause2929 : CNF.NClause := [(107,true),(32,false),(39,false),(41,false),(48,false),(55,true),(58,true)]
theorem inputList2929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2929 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2929 (by decide) v hb
mask_input "2929|284228050747392|162259276829213687650751180963840"
def inputClause2930 : CNF.NClause := [(107,true),(32,true),(39,false),(41,false),(48,false),(55,true),(58,true)]
theorem inputList2930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2930 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2930 (by decide) v hb
mask_input "2930|284223755780096|162259276829213687650755475931136"
def inputClause2931 : CNF.NClause := [(107,true),(32,false),(39,true),(41,false),(48,false),(55,true),(58,true)]
theorem inputList2931 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2931 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2931 (by decide) v hb
mask_input "2931|283678294933504|162259276829213687651300936777728"
def inputClause2932 : CNF.NClause := [(107,true),(32,true),(39,true),(41,false),(48,false),(55,true),(58,true)]
theorem inputList2932 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2932 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2932 (by decide) v hb
mask_input "2932|283673999966208|162259276829213687651305231745024"
def inputClause2933 : CNF.NClause := [(107,true),(32,false),(39,false),(41,true),(48,false),(55,true),(58,true)]
theorem inputList2933 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2933 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2933 (by decide) v hb
mask_input "2933|282029027491840|162259276829213687652950204219392"
def inputClause2934 : CNF.NClause := [(107,true),(32,true),(39,false),(41,true),(48,false),(55,true),(58,true)]
theorem inputList2934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2934 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2934 (by decide) v hb
mask_input "2934|282024732524544|162259276829213687652954499186688"
def inputClause2935 : CNF.NClause := [(107,true),(32,false),(39,true),(41,true),(48,false),(55,true),(58,true)]
theorem inputList2935 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2935 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2935 (by decide) v hb
mask_input "2935|281479271677952|162259276829213687653499960033280"
def inputClause2937 : CNF.NClause := [(107,true),(32,false),(39,false),(41,false),(48,true),(55,true),(58,true)]
theorem inputList2937 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2937 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2937 (by decide) v hb
mask_input "2937|2753074036736|162259276829213687932226157674496"
def inputClause2938 : CNF.NClause := [(107,true),(32,true),(39,false),(41,false),(48,true),(55,true),(58,true)]
theorem inputList2938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2938 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2938 (by decide) v hb
mask_input "2938|2748779069440|162259276829213687932230452641792"
def inputClause2939 : CNF.NClause := [(107,true),(32,false),(39,true),(41,false),(48,true),(55,true),(58,true)]
theorem inputList2939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2939 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2939 (by decide) v hb
mask_input "2939|2203318222848|162259276829213687932775913488384"
def inputClause2941 : CNF.NClause := [(107,true),(32,false),(39,false),(41,true),(48,true),(55,true),(58,true)]
theorem inputList2941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2941 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2941 (by decide) v hb
mask_input "2941|554050781184|162259276829213687934425180930048"
def inputClause2944 : CNF.NClause := [(107,false),(32,true),(39,true),(41,true),(48,true),(55,true),(58,true)]
theorem inputList2944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2944 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) inputClause2944 (by decide) v hb
mask_input "2944|162259276829213363391578010288128|324543401221423104"
def inputClause2945 : CNF.NClause := [(108,true),(46,false),(47,false),(48,false),(49,false),(50,false),(61,false)]
theorem inputList2945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2945 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) inputClause2945 (by decide) v hb
mask_input "2945|2308024440283201536|324518553658426726783156020576256"
end Percolation.MaskChain
