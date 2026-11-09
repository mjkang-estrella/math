import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause4899 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,false),(80,false),(82,true),(89,false)]
theorem inputList4899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4899 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4899 (by decide) v hb
mask_input "4899|620190751378512215615209600|4835721725202590408376320"
def inputClause4900 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,false),(80,false),(82,true),(89,false)]
theorem inputList4900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4900 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4900 (by decide) v hb
mask_input "4900|620190751378512215615209472|4835721725202590408376448"
def inputClause4901 : CNF.NClause := [(38,false),(7,false),(64,false),(71,true),(73,false),(80,false),(82,true),(89,false)]
theorem inputList4901 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4901 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4901 (by decide) v hb
mask_input "4901|620188408642014854502154368|4838064461699951521431552"
def inputClause4902 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,false),(80,false),(82,true),(89,false)]
theorem inputList4902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4902 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4902 (by decide) v hb
mask_input "4902|620188408642014854502154240|4838064461699951521431680"
def inputClause4903 : CNF.NClause := [(38,false),(7,false),(64,true),(71,true),(73,false),(80,false),(82,true),(89,false)]
theorem inputList4903 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4903 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4903 (by decide) v hb
mask_input "4903|620188390195270780792602752|4838082908444025230983168"
def inputClause4904 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,false),(80,false),(82,true),(89,false)]
theorem inputList4904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4904 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4904 (by decide) v hb
mask_input "4904|620188390195270780792602624|4838082908444025230983296"
def inputClause4905 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,true),(80,false),(82,true),(89,false)]
theorem inputList4905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4905 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4905 (by decide) v hb
mask_input "4905|620181325092290550034333824|4845148011424255989252096"
def inputClause4906 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,true),(80,false),(82,true),(89,false)]
theorem inputList4906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4906 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4906 (by decide) v hb
mask_input "4906|620181325092290550034333696|4845148011424255989252224"
def inputClause4907 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,true),(80,false),(82,true),(89,false)]
theorem inputList4907 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4907 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4907 (by decide) v hb
mask_input "4907|620181306645546476324782208|4845166458168329698803712"
def inputClause4908 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,true),(80,false),(82,true),(89,false)]
theorem inputList4908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4908 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4908 (by decide) v hb
mask_input "4908|620181306645546476324782080|4845166458168329698803840"
def inputClause4909 : CNF.NClause := [(38,false),(7,false),(64,false),(71,true),(73,true),(80,false),(82,true),(89,false)]
theorem inputList4909 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4909 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4909 (by decide) v hb
mask_input "4909|620178963909049115211726976|4847509194665690811858944"
def inputClause4910 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,true),(80,false),(82,true),(89,false)]
theorem inputList4910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4910 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4910 (by decide) v hb
mask_input "4910|620178963909049115211726848|4847509194665690811859072"
def inputClause4911 : CNF.NClause := [(38,false),(7,false),(64,true),(71,true),(73,true),(80,false),(82,true),(89,false)]
theorem inputList4911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4911 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4911 (by decide) v hb
mask_input "4911|620178945462305041502175360|4847527641409764521410560"
def inputClause4912 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,true),(80,false),(82,true),(89,false)]
theorem inputList4912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4912 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4912 (by decide) v hb
mask_input "4912|620178945462305041502175232|4847527641409764521410688"
def inputClause4913 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,false),(80,true),(82,true),(89,false)]
theorem inputList4913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4913 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4913 (by decide) v hb
mask_input "4913|618981844005641660150055040|6044629098073145873530880"
def inputClause4914 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,false),(80,true),(82,true),(89,false)]
theorem inputList4914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4914 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4914 (by decide) v hb
mask_input "4914|618981844005641660150054912|6044629098073145873531008"
def inputClause4915 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,false),(80,true),(82,true),(89,false)]
theorem inputList4915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4915 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4915 (by decide) v hb
mask_input "4915|618981825558897586440503424|6044647544817219583082496"
def inputClause4916 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,false),(80,true),(82,true),(89,false)]
theorem inputList4916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4916 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4916 (by decide) v hb
mask_input "4916|618981825558897586440503296|6044647544817219583082624"
def inputClause4917 : CNF.NClause := [(38,false),(7,false),(64,false),(71,true),(73,false),(80,true),(82,true),(89,false)]
theorem inputList4917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4917 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4917 (by decide) v hb
mask_input "4917|618979482822400225327448192|6046990281314580696137728"
def inputClause4918 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,false),(80,true),(82,true),(89,false)]
theorem inputList4918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4918 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4918 (by decide) v hb
mask_input "4918|618979482822400225327448064|6046990281314580696137856"
def inputClause4919 : CNF.NClause := [(38,false),(7,false),(64,true),(71,true),(73,false),(80,true),(82,true),(89,false)]
theorem inputList4919 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4919 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4919 (by decide) v hb
mask_input "4919|618979464375656151617896576|6047008728058654405689344"
def inputClause4920 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,false),(80,true),(82,true),(89,false)]
theorem inputList4920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4920 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4920 (by decide) v hb
mask_input "4920|618979464375656151617896448|6047008728058654405689472"
def inputClause4921 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,true),(80,true),(82,true),(89,false)]
theorem inputList4921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4921 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4921 (by decide) v hb
mask_input "4921|618972399272675920859627648|6054073831038885163958272"
def inputClause4922 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,true),(80,true),(82,true),(89,false)]
theorem inputList4922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4922 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4922 (by decide) v hb
mask_input "4922|618972399272675920859627520|6054073831038885163958400"
def inputClause4923 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,true),(80,true),(82,true),(89,false)]
theorem inputList4923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4923 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4923 (by decide) v hb
mask_input "4923|618972380825931847150076032|6054092277782958873509888"
def inputClause4924 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,true),(80,true),(82,true),(89,false)]
theorem inputList4924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4924 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4924 (by decide) v hb
mask_input "4924|618972380825931847150075904|6054092277782958873510016"
def inputClause4925 : CNF.NClause := [(38,false),(7,false),(64,false),(71,true),(73,true),(80,true),(82,true),(89,false)]
theorem inputList4925 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4925 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4925 (by decide) v hb
mask_input "4925|618970038089434486037020800|6056435014280319986565120"
def inputClause4926 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,true),(80,true),(82,true),(89,false)]
theorem inputList4926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4926 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4926 (by decide) v hb
mask_input "4926|618970038089434486037020672|6056435014280319986565248"
def inputClause4927 : CNF.NClause := [(38,false),(7,false),(64,true),(71,true),(73,true),(80,true),(82,true),(89,false)]
theorem inputList4927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4927 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4927 (by decide) v hb
mask_input "4927|618970019642690412327469184|6056453461024393696116736"
def inputClause4928 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,true),(80,true),(82,true),(89,false)]
theorem inputList4928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4928 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4928 (by decide) v hb
mask_input "4928|618970019642690412327469056|6056453461024393696116864"
def inputClause4929 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,false),(80,false),(82,false),(89,true)]
theorem inputList4929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4929 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4929 (by decide) v hb
mask_input "4929|6056453461024668574023808|618970019642690137449562112"
def inputClause4930 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,false),(80,false),(82,false),(89,true)]
theorem inputList4930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4930 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4930 (by decide) v hb
mask_input "4930|6056453461024668574023680|618970019642690137449562240"
def inputClause4931 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,false),(80,false),(82,false),(89,true)]
theorem inputList4931 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4931 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4931 (by decide) v hb
mask_input "4931|6056435014280594864472192|618970038089434211159113728"
def inputClause4932 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,false),(80,false),(82,false),(89,true)]
theorem inputList4932 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4932 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4932 (by decide) v hb
mask_input "4932|6056435014280594864472064|618970038089434211159113856"
def inputClause4933 : CNF.NClause := [(38,false),(7,false),(64,false),(71,true),(73,false),(80,false),(82,false),(89,true)]
theorem inputList4933 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4933 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4933 (by decide) v hb
mask_input "4933|6054092277783233751416960|618972380825931572272168960"
def inputClause4934 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,false),(80,false),(82,false),(89,true)]
theorem inputList4934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4934 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4934 (by decide) v hb
mask_input "4934|6054092277783233751416832|618972380825931572272169088"
def inputClause4935 : CNF.NClause := [(38,false),(7,false),(64,true),(71,true),(73,false),(80,false),(82,false),(89,true)]
theorem inputList4935 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4935 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4935 (by decide) v hb
mask_input "4935|6054073831039160041865344|618972399272675645981720576"
def inputClause4936 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,false),(80,false),(82,false),(89,true)]
theorem inputList4936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4936 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4936 (by decide) v hb
mask_input "4936|6054073831039160041865216|618972399272675645981720704"
def inputClause4937 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,true),(80,false),(82,false),(89,true)]
theorem inputList4937 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4937 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4937 (by decide) v hb
mask_input "4937|6047008728058929283596416|618979464375655876739989504"
def inputClause4938 : CNF.NClause := [(38,false),(7,true),(64,false),(71,false),(73,true),(80,false),(82,false),(89,true)]
theorem inputList4938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4938 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 7) (spread_mem 7) inputClause4938 (by decide) v hb
mask_input "4938|6047008728058929283596288|618979464375655876739989632"
end Percolation.MaskChain
