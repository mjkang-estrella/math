import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause6710 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,false),(79,true),(85,true),(88,false)]
theorem inputList6710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6710 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6710 (by decide) v hb
mask_input "6710|309494528345790702480785408|39290236711428037856460800"
def inputClause6718 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,true),(79,true),(85,true),(88,false)]
theorem inputList6718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6718 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6718 (by decide) v hb
mask_input "6718|309485083612824963190358016|39299681444393777146888192"
def inputClause6726 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,false),(79,false),(85,false),(88,true)]
theorem inputList6726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6726 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6726 (by decide) v hb
mask_input "6726|39299607661921081933955072|309485157395297658403291136"
def inputClause6734 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,true),(79,false),(85,false),(88,true)]
theorem inputList6734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6734 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6734 (by decide) v hb
mask_input "6734|39290162928955342643527680|309494602128263397693718528"
def inputClause6742 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,false),(79,true),(85,false),(88,true)]
theorem inputList6742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6742 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6742 (by decide) v hb
mask_input "6742|38695144752113767346601984|310089620305104972990644224"
def inputClause6750 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,true),(79,true),(85,false),(88,true)]
theorem inputList6750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6750 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6750 (by decide) v hb
mask_input "6750|38685700019148028056174592|310099065038070712281071616"
def inputClause6758 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,false),(79,false),(85,true),(88,true)]
theorem inputList6758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6758 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6758 (by decide) v hb
mask_input "6758|613981434252948343357440|348170783622965791993888768"
def inputClause6766 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,true),(79,false),(85,true),(88,true)]
theorem inputList6766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6766 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6766 (by decide) v hb
mask_input "6766|604536701287209052930048|348180228355931531284316160"
def inputClause6774 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,false),(79,true),(85,true),(88,true)]
theorem inputList6774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6774 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6774 (by decide) v hb
mask_input "6774|9518524445633756004352|348775246532773106581241856"
def inputClause6782 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,true),(79,true),(85,true),(88,true)]
theorem inputList6782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6782 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6782 (by decide) v hb
mask_input "6782|73791479894465576960|348784691265738845871669248"
def inputClause6786 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,false),(78,false),(86,false),(90,false)]
theorem inputList6786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6786 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6786 (by decide) v hb
mask_input "6786|1315651468157187019176411136|4194304"
def inputClause6794 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,true),(78,false),(86,false),(90,false)]
theorem inputList6794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6794 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6794 (by decide) v hb
mask_input "6794|1315613689225324062014701568|37778931862957165903872"
def inputClause6802 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,false),(78,true),(86,false),(90,false)]
theorem inputList6802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6802 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6802 (by decide) v hb
mask_input "6802|1315349236702283361882734592|302231454903657297870848"
def inputClause6810 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,true),(78,true),(86,false),(90,false)]
theorem inputList6810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6810 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6810 (by decide) v hb
mask_input "6810|1315311457770420404721025024|340010386766614459580416"
def inputClause6818 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,false),(78,false),(86,true),(90,false)]
theorem inputList6818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6818 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6818 (by decide) v hb
mask_input "6818|1238280215701850751995215872|77371252455336267185389568"
def inputClause6826 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,true),(78,false),(86,true),(90,false)]
theorem inputList6826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6826 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6826 (by decide) v hb
mask_input "6826|1238242436769987794833506304|77409031387199224347099136"
def inputClause6834 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,false),(78,true),(86,true),(90,false)]
theorem inputList6834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6834 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6834 (by decide) v hb
mask_input "6834|1237977984246947094701539328|77673483910239924479066112"
def inputClause6842 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,true),(78,true),(86,true),(90,false)]
theorem inputList6842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6842 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6842 (by decide) v hb
mask_input "6842|1237940205315084137539829760|77711262842102881640775680"
def inputClause6850 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,false),(78,false),(86,false),(90,true)]
theorem inputList6850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6850 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6850 (by decide) v hb
mask_input "6850|77711428871806744277286912|1237940039285380274903318528"
def inputClause6858 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,true),(78,false),(86,false),(90,true)]
theorem inputList6858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6858 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6858 (by decide) v hb
mask_input "6858|77673649939943787115577344|1237977818217243232065028096"
def inputClause6866 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,false),(78,true),(86,false),(90,true)]
theorem inputList6866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6866 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6866 (by decide) v hb
mask_input "6866|77409197416903086983610368|1238242270740283932196995072"
def inputClause6874 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,true),(78,true),(86,false),(90,true)]
theorem inputList6874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6874 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6874 (by decide) v hb
mask_input "6874|77371418485040129821900800|1238280049672146889358704640"
def inputClause6882 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,false),(78,false),(86,true),(90,true)]
theorem inputList6882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6882 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6882 (by decide) v hb
mask_input "6882|340176416470477096091648|1315311291740716542084513792"
def inputClause6890 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,true),(78,false),(86,true),(90,true)]
theorem inputList6890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6890 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6890 (by decide) v hb
mask_input "6890|302397484607519934382080|1315349070672579499246223360"
def inputClause6898 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,false),(78,true),(86,true),(90,true)]
theorem inputList6898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6898 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6898 (by decide) v hb
mask_input "6898|37944961566819802415104|1315613523195620199378190336"
def inputClause6906 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,true),(78,true),(86,true),(90,true)]
theorem inputList6906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6906 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6906 (by decide) v hb
mask_input "6906|166029703862640705536|1315651302127483156539899904"
def inputClause6914 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,false),(81,false),(83,false),(89,false)]
theorem inputList6914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6914 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6914 (by decide) v hb
mask_input "6914|631078351790223043382476800|8388608"
def inputClause6915 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(74,false),(81,false),(83,false),(89,false)]
theorem inputList6915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6915 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6915 (by decide) v hb
mask_input "6915|631078314896734895971762176|36893488147419103232"
def inputClause6916 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,false),(81,false),(83,false),(89,false)]
theorem inputList6916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6916 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6916 (by decide) v hb
mask_input "6916|631078314896734895963373568|36893488147427491840"
def inputClause6917 : CNF.NClause := [(54,false),(23,false),(65,false),(67,true),(74,false),(81,false),(83,false),(89,false)]
theorem inputList6917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6917 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6917 (by decide) v hb
mask_input "6917|631078204216270453714452480|147573952589676412928"
def inputClause6918 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(74,false),(81,false),(83,false),(89,false)]
theorem inputList6918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6918 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6918 (by decide) v hb
mask_input "6918|631078204216270453706063872|147573952589684801536"
def inputClause6919 : CNF.NClause := [(54,false),(23,false),(65,true),(67,true),(74,false),(81,false),(83,false),(89,false)]
theorem inputList6919 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6919 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6919 (by decide) v hb
mask_input "6919|631078167322782306295349248|184467440737095516160"
def inputClause6920 : CNF.NClause := [(54,false),(23,true),(65,true),(67,true),(74,false),(81,false),(83,false),(89,false)]
theorem inputList6920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6920 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6920 (by decide) v hb
mask_input "6920|631078167322782306286960640|184467440737103904768"
def inputClause6921 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,true),(81,false),(83,false),(89,false)]
theorem inputList6921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6921 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6921 (by decide) v hb
mask_input "6921|631059462324291564810010624|18889465931478580854784"
def inputClause6922 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,true),(81,false),(83,false),(89,false)]
theorem inputList6922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6922 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6922 (by decide) v hb
mask_input "6922|631059462324291564801622016|18889465931478589243392"
def inputClause6923 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(74,true),(81,false),(83,false),(89,false)]
theorem inputList6923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6923 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6923 (by decide) v hb
mask_input "6923|631059425430803417390907392|18926359419625999958016"
def inputClause6924 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,true),(81,false),(83,false),(89,false)]
theorem inputList6924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6924 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6924 (by decide) v hb
mask_input "6924|631059425430803417382518784|18926359419626008346624"
def inputClause6925 : CNF.NClause := [(54,false),(23,false),(65,false),(67,true),(74,true),(81,false),(83,false),(89,false)]
theorem inputList6925 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6925 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6925 (by decide) v hb
mask_input "6925|631059314750338975133597696|19037039884068257267712"
def inputClause6926 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(74,true),(81,false),(83,false),(89,false)]
theorem inputList6926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6926 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6926 (by decide) v hb
mask_input "6926|631059314750338975125209088|19037039884068265656320"
def inputClause6927 : CNF.NClause := [(54,false),(23,false),(65,true),(67,true),(74,true),(81,false),(83,false),(89,false)]
theorem inputList6927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6927 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6927 (by decide) v hb
mask_input "6927|631059277856850827714494464|19073933372215676370944"
end Percolation.MaskChain
