import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause5877 : CNF.NClause := [(45,false),(14,false),(63,false),(70,true),(72,false),(79,true),(86,true),(89,true)]
theorem inputList5877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5877 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5877 (by decide) v hb
mask_input "5877|4731589890090872094720|696946915599454436629413888"
def inputClause5879 : CNF.NClause := [(45,false),(14,false),(63,true),(70,true),(72,false),(79,true),(86,true),(89,true)]
theorem inputList5879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5879 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5879 (by decide) v hb
mask_input "5879|4722366518054017318912|696946924822826473484189696"
def inputClause5880 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(72,false),(79,true),(86,true),(89,true)]
theorem inputList5880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5880 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5880 (by decide) v hb
mask_input "5880|4722366518054017302528|696946924822826473484206080"
def inputClause5881 : CNF.NClause := [(45,false),(14,false),(63,false),(70,false),(72,true),(79,true),(86,true),(89,true)]
theorem inputList5881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5881 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5881 (by decide) v hb
mask_input "5881|1189815027938638184448|696950457374316588863324160"
def inputClause5882 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,true),(79,true),(86,true),(89,true)]
theorem inputList5882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5882 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5882 (by decide) v hb
mask_input "5882|1189815027938638168064|696950457374316588863340544"
def inputClause5884 : CNF.NClause := [(45,false),(14,true),(63,true),(70,false),(72,true),(79,true),(86,true),(89,true)]
theorem inputList5884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5884 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5884 (by decide) v hb
mask_input "5884|1180591655901783392256|696950466597688625718116352"
def inputClause5888 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(72,true),(79,true),(86,true),(89,true)]
theorem inputList5888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5888 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5888 (by decide) v hb
mask_input "5888|35184372088832|696951647189309343129419776"
def inputClause5889 : CNF.NClause := [(46,true),(15,false),(77,false),(78,false),(79,false),(80,false),(81,false),(92,false)]
theorem inputList5889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5889 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5889 (by decide) v hb
mask_input "5889|4956444744692527787648516096|70368744177664"
def inputClause5890 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,false),(80,false),(81,false),(92,false)]
theorem inputList5890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5890 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5890 (by decide) v hb
mask_input "5890|4956444744692598156392660992|32768"
def inputClause5892 : CNF.NClause := [(46,false),(15,true),(77,true),(78,false),(79,false),(80,false),(81,false),(92,false)]
theorem inputList5892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5892 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5892 (by decide) v hb
mask_input "5892|4956293628965146327745822720|151115727451828646871040"
def inputClause5893 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(79,false),(80,false),(81,false),(92,false)]
theorem inputList5893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5893 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5893 (by decide) v hb
mask_input "5893|4956142513237694499099017216|302231454903657293676544"
def inputClause5894 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(79,false),(80,false),(81,false),(92,false)]
theorem inputList5894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5894 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5894 (by decide) v hb
mask_input "5894|4956142513237694499098984448|302231454903657293709312"
def inputClause5895 : CNF.NClause := [(46,false),(15,false),(77,true),(78,true),(79,false),(80,false),(81,false),(92,false)]
theorem inputList5895 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5895 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5895 (by decide) v hb
mask_input "5895|4955991397510242670452178944|453347182355485940514816"
def inputClause5896 : CNF.NClause := [(46,false),(15,true),(77,true),(78,true),(79,false),(80,false),(81,false),(92,false)]
theorem inputList5896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5896 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5896 (by decide) v hb
mask_input "5896|4955991397510242670452146176|453347182355485940547584"
def inputClause5897 : CNF.NClause := [(46,false),(15,false),(77,false),(78,false),(79,true),(80,false),(81,false),(92,false)]
theorem inputList5897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5897 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5897 (by decide) v hb
mask_input "5897|4955840281782790841805340672|604462909807314587353088"
def inputClause5898 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,true),(80,false),(81,false),(92,false)]
theorem inputList5898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5898 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5898 (by decide) v hb
mask_input "5898|4955840281782790841805307904|604462909807314587385856"
def inputClause5899 : CNF.NClause := [(46,false),(15,false),(77,true),(78,false),(79,true),(80,false),(81,false),(92,false)]
theorem inputList5899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5899 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5899 (by decide) v hb
mask_input "5899|4955689166055339013158502400|755578637259143234191360"
def inputClause5900 : CNF.NClause := [(46,false),(15,true),(77,true),(78,false),(79,true),(80,false),(81,false),(92,false)]
theorem inputList5900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5900 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5900 (by decide) v hb
mask_input "5900|4955689166055339013158469632|755578637259143234224128"
def inputClause5901 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(79,true),(80,false),(81,false),(92,false)]
theorem inputList5901 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5901 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5901 (by decide) v hb
mask_input "5901|4955538050327887184511664128|906694364710971881029632"
def inputClause5902 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(79,true),(80,false),(81,false),(92,false)]
theorem inputList5902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5902 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5902 (by decide) v hb
mask_input "5902|4955538050327887184511631360|906694364710971881062400"
def inputClause5903 : CNF.NClause := [(46,false),(15,false),(77,true),(78,true),(79,true),(80,false),(81,false),(92,false)]
theorem inputList5903 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5903 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5903 (by decide) v hb
mask_input "5903|4955386934600435355864825856|1057810092162800527867904"
def inputClause5904 : CNF.NClause := [(46,false),(15,true),(77,true),(78,true),(79,true),(80,false),(81,false),(92,false)]
theorem inputList5904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5904 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5904 (by decide) v hb
mask_input "5904|4955386934600435355864793088|1057810092162800527900672"
def inputClause5905 : CNF.NClause := [(46,false),(15,false),(77,false),(78,false),(79,false),(80,true),(81,false),(92,false)]
theorem inputList5905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5905 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5905 (by decide) v hb
mask_input "5905|4955235818872983527217987584|1208925819614629174706176"
def inputClause5906 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,false),(80,true),(81,false),(92,false)]
theorem inputList5906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5906 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5906 (by decide) v hb
mask_input "5906|4955235818872983527217954816|1208925819614629174738944"
def inputClause5908 : CNF.NClause := [(46,false),(15,true),(77,true),(78,false),(79,false),(80,true),(81,false),(92,false)]
theorem inputList5908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5908 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5908 (by decide) v hb
mask_input "5908|4955084703145531698571116544|1360041547066457821577216"
def inputClause5909 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(79,false),(80,true),(81,false),(92,false)]
theorem inputList5909 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5909 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5909 (by decide) v hb
mask_input "5909|4954933587418079869924311040|1511157274518286468382720"
def inputClause5910 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(79,false),(80,true),(81,false),(92,false)]
theorem inputList5910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5910 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5910 (by decide) v hb
mask_input "5910|4954933587418079869924278272|1511157274518286468415488"
def inputClause5911 : CNF.NClause := [(46,false),(15,false),(77,true),(78,true),(79,false),(80,true),(81,false),(92,false)]
theorem inputList5911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5911 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5911 (by decide) v hb
mask_input "5911|4954782471690628041277472768|1662273001970115115220992"
def inputClause5912 : CNF.NClause := [(46,false),(15,true),(77,true),(78,true),(79,false),(80,true),(81,false),(92,false)]
theorem inputList5912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5912 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5912 (by decide) v hb
mask_input "5912|4954782471690628041277440000|1662273001970115115253760"
def inputClause5913 : CNF.NClause := [(46,false),(15,false),(77,false),(78,false),(79,true),(80,true),(81,false),(92,false)]
theorem inputList5913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5913 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5913 (by decide) v hb
mask_input "5913|4954631355963176212630634496|1813388729421943762059264"
def inputClause5914 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,true),(80,true),(81,false),(92,false)]
theorem inputList5914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5914 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5914 (by decide) v hb
mask_input "5914|4954631355963176212630601728|1813388729421943762092032"
def inputClause5915 : CNF.NClause := [(46,false),(15,false),(77,true),(78,false),(79,true),(80,true),(81,false),(92,false)]
theorem inputList5915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5915 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5915 (by decide) v hb
mask_input "5915|4954480240235724383983796224|1964504456873772408897536"
def inputClause5916 : CNF.NClause := [(46,false),(15,true),(77,true),(78,false),(79,true),(80,true),(81,false),(92,false)]
theorem inputList5916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5916 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5916 (by decide) v hb
mask_input "5916|4954480240235724383983763456|1964504456873772408930304"
def inputClause5917 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(79,true),(80,true),(81,false),(92,false)]
theorem inputList5917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5917 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5917 (by decide) v hb
mask_input "5917|4954329124508272555336957952|2115620184325601055735808"
def inputClause5918 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(79,true),(80,true),(81,false),(92,false)]
theorem inputList5918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5918 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5918 (by decide) v hb
mask_input "5918|4954329124508272555336925184|2115620184325601055768576"
def inputClause5919 : CNF.NClause := [(46,false),(15,false),(77,true),(78,true),(79,true),(80,true),(81,false),(92,false)]
theorem inputList5919 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5919 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5919 (by decide) v hb
mask_input "5919|4954178008780820726690119680|2266735911777429702574080"
def inputClause5920 : CNF.NClause := [(46,false),(15,true),(77,true),(78,true),(79,true),(80,true),(81,false),(92,false)]
theorem inputList5920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5920 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5920 (by decide) v hb
mask_input "5920|4954178008780820726690086912|2266735911777429702606848"
def inputClause5921 : CNF.NClause := [(46,false),(15,false),(77,false),(78,false),(79,false),(80,false),(81,true),(92,false)]
theorem inputList5921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5921 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5921 (by decide) v hb
mask_input "5921|4954026893053368898043281408|2417851639229258349412352"
def inputClause5922 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,false),(80,false),(81,true),(92,false)]
theorem inputList5922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5922 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5922 (by decide) v hb
mask_input "5922|4954026893053368898043248640|2417851639229258349445120"
def inputClause5923 : CNF.NClause := [(46,false),(15,false),(77,true),(78,false),(79,false),(80,false),(81,true),(92,false)]
theorem inputList5923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5923 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5923 (by decide) v hb
mask_input "5923|4953875777325917069396443136|2568967366681086996250624"
end Percolation.MaskChain
