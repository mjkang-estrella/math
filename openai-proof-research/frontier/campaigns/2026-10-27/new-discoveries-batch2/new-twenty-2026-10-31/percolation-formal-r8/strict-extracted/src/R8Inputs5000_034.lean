import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause5827 : CNF.NClause := [(45,false),(14,false),(63,true),(70,false),(72,false),(79,false),(86,false),(89,true)]
theorem inputList5827 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5827 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5827 (by decide) v hb
mask_input "5827|77981618323282353197170688|618970028866062174304337920"
def inputClause5828 : CNF.NClause := [(45,false),(14,true),(63,true),(70,false),(72,false),(79,false),(86,false),(89,true)]
theorem inputList5828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5828 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5828 (by decide) v hb
mask_input "5828|77981618323282353197154304|618970028866062174304354304"
def inputClause5829 : CNF.NClause := [(45,false),(14,false),(63,false),(70,true),(72,false),(79,false),(86,false),(89,true)]
theorem inputList5829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5829 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5829 (by decide) v hb
mask_input "5829|77980446955033672640643072|618971200234310854860865536"
def inputClause5831 : CNF.NClause := [(45,false),(14,false),(63,true),(70,true),(72,false),(79,false),(86,false),(89,true)]
theorem inputList5831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5831 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5831 (by decide) v hb
mask_input "5831|77980437731661635785867264|618971209457682891715641344"
def inputClause5832 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(72,false),(79,false),(86,false),(89,true)]
theorem inputList5832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5832 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5832 (by decide) v hb
mask_input "5832|77980437731661635785850880|618971209457682891715657728"
def inputClause5833 : CNF.NClause := [(45,false),(14,false),(63,false),(70,false),(72,true),(79,false),(86,false),(89,true)]
theorem inputList5833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5833 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5833 (by decide) v hb
mask_input "5833|77976905180171520406732800|618974742009173007094775808"
def inputClause5834 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,true),(79,false),(86,false),(89,true)]
theorem inputList5834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5834 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5834 (by decide) v hb
mask_input "5834|77976905180171520406716416|618974742009173007094792192"
def inputClause5835 : CNF.NClause := [(45,false),(14,false),(63,true),(70,false),(72,true),(79,false),(86,false),(89,true)]
theorem inputList5835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5835 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5835 (by decide) v hb
mask_input "5835|77976895956799483551956992|618974751232545043949551616"
def inputClause5836 : CNF.NClause := [(45,false),(14,true),(63,true),(70,false),(72,true),(79,false),(86,false),(89,true)]
theorem inputList5836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5836 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5836 (by decide) v hb
mask_input "5836|77976895956799483551940608|618974751232545043949568000"
def inputClause5837 : CNF.NClause := [(45,false),(14,false),(63,false),(70,true),(72,true),(79,false),(86,false),(89,true)]
theorem inputList5837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5837 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5837 (by decide) v hb
mask_input "5837|77975724588550802995429376|618975922600793724506079232"
def inputClause5839 : CNF.NClause := [(45,false),(14,false),(63,true),(70,true),(72,true),(79,false),(86,false),(89,true)]
theorem inputList5839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5839 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5839 (by decide) v hb
mask_input "5839|77975715365178766140653568|618975931824165761360855040"
def inputClause5840 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(72,true),(79,false),(86,false),(89,true)]
theorem inputList5840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5840 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5840 (by decide) v hb
mask_input "5840|77975715365178766140637184|618975931824165761360871424"
def inputClause5841 : CNF.NClause := [(45,false),(14,false),(63,false),(70,false),(72,false),(79,true),(86,false),(89,true)]
theorem inputList5841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5841 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5841 (by decide) v hb
mask_input "5841|77377164636847075464593408|619574482552497452036915200"
def inputClause5842 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,false),(79,true),(86,false),(89,true)]
theorem inputList5842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5842 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5842 (by decide) v hb
mask_input "5842|77377164636847075464577024|619574482552497452036931584"
def inputClause5843 : CNF.NClause := [(45,false),(14,false),(63,true),(70,false),(72,false),(79,true),(86,false),(89,true)]
theorem inputList5843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5843 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5843 (by decide) v hb
mask_input "5843|77377155413475038609817600|619574491775869488891691008"
def inputClause5844 : CNF.NClause := [(45,false),(14,true),(63,true),(70,false),(72,false),(79,true),(86,false),(89,true)]
theorem inputList5844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5844 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5844 (by decide) v hb
mask_input "5844|77377155413475038609801216|619574491775869488891707392"
def inputClause5845 : CNF.NClause := [(45,false),(14,false),(63,false),(70,true),(72,false),(79,true),(86,false),(89,true)]
theorem inputList5845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5845 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5845 (by decide) v hb
mask_input "5845|77375984045226358053289984|619575663144118169448218624"
def inputClause5847 : CNF.NClause := [(45,false),(14,false),(63,true),(70,true),(72,false),(79,true),(86,false),(89,true)]
theorem inputList5847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5847 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5847 (by decide) v hb
mask_input "5847|77375974821854321198514176|619575672367490206302994432"
def inputClause5848 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(72,false),(79,true),(86,false),(89,true)]
theorem inputList5848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5848 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5848 (by decide) v hb
mask_input "5848|77375974821854321198497792|619575672367490206303010816"
def inputClause5849 : CNF.NClause := [(45,false),(14,false),(63,false),(70,false),(72,true),(79,true),(86,false),(89,true)]
theorem inputList5849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5849 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5849 (by decide) v hb
mask_input "5849|77372442270364205819379712|619579204918980321682128896"
def inputClause5850 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,true),(79,true),(86,false),(89,true)]
theorem inputList5850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5850 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5850 (by decide) v hb
mask_input "5850|77372442270364205819363328|619579204918980321682145280"
def inputClause5852 : CNF.NClause := [(45,false),(14,true),(63,true),(70,false),(72,true),(79,true),(86,false),(89,true)]
theorem inputList5852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5852 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5852 (by decide) v hb
mask_input "5852|77372433046992168964587520|619579214142352358536921088"
def inputClause5853 : CNF.NClause := [(45,false),(14,false),(63,false),(70,true),(72,true),(79,true),(86,false),(89,true)]
theorem inputList5853 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5853 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5853 (by decide) v hb
mask_input "5853|77371261678743488408076288|619580385510601039093432320"
def inputClause5856 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(72,true),(79,true),(86,false),(89,true)]
theorem inputList5856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5856 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5856 (by decide) v hb
mask_input "5856|77371252455371451553284096|619580394733973075948224512"
def inputClause5857 : CNF.NClause := [(45,false),(14,false),(63,false),(70,false),(72,false),(79,false),(86,true),(89,true)]
theorem inputList5857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5857 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5857 (by decide) v hb
mask_input "5857|610375091318122870751232|696341272098026404630757376"
def inputClause5859 : CNF.NClause := [(45,false),(14,false),(63,true),(70,false),(72,false),(79,false),(86,true),(89,true)]
theorem inputList5859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5859 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5859 (by decide) v hb
mask_input "5859|610365867946086015975424|696341281321398441485533184"
def inputClause5860 : CNF.NClause := [(45,false),(14,true),(63,true),(70,false),(72,false),(79,false),(86,true),(89,true)]
theorem inputList5860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5860 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5860 (by decide) v hb
mask_input "5860|610365867946086015959040|696341281321398441485549568"
def inputClause5861 : CNF.NClause := [(45,false),(14,false),(63,false),(70,true),(72,false),(79,false),(86,true),(89,true)]
theorem inputList5861 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5861 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5861 (by decide) v hb
mask_input "5861|609194499697405459447808|696342452689647122042060800"
def inputClause5863 : CNF.NClause := [(45,false),(14,false),(63,true),(70,true),(72,false),(79,false),(86,true),(89,true)]
theorem inputList5863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5863 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5863 (by decide) v hb
mask_input "5863|609185276325368604672000|696342461913019158896836608"
def inputClause5864 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(72,false),(79,false),(86,true),(89,true)]
theorem inputList5864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5864 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5864 (by decide) v hb
mask_input "5864|609185276325368604655616|696342461913019158896852992"
def inputClause5865 : CNF.NClause := [(45,false),(14,false),(63,false),(70,false),(72,true),(79,false),(86,true),(89,true)]
theorem inputList5865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5865 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5865 (by decide) v hb
mask_input "5865|605652724835253225537536|696345994464509274275971072"
def inputClause5866 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,true),(79,false),(86,true),(89,true)]
theorem inputList5866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5866 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5866 (by decide) v hb
mask_input "5866|605652724835253225521152|696345994464509274275987456"
def inputClause5867 : CNF.NClause := [(45,false),(14,false),(63,true),(70,false),(72,true),(79,false),(86,true),(89,true)]
theorem inputList5867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5867 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5867 (by decide) v hb
mask_input "5867|605643501463216370761728|696346003687881311130746880"
def inputClause5868 : CNF.NClause := [(45,false),(14,true),(63,true),(70,false),(72,true),(79,false),(86,true),(89,true)]
theorem inputList5868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5868 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5868 (by decide) v hb
mask_input "5868|605643501463216370745344|696346003687881311130763264"
def inputClause5869 : CNF.NClause := [(45,false),(14,false),(63,false),(70,true),(72,true),(79,false),(86,true),(89,true)]
theorem inputList5869 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5869 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5869 (by decide) v hb
mask_input "5869|604472133214535814234112|696347175056129991687274496"
def inputClause5871 : CNF.NClause := [(45,false),(14,false),(63,true),(70,true),(72,true),(79,false),(86,true),(89,true)]
theorem inputList5871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5871 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5871 (by decide) v hb
mask_input "5871|604462909842498959458304|696347184279502028542050304"
def inputClause5872 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(72,true),(79,false),(86,true),(89,true)]
theorem inputList5872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5872 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5872 (by decide) v hb
mask_input "5872|604462909842498959441920|696347184279502028542066688"
def inputClause5873 : CNF.NClause := [(45,false),(14,false),(63,false),(70,false),(72,false),(79,true),(86,true),(89,true)]
theorem inputList5873 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5873 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5873 (by decide) v hb
mask_input "5873|5912181510808283398144|696945735007833719218110464"
def inputClause5874 : CNF.NClause := [(45,false),(14,true),(63,false),(70,false),(72,false),(79,true),(86,true),(89,true)]
theorem inputList5874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5874 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5874 (by decide) v hb
mask_input "5874|5912181510808283381760|696945735007833719218126848"
def inputClause5876 : CNF.NClause := [(45,false),(14,true),(63,true),(70,false),(72,false),(79,true),(86,true),(89,true)]
theorem inputList5876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5876 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 14) (spread_mem 14) inputClause5876 (by decide) v hb
mask_input "5876|5902958138771428605952|696945744231205756072902656"
end Percolation.MaskChain
