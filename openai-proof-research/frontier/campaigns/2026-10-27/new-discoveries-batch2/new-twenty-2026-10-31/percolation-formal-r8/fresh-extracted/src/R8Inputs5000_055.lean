import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause6790 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,false),(78,false),(86,false),(90,false)]
theorem inputList6790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6790 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6790 (by decide) v hb
mask_input "6790|1315651320583234429499998208|147573952589680607232"
def inputClause6791 : CNF.NClause := [(53,false),(22,false),(64,true),(67,true),(75,false),(78,false),(86,false),(90,false)]
theorem inputList6791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6791 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6791 (by decide) v hb
mask_input "6791|1315651302136490355794640896|166020696663385964544"
def inputClause6792 : CNF.NClause := [(53,false),(22,true),(64,true),(67,true),(75,false),(78,false),(86,false),(90,false)]
theorem inputList6792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6792 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6792 (by decide) v hb
mask_input "6792|1315651302136490355790446592|166020696663390158848"
def inputClause6793 : CNF.NClause := [(53,false),(22,false),(64,false),(67,false),(75,true),(78,false),(86,false),(90,false)]
theorem inputList6793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6793 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6793 (by decide) v hb
mask_input "6793|1315613689225324062018895872|37778931862957161709568"
def inputClause6795 : CNF.NClause := [(53,false),(22,false),(64,true),(67,false),(75,true),(78,false),(86,false),(90,false)]
theorem inputList6795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6795 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6795 (by decide) v hb
mask_input "6795|1315613670778579988309344256|37797378607030871261184"
def inputClause6796 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(75,true),(78,false),(86,false),(90,false)]
theorem inputList6796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6796 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6796 (by decide) v hb
mask_input "6796|1315613670778579988305149952|37797378607030875455488"
def inputClause6797 : CNF.NClause := [(53,false),(22,false),(64,false),(67,true),(75,true),(78,false),(86,false),(90,false)]
theorem inputList6797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6797 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6797 (by decide) v hb
mask_input "6797|1315613541651371472342482944|37926505815546838122496"
def inputClause6798 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,true),(78,false),(86,false),(90,false)]
theorem inputList6798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6798 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6798 (by decide) v hb
mask_input "6798|1315613541651371472338288640|37926505815546842316800"
def inputClause6799 : CNF.NClause := [(53,false),(22,false),(64,true),(67,true),(75,true),(78,false),(86,false),(90,false)]
theorem inputList6799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6799 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6799 (by decide) v hb
mask_input "6799|1315613523204627398632931328|37944952559620547674112"
def inputClause6800 : CNF.NClause := [(53,false),(22,true),(64,true),(67,true),(75,true),(78,false),(86,false),(90,false)]
theorem inputList6800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6800 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6800 (by decide) v hb
mask_input "6800|1315613523204627398628737024|37944952559620551868416"
def inputClause6801 : CNF.NClause := [(53,false),(22,false),(64,false),(67,false),(75,false),(78,true),(86,false),(90,false)]
theorem inputList6801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6801 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6801 (by decide) v hb
mask_input "6801|1315349236702283361886928896|302231454903657293676544"
def inputClause6803 : CNF.NClause := [(53,false),(22,false),(64,true),(67,false),(75,false),(78,true),(86,false),(90,false)]
theorem inputList6803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6803 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6803 (by decide) v hb
mask_input "6803|1315349218255539288177377280|302249901647731003228160"
def inputClause6804 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(75,false),(78,true),(86,false),(90,false)]
theorem inputList6804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6804 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6804 (by decide) v hb
mask_input "6804|1315349218255539288173182976|302249901647731007422464"
def inputClause6805 : CNF.NClause := [(53,false),(22,false),(64,false),(67,true),(75,false),(78,true),(86,false),(90,false)]
theorem inputList6805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6805 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6805 (by decide) v hb
mask_input "6805|1315349089128330772210515968|302379028856246970089472"
def inputClause6806 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,false),(78,true),(86,false),(90,false)]
theorem inputList6806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6806 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6806 (by decide) v hb
mask_input "6806|1315349089128330772206321664|302379028856246974283776"
def inputClause6807 : CNF.NClause := [(53,false),(22,false),(64,true),(67,true),(75,false),(78,true),(86,false),(90,false)]
theorem inputList6807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6807 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6807 (by decide) v hb
mask_input "6807|1315349070681586698500964352|302397475600320679641088"
def inputClause6808 : CNF.NClause := [(53,false),(22,true),(64,true),(67,true),(75,false),(78,true),(86,false),(90,false)]
theorem inputList6808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6808 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6808 (by decide) v hb
mask_input "6808|1315349070681586698496770048|302397475600320683835392"
def inputClause6809 : CNF.NClause := [(53,false),(22,false),(64,false),(67,false),(75,true),(78,true),(86,false),(90,false)]
theorem inputList6809 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6809 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6809 (by decide) v hb
mask_input "6809|1315311457770420404725219328|340010386766614455386112"
def inputClause6811 : CNF.NClause := [(53,false),(22,false),(64,true),(67,false),(75,true),(78,true),(86,false),(90,false)]
theorem inputList6811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6811 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6811 (by decide) v hb
mask_input "6811|1315311439323676331015667712|340028833510688164937728"
def inputClause6812 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(75,true),(78,true),(86,false),(90,false)]
theorem inputList6812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6812 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6812 (by decide) v hb
mask_input "6812|1315311439323676331011473408|340028833510688169132032"
def inputClause6813 : CNF.NClause := [(53,false),(22,false),(64,false),(67,true),(75,true),(78,true),(86,false),(90,false)]
theorem inputList6813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6813 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6813 (by decide) v hb
mask_input "6813|1315311310196467815048806400|340157960719204131799040"
def inputClause6814 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,true),(78,true),(86,false),(90,false)]
theorem inputList6814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6814 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6814 (by decide) v hb
mask_input "6814|1315311310196467815044612096|340157960719204135993344"
def inputClause6815 : CNF.NClause := [(53,false),(22,false),(64,true),(67,true),(75,true),(78,true),(86,false),(90,false)]
theorem inputList6815 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6815 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6815 (by decide) v hb
mask_input "6815|1315311291749723741339254784|340176407463277841350656"
def inputClause6816 : CNF.NClause := [(53,false),(22,true),(64,true),(67,true),(75,true),(78,true),(86,false),(90,false)]
theorem inputList6816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6816 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6816 (by decide) v hb
mask_input "6816|1315311291749723741335060480|340176407463277845544960"
def inputClause6817 : CNF.NClause := [(53,false),(22,false),(64,false),(67,false),(75,false),(78,false),(86,true),(90,false)]
theorem inputList6817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6817 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6817 (by decide) v hb
mask_input "6817|1238280215701850751999410176|77371252455336267181195264"
def inputClause6819 : CNF.NClause := [(53,false),(22,false),(64,true),(67,false),(75,false),(78,false),(86,true),(90,false)]
theorem inputList6819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6819 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6819 (by decide) v hb
mask_input "6819|1238280197255106678289858560|77371270902080340890746880"
def inputClause6820 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(75,false),(78,false),(86,true),(90,false)]
theorem inputList6820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6820 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6820 (by decide) v hb
mask_input "6820|1238280197255106678285664256|77371270902080340894941184"
def inputClause6821 : CNF.NClause := [(53,false),(22,false),(64,false),(67,true),(75,false),(78,false),(86,true),(90,false)]
theorem inputList6821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6821 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6821 (by decide) v hb
mask_input "6821|1238280068127898162322997248|77371400029288856857608192"
def inputClause6822 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,false),(78,false),(86,true),(90,false)]
theorem inputList6822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6822 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6822 (by decide) v hb
mask_input "6822|1238280068127898162318802944|77371400029288856861802496"
def inputClause6823 : CNF.NClause := [(53,false),(22,false),(64,true),(67,true),(75,false),(78,false),(86,true),(90,false)]
theorem inputList6823 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6823 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6823 (by decide) v hb
mask_input "6823|1238280049681154088613445632|77371418476032930567159808"
def inputClause6824 : CNF.NClause := [(53,false),(22,true),(64,true),(67,true),(75,false),(78,false),(86,true),(90,false)]
theorem inputList6824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6824 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6824 (by decide) v hb
mask_input "6824|1238280049681154088609251328|77371418476032930571354112"
def inputClause6825 : CNF.NClause := [(53,false),(22,false),(64,false),(67,false),(75,true),(78,false),(86,true),(90,false)]
theorem inputList6825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6825 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6825 (by decide) v hb
mask_input "6825|1238242436769987794837700608|77409031387199224342904832"
def inputClause6827 : CNF.NClause := [(53,false),(22,false),(64,true),(67,false),(75,true),(78,false),(86,true),(90,false)]
theorem inputList6827 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6827 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6827 (by decide) v hb
mask_input "6827|1238242418323243721128148992|77409049833943298052456448"
def inputClause6828 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(75,true),(78,false),(86,true),(90,false)]
theorem inputList6828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6828 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6828 (by decide) v hb
mask_input "6828|1238242418323243721123954688|77409049833943298056650752"
def inputClause6829 : CNF.NClause := [(53,false),(22,false),(64,false),(67,true),(75,true),(78,false),(86,true),(90,false)]
theorem inputList6829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6829 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6829 (by decide) v hb
mask_input "6829|1238242289196035205161287680|77409178961151814019317760"
def inputClause6830 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,true),(78,false),(86,true),(90,false)]
theorem inputList6830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6830 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6830 (by decide) v hb
mask_input "6830|1238242289196035205157093376|77409178961151814023512064"
def inputClause6831 : CNF.NClause := [(53,false),(22,false),(64,true),(67,true),(75,true),(78,false),(86,true),(90,false)]
theorem inputList6831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6831 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6831 (by decide) v hb
mask_input "6831|1238242270749291131451736064|77409197407895887728869376"
def inputClause6832 : CNF.NClause := [(53,false),(22,true),(64,true),(67,true),(75,true),(78,false),(86,true),(90,false)]
theorem inputList6832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6832 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6832 (by decide) v hb
mask_input "6832|1238242270749291131447541760|77409197407895887733063680"
def inputClause6833 : CNF.NClause := [(53,false),(22,false),(64,false),(67,false),(75,false),(78,true),(86,true),(90,false)]
theorem inputList6833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6833 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6833 (by decide) v hb
mask_input "6833|1237977984246947094705733632|77673483910239924474871808"
def inputClause6835 : CNF.NClause := [(53,false),(22,false),(64,true),(67,false),(75,false),(78,true),(86,true),(90,false)]
theorem inputList6835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6835 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6835 (by decide) v hb
mask_input "6835|1237977965800203020996182016|77673502356983998184423424"
end Percolation.MaskChain
