import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause6881 : CNF.NClause := [(53,false),(22,false),(64,false),(67,false),(75,false),(78,false),(86,true),(90,true)]
theorem inputList6881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6881 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6881 (by decide) v hb
mask_input "6881|340176416470477100285952|1315311291740716542080319488"
def inputClause6883 : CNF.NClause := [(53,false),(22,false),(64,true),(67,false),(75,false),(78,false),(86,true),(90,true)]
theorem inputList6883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6883 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6883 (by decide) v hb
mask_input "6883|340157969726403390734336|1315311310187460615789871104"
def inputClause6884 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(75,false),(78,false),(86,true),(90,true)]
theorem inputList6884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6884 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6884 (by decide) v hb
mask_input "6884|340157969726403386540032|1315311310187460615794065408"
def inputClause6885 : CNF.NClause := [(53,false),(22,false),(64,false),(67,true),(75,false),(78,false),(86,true),(90,true)]
theorem inputList6885 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6885 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6885 (by decide) v hb
mask_input "6885|340028842517887423873024|1315311439314669131756732416"
def inputClause6886 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,false),(78,false),(86,true),(90,true)]
theorem inputList6886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6886 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6886 (by decide) v hb
mask_input "6886|340028842517887419678720|1315311439314669131760926720"
def inputClause6887 : CNF.NClause := [(53,false),(22,false),(64,true),(67,true),(75,false),(78,false),(86,true),(90,true)]
theorem inputList6887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6887 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6887 (by decide) v hb
mask_input "6887|340010395773813714321408|1315311457761413205466284032"
def inputClause6888 : CNF.NClause := [(53,false),(22,true),(64,true),(67,true),(75,false),(78,false),(86,true),(90,true)]
theorem inputList6888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6888 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6888 (by decide) v hb
mask_input "6888|340010395773813710127104|1315311457761413205470478336"
def inputClause6889 : CNF.NClause := [(53,false),(22,false),(64,false),(67,false),(75,true),(78,false),(86,true),(90,true)]
theorem inputList6889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6889 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6889 (by decide) v hb
mask_input "6889|302397484607519938576384|1315349070672579499242029056"
def inputClause6892 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(75,true),(78,false),(86,true),(90,true)]
theorem inputList6892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6892 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6892 (by decide) v hb
mask_input "6892|302379037863446224830464|1315349089119323572955774976"
def inputClause6893 : CNF.NClause := [(53,false),(22,false),(64,false),(67,true),(75,true),(78,false),(86,true),(90,true)]
theorem inputList6893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6893 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6893 (by decide) v hb
mask_input "6893|302249910654930262163456|1315349218246532088918441984"
def inputClause6894 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,true),(78,false),(86,true),(90,true)]
theorem inputList6894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6894 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6894 (by decide) v hb
mask_input "6894|302249910654930257969152|1315349218246532088922636288"
def inputClause6896 : CNF.NClause := [(53,false),(22,true),(64,true),(67,true),(75,true),(78,false),(86,true),(90,true)]
theorem inputList6896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6896 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6896 (by decide) v hb
mask_input "6896|302231463910856548417536|1315349236693276162632187904"
def inputClause6897 : CNF.NClause := [(53,false),(22,false),(64,false),(67,false),(75,false),(78,true),(86,true),(90,true)]
theorem inputList6897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6897 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6897 (by decide) v hb
mask_input "6897|37944961566819806609408|1315613523195620199373996032"
def inputClause6899 : CNF.NClause := [(53,false),(22,false),(64,true),(67,false),(75,false),(78,true),(86,true),(90,true)]
theorem inputList6899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6899 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6899 (by decide) v hb
mask_input "6899|37926514822746097057792|1315613541642364273083547648"
def inputClause6900 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(75,false),(78,true),(86,true),(90,true)]
theorem inputList6900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6900 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6900 (by decide) v hb
mask_input "6900|37926514822746092863488|1315613541642364273087741952"
def inputClause6901 : CNF.NClause := [(53,false),(22,false),(64,false),(67,true),(75,false),(78,true),(86,true),(90,true)]
theorem inputList6901 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6901 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6901 (by decide) v hb
mask_input "6901|37797387614230130196480|1315613670769572789050408960"
def inputClause6902 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,false),(78,true),(86,true),(90,true)]
theorem inputList6902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6902 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6902 (by decide) v hb
mask_input "6902|37797387614230126002176|1315613670769572789054603264"
def inputClause6903 : CNF.NClause := [(53,false),(22,false),(64,true),(67,true),(75,false),(78,true),(86,true),(90,true)]
theorem inputList6903 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6903 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6903 (by decide) v hb
mask_input "6903|37778940870156420644864|1315613689216316862759960576"
def inputClause6904 : CNF.NClause := [(53,false),(22,true),(64,true),(67,true),(75,false),(78,true),(86,true),(90,true)]
theorem inputList6904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6904 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6904 (by decide) v hb
mask_input "6904|37778940870156416450560|1315613689216316862764154880"
def inputClause6905 : CNF.NClause := [(53,false),(22,false),(64,false),(67,false),(75,true),(78,true),(86,true),(90,true)]
theorem inputList6905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6905 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6905 (by decide) v hb
mask_input "6905|166029703862644899840|1315651302127483156535705600"
def inputClause6908 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(75,true),(78,true),(86,true),(90,true)]
theorem inputList6908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6908 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6908 (by decide) v hb
mask_input "6908|147582959788931153920|1315651320574227230249451520"
def inputClause6909 : CNF.NClause := [(53,false),(22,false),(64,false),(67,true),(75,true),(78,true),(86,true),(90,true)]
theorem inputList6909 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6909 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6909 (by decide) v hb
mask_input "6909|18455751272968486912|1315651449701435746212118528"
def inputClause6910 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,true),(78,true),(86,true),(90,true)]
theorem inputList6910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6910 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6910 (by decide) v hb
mask_input "6910|18455751272964292608|1315651449701435746216312832"
def inputClause6912 : CNF.NClause := [(53,false),(22,true),(64,true),(67,true),(75,true),(78,true),(86,true),(90,true)]
theorem inputList6912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6912 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6912 (by decide) v hb
mask_input "6912|9007199254740992|1315651468148179819925864448"
def inputClause6913 : CNF.NClause := [(54,true),(23,false),(65,false),(67,false),(74,false),(81,false),(83,false),(89,false)]
theorem inputList6913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6913 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 23) (spread_mem 23) inputClause6913 (by decide) v hb
mask_input "6913|631078351772208644881383424|18014398509481984"
def inputClause7041 : CNF.NClause := [(55,true),(24,false),(63,false),(67,false),(76,false),(80,false),(84,false),(91,false)]
theorem inputList7041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7041 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7041 (by decide) v hb
mask_input "7041|2496507532165259786639638528|36028797018963968"
def inputClause7042 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(76,false),(80,false),(84,false),(91,false)]
theorem inputList7042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7042 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7042 (by decide) v hb
mask_input "7042|2496507532201288583641825280|16777216"
def inputClause7069 : CNF.NClause := [(55,false),(24,false),(63,false),(67,true),(76,true),(80,true),(84,false),(91,false)]
theorem inputList7069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7069 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7069 (by decide) v hb
mask_input "7069|2495222900943995450484064256|1284631257293133174538240"
def inputClause7070 : CNF.NClause := [(55,false),(24,true),(63,false),(67,true),(76,true),(80,true),(84,false),(91,false)]
theorem inputList7070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7070 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7070 (by decide) v hb
mask_input "7070|2495222900943995450467287040|1284631257293133191315456"
def inputClause7071 : CNF.NClause := [(55,false),(24,false),(63,true),(67,true),(76,true),(80,true),(84,false),(91,false)]
theorem inputList7071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7071 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7071 (by decide) v hb
mask_input "7071|2495222891720623413629288448|1284640480665170029314048"
def inputClause7072 : CNF.NClause := [(55,false),(24,true),(63,true),(67,true),(76,true),(80,true),(84,false),(91,false)]
theorem inputList7072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7072 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7072 (by decide) v hb
mask_input "7072|2495222891720623413612511232|1284640480665170046091264"
def inputClause7073 : CNF.NClause := [(55,false),(24,false),(63,false),(67,false),(76,false),(80,false),(84,true),(91,false)]
theorem inputList7073 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7073 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7073 (by decide) v hb
mask_input "7073|2477164719087454516863303680|19342813113834066795298816"
def inputClause7074 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(76,false),(80,false),(84,true),(91,false)]
theorem inputList7074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7074 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7074 (by decide) v hb
mask_input "7074|2477164719087454516846526464|19342813113834066812076032"
def inputClause7075 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,false),(80,false),(84,true),(91,false)]
theorem inputList7075 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7075 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7075 (by decide) v hb
mask_input "7075|2477164709864082480008527872|19342822337206103650074624"
def inputClause7076 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,false),(80,false),(84,true),(91,false)]
theorem inputList7076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7076 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7076 (by decide) v hb
mask_input "7076|2477164709864082479991750656|19342822337206103666851840"
def inputClause7077 : CNF.NClause := [(55,false),(24,false),(63,false),(67,true),(76,false),(80,false),(84,true),(91,false)]
theorem inputList7077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7077 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7077 (by decide) v hb
mask_input "7077|2477164571513501927186890752|19342960687786656471711744"
def inputClause7078 : CNF.NClause := [(55,false),(24,true),(63,false),(67,true),(76,false),(80,false),(84,true),(91,false)]
theorem inputList7078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7078 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7078 (by decide) v hb
mask_input "7078|2477164571513501927170113536|19342960687786656488488960"
def inputClause7079 : CNF.NClause := [(55,false),(24,false),(63,true),(67,true),(76,false),(80,false),(84,true),(91,false)]
theorem inputList7079 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7079 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7079 (by decide) v hb
mask_input "7079|2477164562290129890332114944|19342969911158693326487552"
def inputClause7080 : CNF.NClause := [(55,false),(24,true),(63,true),(67,true),(76,false),(80,false),(84,true),(91,false)]
theorem inputList7080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7080 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7080 (by decide) v hb
mask_input "7080|2477164562290129890315337728|19342969911158693343264768"
def inputClause7081 : CNF.NClause := [(55,false),(24,false),(63,false),(67,false),(76,true),(80,false),(84,true),(91,false)]
theorem inputList7081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7081 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 24) (spread_mem 24) inputClause7081 (by decide) v hb
mask_input "7081|2477089161223728602539884544|19418370977559981118717952"
end Percolation.MaskChain
