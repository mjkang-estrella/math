import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause7568 : CNF.NClause := [(59,false),(28,true),(62,true),(70,true),(73,true),(81,false),(84,false),(90,false)]
theorem inputList7568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7568 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7568 (by decide) v hb
mask_input "7568|1259700704614904352347258880|10629936272475397554176"
def inputClause7569 : CNF.NClause := [(59,false),(28,false),(62,false),(70,false),(73,false),(81,true),(84,false),(90,false)]
theorem inputList7569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7569 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7569 (by decide) v hb
mask_input "7569|1257293482911947569395400704|2417851639229258349412352"
def inputClause7570 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,false),(81,true),(84,false),(90,false)]
theorem inputList7570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7570 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7570 (by decide) v hb
mask_input "7570|1257293482911947569126965248|2417851639229258617847808"
def inputClause7571 : CNF.NClause := [(59,false),(28,false),(62,true),(70,false),(73,false),(81,true),(84,false),(90,false)]
theorem inputList7571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7571 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7571 (by decide) v hb
mask_input "7571|1257293478300261550968012800|2417856250915276776800256"
def inputClause7572 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,false),(81,true),(84,false),(90,false)]
theorem inputList7572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7572 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7572 (by decide) v hb
mask_input "7572|1257293478300261550699577344|2417856250915277045235712"
def inputClause7573 : CNF.NClause := [(59,false),(28,false),(62,false),(70,true),(73,false),(81,true),(84,false),(90,false)]
theorem inputList7573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7573 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7573 (by decide) v hb
mask_input "7573|1257292302320326851984097280|2419032230849975760715776"
def inputClause7574 : CNF.NClause := [(59,false),(28,true),(62,false),(70,true),(73,false),(81,true),(84,false),(90,false)]
theorem inputList7574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7574 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7574 (by decide) v hb
mask_input "7574|1257292302320326851715661824|2419032230849976029151232"
def inputClause7575 : CNF.NClause := [(59,false),(28,false),(62,true),(70,true),(73,false),(81,true),(84,false),(90,false)]
theorem inputList7575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7575 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7575 (by decide) v hb
mask_input "7575|1257292297708640833556709376|2419036842535994188103680"
def inputClause7576 : CNF.NClause := [(59,false),(28,true),(62,true),(70,true),(73,false),(81,true),(84,false),(90,false)]
theorem inputList7576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7576 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7576 (by decide) v hb
mask_input "7576|1257292297708640833288273920|2419036842535994456539136"
def inputClause7577 : CNF.NClause := [(59,false),(28,false),(62,false),(70,false),(73,true),(81,true),(84,false),(90,false)]
theorem inputList7577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7577 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7577 (by decide) v hb
mask_input "7577|1257284038178981830104973312|2427296372194997639839744"
def inputClause7578 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,true),(81,true),(84,false),(90,false)]
theorem inputList7578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7578 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7578 (by decide) v hb
mask_input "7578|1257284038178981829836537856|2427296372194997908275200"
def inputClause7579 : CNF.NClause := [(59,false),(28,false),(62,true),(70,false),(73,true),(81,true),(84,false),(90,false)]
theorem inputList7579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7579 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7579 (by decide) v hb
mask_input "7579|1257284033567295811677585408|2427300983881016067227648"
def inputClause7580 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,true),(81,true),(84,false),(90,false)]
theorem inputList7580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7580 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7580 (by decide) v hb
mask_input "7580|1257284033567295811409149952|2427300983881016335663104"
def inputClause7581 : CNF.NClause := [(59,false),(28,false),(62,false),(70,true),(73,true),(81,true),(84,false),(90,false)]
theorem inputList7581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7581 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7581 (by decide) v hb
mask_input "7581|1257282857587361112693669888|2428476963815715051143168"
def inputClause7582 : CNF.NClause := [(59,false),(28,true),(62,false),(70,true),(73,true),(81,true),(84,false),(90,false)]
theorem inputList7582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7582 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7582 (by decide) v hb
mask_input "7582|1257282857587361112425234432|2428476963815715319578624"
def inputClause7583 : CNF.NClause := [(59,false),(28,false),(62,true),(70,true),(73,true),(81,true),(84,false),(90,false)]
theorem inputList7583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7583 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7583 (by decide) v hb
mask_input "7583|1257282852975675094266281984|2428481575501733478531072"
def inputClause7584 : CNF.NClause := [(59,false),(28,true),(62,true),(70,true),(73,true),(81,true),(84,false),(90,false)]
theorem inputList7584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7584 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7584 (by decide) v hb
mask_input "7584|1257282852975675093997846528|2428481575501733746966528"
def inputClause7585 : CNF.NClause := [(59,false),(28,false),(62,false),(70,false),(73,false),(81,false),(84,true),(90,false)]
theorem inputList7585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7585 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7585 (by decide) v hb
mask_input "7585|1240368521437342760949514240|19342813113834066795298816"
def inputClause7586 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,false),(81,false),(84,true),(90,false)]
theorem inputList7586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7586 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7586 (by decide) v hb
mask_input "7586|1240368521437342760681078784|19342813113834067063734272"
def inputClause7587 : CNF.NClause := [(59,false),(28,false),(62,true),(70,false),(73,false),(81,false),(84,true),(90,false)]
theorem inputList7587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7587 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7587 (by decide) v hb
mask_input "7587|1240368516825656742522126336|19342817725520085222686720"
def inputClause7588 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,false),(81,false),(84,true),(90,false)]
theorem inputList7588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7588 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7588 (by decide) v hb
mask_input "7588|1240368516825656742253690880|19342817725520085491122176"
def inputClause7589 : CNF.NClause := [(59,false),(28,false),(62,false),(70,true),(73,false),(81,false),(84,true),(90,false)]
theorem inputList7589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7589 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7589 (by decide) v hb
mask_input "7589|1240367340845722043538210816|19343993705454784206602240"
def inputClause7590 : CNF.NClause := [(59,false),(28,true),(62,false),(70,true),(73,false),(81,false),(84,true),(90,false)]
theorem inputList7590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7590 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7590 (by decide) v hb
mask_input "7590|1240367340845722043269775360|19343993705454784475037696"
def inputClause7591 : CNF.NClause := [(59,false),(28,false),(62,true),(70,true),(73,false),(81,false),(84,true),(90,false)]
theorem inputList7591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7591 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7591 (by decide) v hb
mask_input "7591|1240367336234036025110822912|19343998317140802633990144"
def inputClause7592 : CNF.NClause := [(59,false),(28,true),(62,true),(70,true),(73,false),(81,false),(84,true),(90,false)]
theorem inputList7592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7592 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7592 (by decide) v hb
mask_input "7592|1240367336234036024842387456|19343998317140802902425600"
def inputClause7593 : CNF.NClause := [(59,false),(28,false),(62,false),(70,false),(73,true),(81,false),(84,true),(90,false)]
theorem inputList7593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7593 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7593 (by decide) v hb
mask_input "7593|1240359076704377021659086848|19352257846799806085726208"
def inputClause7594 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,true),(81,false),(84,true),(90,false)]
theorem inputList7594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7594 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7594 (by decide) v hb
mask_input "7594|1240359076704377021390651392|19352257846799806354161664"
def inputClause7595 : CNF.NClause := [(59,false),(28,false),(62,true),(70,false),(73,true),(81,false),(84,true),(90,false)]
theorem inputList7595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7595 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7595 (by decide) v hb
mask_input "7595|1240359072092691003231698944|19352262458485824513114112"
def inputClause7596 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,true),(81,false),(84,true),(90,false)]
theorem inputList7596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7596 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7596 (by decide) v hb
mask_input "7596|1240359072092691002963263488|19352262458485824781549568"
def inputClause7597 : CNF.NClause := [(59,false),(28,false),(62,false),(70,true),(73,true),(81,false),(84,true),(90,false)]
theorem inputList7597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7597 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7597 (by decide) v hb
mask_input "7597|1240357896112756304247783424|19353438438420523497029632"
def inputClause7598 : CNF.NClause := [(59,false),(28,true),(62,false),(70,true),(73,true),(81,false),(84,true),(90,false)]
theorem inputList7598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7598 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7598 (by decide) v hb
mask_input "7598|1240357896112756303979347968|19353438438420523765465088"
def inputClause7599 : CNF.NClause := [(59,false),(28,false),(62,true),(70,true),(73,true),(81,false),(84,true),(90,false)]
theorem inputList7599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7599 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7599 (by decide) v hb
mask_input "7599|1240357891501070285820395520|19353443050106541924417536"
def inputClause7600 : CNF.NClause := [(59,false),(28,true),(62,true),(70,true),(73,true),(81,false),(84,true),(90,false)]
theorem inputList7600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7600 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7600 (by decide) v hb
mask_input "7600|1240357891501070285551960064|19353443050106542192852992"
def inputClause7601 : CNF.NClause := [(59,false),(28,false),(62,false),(70,false),(73,false),(81,true),(84,true),(90,false)]
theorem inputList7601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7601 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7601 (by decide) v hb
mask_input "7601|1237950669798113502600101888|21760664753063325144711168"
def inputClause7602 : CNF.NClause := [(59,false),(28,true),(62,false),(70,false),(73,false),(81,true),(84,true),(90,false)]
theorem inputList7602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7602 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7602 (by decide) v hb
mask_input "7602|1237950669798113502331666432|21760664753063325413146624"
def inputClause7603 : CNF.NClause := [(59,false),(28,false),(62,true),(70,false),(73,false),(81,true),(84,true),(90,false)]
theorem inputList7603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7603 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7603 (by decide) v hb
mask_input "7603|1237950665186427484172713984|21760669364749343572099072"
def inputClause7604 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,false),(81,true),(84,true),(90,false)]
theorem inputList7604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7604 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7604 (by decide) v hb
mask_input "7604|1237950665186427483904278528|21760669364749343840534528"
def inputClause7605 : CNF.NClause := [(59,false),(28,false),(62,false),(70,true),(73,false),(81,true),(84,true),(90,false)]
theorem inputList7605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7605 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7605 (by decide) v hb
mask_input "7605|1237949489206492785188798464|21761845344684042556014592"
def inputClause7606 : CNF.NClause := [(59,false),(28,true),(62,false),(70,true),(73,false),(81,true),(84,true),(90,false)]
theorem inputList7606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7606 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7606 (by decide) v hb
mask_input "7606|1237949489206492784920363008|21761845344684042824450048"
def inputClause7607 : CNF.NClause := [(59,false),(28,false),(62,true),(70,true),(73,false),(81,true),(84,true),(90,false)]
theorem inputList7607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7607 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 28) (spread_mem 28) inputClause7607 (by decide) v hb
mask_input "7607|1237949484594806766761410560|21761849956370060983402496"
end Percolation.MaskChain
