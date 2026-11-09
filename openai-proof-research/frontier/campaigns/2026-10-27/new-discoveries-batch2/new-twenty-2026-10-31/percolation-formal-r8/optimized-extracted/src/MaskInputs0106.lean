import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause7780 : CNF.NClause := [(60,false),(29,true),(62,true),(68,false),(74,false),(80,false),(86,true),(88,true)]
theorem inputList7780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7780 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7780 (by decide) v hb
mask_input "7780|1228111586372791715233792|386856266888367354870235136"
def inputClause7781 : CNF.NClause := [(60,false),(29,false),(62,false),(68,true),(74,false),(80,false),(86,true),(88,true)]
theorem inputList7781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7781 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7781 (by decide) v hb
mask_input "7781|1227821050153631326666752|386856557424586515258802176"
def inputClause7782 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(74,false),(80,false),(86,true),(88,true)]
theorem inputList7782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7782 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7782 (by decide) v hb
mask_input "7782|1227821050153630789795840|386856557424586515795673088"
def inputClause7783 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(74,false),(80,false),(86,true),(88,true)]
theorem inputList7783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7783 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7783 (by decide) v hb
mask_input "7783|1227816438467612899278848|386856562036272533686190080"
def inputClause7784 : CNF.NClause := [(60,false),(29,true),(62,true),(68,true),(74,false),(80,false),(86,true),(88,true)]
theorem inputList7784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7784 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7784 (by decide) v hb
mask_input "7784|1227816438467612362407936|386856562036272534223060992"
def inputClause7785 : CNF.NClause := [(60,false),(29,false),(62,false),(68,false),(74,true),(80,false),(86,true),(88,true)]
theorem inputList7785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7785 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7785 (by decide) v hb
mask_input "7785|1209226732127332098637824|386875151742612814486831104"
def inputClause7786 : CNF.NClause := [(60,false),(29,true),(62,false),(68,false),(74,true),(80,false),(86,true),(88,true)]
theorem inputList7786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7786 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7786 (by decide) v hb
mask_input "7786|1209226732127331561766912|386875151742612815023702016"
def inputClause7787 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,true),(80,false),(86,true),(88,true)]
theorem inputList7787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7787 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7787 (by decide) v hb
mask_input "7787|1209222120441313671249920|386875156354298832914219008"
def inputClause7788 : CNF.NClause := [(60,false),(29,true),(62,true),(68,false),(74,true),(80,false),(86,true),(88,true)]
theorem inputList7788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7788 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7788 (by decide) v hb
mask_input "7788|1209222120441313134379008|386875156354298833451089920"
def inputClause7789 : CNF.NClause := [(60,false),(29,false),(62,false),(68,true),(74,true),(80,false),(86,true),(88,true)]
theorem inputList7789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7789 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7789 (by decide) v hb
mask_input "7789|1208931584222152745811968|386875446890517993839656960"
def inputClause7790 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(74,true),(80,false),(86,true),(88,true)]
theorem inputList7790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7790 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7790 (by decide) v hb
mask_input "7790|1208931584222152208941056|386875446890517994376527872"
def inputClause7791 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(74,true),(80,false),(86,true),(88,true)]
theorem inputList7791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7791 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7791 (by decide) v hb
mask_input "7791|1208926972536134318424064|386875451502204012267044864"
def inputClause7792 : CNF.NClause := [(60,false),(29,true),(62,true),(68,true),(74,true),(80,false),(86,true),(88,true)]
theorem inputList7792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7792 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7792 (by decide) v hb
mask_input "7792|1208926972536133781553152|386875451502204012803915776"
def inputClause7793 : CNF.NClause := [(60,false),(29,false),(62,false),(68,false),(74,false),(80,true),(86,true),(88,true)]
theorem inputList7793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7793 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7793 (by decide) v hb
mask_input "7793|19190378444181504786432|388065188096295965080682496"
def inputClause7794 : CNF.NClause := [(60,false),(29,true),(62,false),(68,false),(74,false),(80,true),(86,true),(88,true)]
theorem inputList7794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7794 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7794 (by decide) v hb
mask_input "7794|19190378444180967915520|388065188096295965617553408"
def inputClause7795 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,false),(80,true),(86,true),(88,true)]
theorem inputList7795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7795 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7795 (by decide) v hb
mask_input "7795|19185766758163077398528|388065192707981983508070400"
def inputClause7796 : CNF.NClause := [(60,false),(29,true),(62,true),(68,false),(74,false),(80,true),(86,true),(88,true)]
theorem inputList7796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7796 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7796 (by decide) v hb
mask_input "7796|19185766758162540527616|388065192707981984044941312"
def inputClause7797 : CNF.NClause := [(60,false),(29,false),(62,false),(68,true),(74,false),(80,true),(86,true),(88,true)]
theorem inputList7797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7797 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7797 (by decide) v hb
mask_input "7797|18895230539002151960576|388065483244201144433508352"
def inputClause7798 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(74,false),(80,true),(86,true),(88,true)]
theorem inputList7798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7798 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7798 (by decide) v hb
mask_input "7798|18895230539001615089664|388065483244201144970379264"
def inputClause7799 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(74,false),(80,true),(86,true),(88,true)]
theorem inputList7799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7799 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7799 (by decide) v hb
mask_input "7799|18890618852983724572672|388065487855887162860896256"
def inputClause7800 : CNF.NClause := [(60,false),(29,true),(62,true),(68,true),(74,false),(80,true),(86,true),(88,true)]
theorem inputList7800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7800 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7800 (by decide) v hb
mask_input "7800|18890618852983187701760|388065487855887163397767168"
def inputClause7801 : CNF.NClause := [(60,false),(29,false),(62,false),(68,false),(74,true),(80,true),(86,true),(88,true)]
theorem inputList7801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7801 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7801 (by decide) v hb
mask_input "7801|300912512702923931648|388084077562227443661537280"
def inputClause7802 : CNF.NClause := [(60,false),(29,true),(62,false),(68,false),(74,true),(80,true),(86,true),(88,true)]
theorem inputList7802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7802 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7802 (by decide) v hb
mask_input "7802|300912512702387060736|388084077562227444198408192"
def inputClause7803 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,true),(80,true),(86,true),(88,true)]
theorem inputList7803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7803 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7803 (by decide) v hb
mask_input "7803|296300826684496543744|388084082173913462088925184"
def inputClause7804 : CNF.NClause := [(60,false),(29,true),(62,true),(68,false),(74,true),(80,true),(86,true),(88,true)]
theorem inputList7804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7804 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7804 (by decide) v hb
mask_input "7804|296300826683959672832|388084082173913462625796096"
def inputClause7805 : CNF.NClause := [(60,false),(29,false),(62,false),(68,true),(74,true),(80,true),(86,true),(88,true)]
theorem inputList7805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7805 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7805 (by decide) v hb
mask_input "7805|5764607523571105792|388084372710132623014363136"
def inputClause7806 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(74,true),(80,true),(86,true),(88,true)]
theorem inputList7806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7806 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7806 (by decide) v hb
mask_input "7806|5764607523034234880|388084372710132623551234048"
def inputClause7807 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(74,true),(80,true),(86,true),(88,true)]
theorem inputList7807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7807 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7807 (by decide) v hb
mask_input "7807|1152921505143717888|388084377321818641441751040"
def inputClause7808 : CNF.NClause := [(60,false),(29,true),(62,true),(68,true),(74,true),(80,true),(86,true),(88,true)]
theorem inputList7808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7808 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) inputClause7808 (by decide) v hb
mask_input "7808|1152921504606846976|388084377321818641978621952"
def inputClause7810 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,false),(77,false),(82,false),(87,false)]
theorem inputList7810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7810 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7810 (by decide) v hb
mask_input "7810|159734200774547366670761984|1073741824"
def inputClause7812 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,false),(77,false),(82,false),(87,false)]
theorem inputList7812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7812 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7812 (by decide) v hb
mask_input "7812|159734196162861348243374080|4611686019501129728"
def inputClause7814 : CNF.NClause := [(61,false),(30,true),(62,false),(67,true),(72,false),(77,false),(82,false),(87,false)]
theorem inputList7814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7814 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7814 (by decide) v hb
mask_input "7814|159734053200594776994349056|147573952590750154752"
def inputClause7816 : CNF.NClause := [(61,false),(30,true),(62,true),(67,true),(72,false),(77,false),(82,false),(87,false)]
theorem inputList7816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7816 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7816 (by decide) v hb
mask_input "7816|159734048588908758566961152|152185638609177542656"
def inputClause7818 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,true),(77,false),(82,false),(87,false)]
theorem inputList7818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7818 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7818 (by decide) v hb
mask_input "7818|159729478408064497025548288|4722366482870718955520"
def inputClause7820 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,true),(77,false),(82,false),(87,false)]
theorem inputList7820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7820 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7820 (by decide) v hb
mask_input "7820|159729473796378478598160384|4726978168889146343424"
def inputClause7822 : CNF.NClause := [(61,false),(30,true),(62,false),(67,true),(72,true),(77,false),(82,false),(87,false)]
theorem inputList7822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7822 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7822 (by decide) v hb
mask_input "7822|159729330834111907349135360|4869940435460395368448"
def inputClause7824 : CNF.NClause := [(61,false),(30,true),(62,true),(67,true),(72,true),(77,false),(82,false),(87,false)]
theorem inputList7824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7824 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7824 (by decide) v hb
mask_input "7824|159729326222425888921747456|4874552121478822756352"
def inputClause7826 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,false),(77,true),(82,false),(87,false)]
theorem inputList7826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7826 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7826 (by decide) v hb
mask_input "7826|159583085047095538023923712|151115727451829720580096"
def inputClause7828 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,false),(77,true),(82,false),(87,false)]
theorem inputList7828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7828 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7828 (by decide) v hb
mask_input "7828|159583080435409519596535808|151120339137848147968000"
def inputClause7830 : CNF.NClause := [(61,false),(30,true),(62,false),(67,true),(72,false),(77,true),(82,false),(87,false)]
theorem inputList7830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7830 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7830 (by decide) v hb
mask_input "7830|159582937473142948347510784|151263301404419396993024"
end Percolation.MaskChain
