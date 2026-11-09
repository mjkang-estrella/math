import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause2593 : CNF.NClause := [(102,true),(32,false),(38,false),(44,false),(50,false),(51,false),(57,true)]
theorem inputList2593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2593 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2593 (by decide) v hb
mask_input "2593|3395571079446528|5070602400913061721174888677376"
def inputClause2594 : CNF.NClause := [(102,true),(32,true),(38,false),(44,false),(50,false),(51,false),(57,true)]
theorem inputList2594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2594 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2594 (by decide) v hb
mask_input "2594|3395566784479232|5070602400913061721179183644672"
def inputClause2595 : CNF.NClause := [(102,true),(32,false),(38,true),(44,false),(50,false),(51,false),(57,true)]
theorem inputList2595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2595 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2595 (by decide) v hb
mask_input "2595|3395296201539584|5070602400913061721449766584320"
def inputClause2596 : CNF.NClause := [(102,true),(32,true),(38,true),(44,false),(50,false),(51,false),(57,true)]
theorem inputList2596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2596 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2596 (by decide) v hb
mask_input "2596|3395291906572288|5070602400913061721454061551616"
def inputClause2597 : CNF.NClause := [(102,true),(32,false),(38,false),(44,true),(50,false),(51,false),(57,true)]
theorem inputList2597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2597 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2597 (by decide) v hb
mask_input "2597|3377978893402112|5070602400913061738767074721792"
def inputClause2598 : CNF.NClause := [(102,true),(32,true),(38,false),(44,true),(50,false),(51,false),(57,true)]
theorem inputList2598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2598 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2598 (by decide) v hb
mask_input "2598|3377974598434816|5070602400913061738771369689088"
def inputClause2599 : CNF.NClause := [(102,true),(32,false),(38,true),(44,true),(50,false),(51,false),(57,true)]
theorem inputList2599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2599 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2599 (by decide) v hb
mask_input "2599|3377704015495168|5070602400913061739041952628736"
def inputClause2600 : CNF.NClause := [(102,true),(32,true),(38,true),(44,true),(50,false),(51,false),(57,true)]
theorem inputList2600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2600 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2600 (by decide) v hb
mask_input "2600|3377699720527872|5070602400913061739046247596032"
def inputClause2601 : CNF.NClause := [(102,true),(32,false),(38,false),(44,false),(50,true),(51,false),(57,true)]
theorem inputList2601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2601 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2601 (by decide) v hb
mask_input "2601|2269671172603904|5070602400913062847074795520000"
def inputClause2602 : CNF.NClause := [(102,true),(32,true),(38,false),(44,false),(50,true),(51,false),(57,true)]
theorem inputList2602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2602 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2602 (by decide) v hb
mask_input "2602|2269666877636608|5070602400913062847079090487296"
def inputClause2603 : CNF.NClause := [(102,true),(32,false),(38,true),(44,false),(50,true),(51,false),(57,true)]
theorem inputList2603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2603 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2603 (by decide) v hb
mask_input "2603|2269396294696960|5070602400913062847349673426944"
def inputClause2604 : CNF.NClause := [(102,true),(32,true),(38,true),(44,false),(50,true),(51,false),(57,true)]
theorem inputList2604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2604 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2604 (by decide) v hb
mask_input "2604|2269391999729664|5070602400913062847353968394240"
def inputClause2605 : CNF.NClause := [(102,true),(32,false),(38,false),(44,true),(50,true),(51,false),(57,true)]
theorem inputList2605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2605 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2605 (by decide) v hb
mask_input "2605|2252078986559488|5070602400913062864666981564416"
def inputClause2606 : CNF.NClause := [(102,true),(32,true),(38,false),(44,true),(50,true),(51,false),(57,true)]
theorem inputList2606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2606 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2606 (by decide) v hb
mask_input "2606|2252074691592192|5070602400913062864671276531712"
def inputClause2607 : CNF.NClause := [(102,true),(32,false),(38,true),(44,true),(50,true),(51,false),(57,true)]
theorem inputList2607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2607 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2607 (by decide) v hb
mask_input "2607|2251804108652544|5070602400913062864941859471360"
def inputClause2609 : CNF.NClause := [(102,true),(32,false),(38,false),(44,false),(50,false),(51,true),(57,true)]
theorem inputList2609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2609 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2609 (by decide) v hb
mask_input "2609|1143771265761280|5070602400913063972974702362624"
def inputClause2610 : CNF.NClause := [(102,true),(32,true),(38,false),(44,false),(50,false),(51,true),(57,true)]
theorem inputList2610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2610 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2610 (by decide) v hb
mask_input "2610|1143766970793984|5070602400913063972978997329920"
def inputClause2611 : CNF.NClause := [(102,true),(32,false),(38,true),(44,false),(50,false),(51,true),(57,true)]
theorem inputList2611 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2611 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2611 (by decide) v hb
mask_input "2611|1143496387854336|5070602400913063973249580269568"
def inputClause2612 : CNF.NClause := [(102,true),(32,true),(38,true),(44,false),(50,false),(51,true),(57,true)]
theorem inputList2612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2612 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2612 (by decide) v hb
mask_input "2612|1143492092887040|5070602400913063973253875236864"
def inputClause2613 : CNF.NClause := [(102,true),(32,false),(38,false),(44,true),(50,false),(51,true),(57,true)]
theorem inputList2613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2613 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2613 (by decide) v hb
mask_input "2613|1126179079716864|5070602400913063990566888407040"
def inputClause2614 : CNF.NClause := [(102,true),(32,true),(38,false),(44,true),(50,false),(51,true),(57,true)]
theorem inputList2614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2614 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2614 (by decide) v hb
mask_input "2614|1126174784749568|5070602400913063990571183374336"
def inputClause2615 : CNF.NClause := [(102,true),(32,false),(38,true),(44,true),(50,false),(51,true),(57,true)]
theorem inputList2615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2615 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2615 (by decide) v hb
mask_input "2615|1125904201809920|5070602400913063990841766313984"
def inputClause2617 : CNF.NClause := [(102,true),(32,false),(38,false),(44,false),(50,true),(51,true),(57,true)]
theorem inputList2617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2617 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2617 (by decide) v hb
mask_input "2617|17871358918656|5070602400913065098874609205248"
def inputClause2618 : CNF.NClause := [(102,true),(32,true),(38,false),(44,false),(50,true),(51,true),(57,true)]
theorem inputList2618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2618 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2618 (by decide) v hb
mask_input "2618|17867063951360|5070602400913065098878904172544"
def inputClause2619 : CNF.NClause := [(102,true),(32,false),(38,true),(44,false),(50,true),(51,true),(57,true)]
theorem inputList2619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2619 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2619 (by decide) v hb
mask_input "2619|17596481011712|5070602400913065099149487112192"
def inputClause2621 : CNF.NClause := [(102,true),(32,false),(38,false),(44,true),(50,true),(51,true),(57,true)]
theorem inputList2621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2621 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2621 (by decide) v hb
mask_input "2621|279172874240|5070602400913065116466795249664"
def inputClause2623 : CNF.NClause := [(102,false),(32,false),(38,true),(44,true),(50,true),(51,true),(57,true)]
theorem inputList2623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2623 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2623 (by decide) v hb
mask_input "2623|5070602400912917605991107788800|147510754860335104"
def inputClause2624 : CNF.NClause := [(102,false),(32,true),(38,true),(44,true),(50,true),(51,true),(57,true)]
theorem inputList2624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2624 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2624 (by decide) v hb
mask_input "2624|5070602400912917605986812821504|147510759155302400"
def inputClause2625 : CNF.NClause := [(103,true),(41,false),(42,false),(43,false),(44,false),(45,false),(61,false)]
theorem inputList2625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2625 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2625 (by decide) v hb
mask_input "2625|2305911178934616064|10141204801825835211973625643008"
def inputClause2626 : CNF.NClause := [(103,true),(41,true),(42,false),(43,false),(44,false),(45,false),(61,false)]
theorem inputList2626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2626 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2626 (by decide) v hb
mask_input "2626|2305908979911360512|10141204801825835214172648898560"
def inputClause2627 : CNF.NClause := [(103,true),(41,false),(42,true),(43,false),(44,false),(45,false),(61,false)]
theorem inputList2627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2627 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2627 (by decide) v hb
mask_input "2627|2305906780888104960|10141204801825835216371672154112"
def inputClause2628 : CNF.NClause := [(103,true),(41,true),(42,true),(43,false),(44,false),(45,false),(61,false)]
theorem inputList2628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2628 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2628 (by decide) v hb
mask_input "2628|2305904581864849408|10141204801825835218570695409664"
def inputClause2629 : CNF.NClause := [(103,true),(41,false),(42,false),(43,true),(44,false),(45,false),(61,false)]
theorem inputList2629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2629 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2629 (by decide) v hb
mask_input "2629|2305902382841593856|10141204801825835220769718665216"
def inputClause2630 : CNF.NClause := [(103,true),(41,true),(42,false),(43,true),(44,false),(45,false),(61,false)]
theorem inputList2630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2630 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2630 (by decide) v hb
mask_input "2630|2305900183818338304|10141204801825835222968741920768"
def inputClause2631 : CNF.NClause := [(103,true),(41,false),(42,true),(43,true),(44,false),(45,false),(61,false)]
theorem inputList2631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2631 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2631 (by decide) v hb
mask_input "2631|2305897984795082752|10141204801825835225167765176320"
def inputClause2632 : CNF.NClause := [(103,true),(41,true),(42,true),(43,true),(44,false),(45,false),(61,false)]
theorem inputList2632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2632 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2632 (by decide) v hb
mask_input "2632|2305895785771827200|10141204801825835227366788431872"
def inputClause2633 : CNF.NClause := [(103,true),(41,false),(42,false),(43,false),(44,true),(45,false),(61,false)]
theorem inputList2633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2633 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2633 (by decide) v hb
mask_input "2633|2305893586748571648|10141204801825835229565811687424"
def inputClause2634 : CNF.NClause := [(103,true),(41,true),(42,false),(43,false),(44,true),(45,false),(61,false)]
theorem inputList2634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2634 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2634 (by decide) v hb
mask_input "2634|2305891387725316096|10141204801825835231764834942976"
def inputClause2635 : CNF.NClause := [(103,true),(41,false),(42,true),(43,false),(44,true),(45,false),(61,false)]
theorem inputList2635 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2635 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2635 (by decide) v hb
mask_input "2635|2305889188702060544|10141204801825835233963858198528"
def inputClause2636 : CNF.NClause := [(103,true),(41,true),(42,true),(43,false),(44,true),(45,false),(61,false)]
theorem inputList2636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2636 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) inputClause2636 (by decide) v hb
mask_input "2636|2305886989678804992|10141204801825835236162881454080"
end Percolation.MaskChain
