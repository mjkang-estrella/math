import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause2548 : CNF.NClause := [(101,true),(34,true),(37,true),(45,false),(48,false),(51,true),(59,true)]
theorem inputList2548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2548 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2548 (by decide) v hb
mask_input "2548|316659348799488|2535301200457037515700142342144"
def inputClause2549 : CNF.NClause := [(101,true),(34,false),(37,false),(45,true),(48,false),(51,true),(59,true)]
theorem inputList2549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2549 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2549 (by decide) v hb
mask_input "2549|281629595533312|2535301200457037550729895608320"
def inputClause2550 : CNF.NClause := [(101,true),(34,true),(37,false),(45,true),(48,false),(51,true),(59,true)]
theorem inputList2550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2550 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2550 (by decide) v hb
mask_input "2550|281612415664128|2535301200457037550747075477504"
def inputClause2551 : CNF.NClause := [(101,true),(34,false),(37,true),(45,true),(48,false),(51,true),(59,true)]
theorem inputList2551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2551 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2551 (by decide) v hb
mask_input "2551|281492156579840|2535301200457037550867334561792"
def inputClause2553 : CNF.NClause := [(101,true),(34,false),(37,false),(45,false),(48,true),(51,true),(59,true)]
theorem inputList2553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2553 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2553 (by decide) v hb
mask_input "2553|35338990911488|2535301200457037797020500230144"
def inputClause2554 : CNF.NClause := [(101,true),(34,true),(37,false),(45,false),(48,true),(51,true),(59,true)]
theorem inputList2554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2554 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2554 (by decide) v hb
mask_input "2554|35321811042304|2535301200457037797037680099328"
def inputClause2555 : CNF.NClause := [(101,true),(34,false),(37,true),(45,false),(48,true),(51,true),(59,true)]
theorem inputList2555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2555 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2555 (by decide) v hb
mask_input "2555|35201551958016|2535301200457037797157939183616"
def inputClause2557 : CNF.NClause := [(101,true),(34,false),(37,false),(45,true),(48,true),(51,true),(59,true)]
theorem inputList2557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2557 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2557 (by decide) v hb
mask_input "2557|154618822656|2535301200457037832204872318976"
def inputClause2560 : CNF.NClause := [(101,false),(34,true),(37,true),(45,true),(48,true),(51,true),(59,true)]
theorem inputList2560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2560 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 8) 8) (activationX_mem 8) inputClause2560 (by decide) v hb
mask_input "2560|2535301200456458802993406410752|579029366084730880"
def inputClause2561 : CNF.NClause := [(102,true),(32,false),(38,false),(44,false),(50,false),(51,false),(57,false)]
theorem inputList2561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2561 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2561 (by decide) v hb
mask_input "2561|147510759155302400|5070602400912917605986812821504"
def inputClause2562 : CNF.NClause := [(102,true),(32,true),(38,false),(44,false),(50,false),(51,false),(57,false)]
theorem inputList2562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2562 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2562 (by decide) v hb
mask_input "2562|147510754860335104|5070602400912917605991107788800"
def inputClause2563 : CNF.NClause := [(102,true),(32,false),(38,true),(44,false),(50,false),(51,false),(57,false)]
theorem inputList2563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2563 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2563 (by decide) v hb
mask_input "2563|147510484277395456|5070602400912917606261690728448"
def inputClause2564 : CNF.NClause := [(102,true),(32,true),(38,true),(44,false),(50,false),(51,false),(57,false)]
theorem inputList2564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2564 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2564 (by decide) v hb
mask_input "2564|147510479982428160|5070602400912917606265985695744"
def inputClause2565 : CNF.NClause := [(102,true),(32,false),(38,false),(44,true),(50,false),(51,false),(57,false)]
theorem inputList2565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2565 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2565 (by decide) v hb
mask_input "2565|147493166969257984|5070602400912917623578998865920"
def inputClause2566 : CNF.NClause := [(102,true),(32,true),(38,false),(44,true),(50,false),(51,false),(57,false)]
theorem inputList2566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2566 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2566 (by decide) v hb
mask_input "2566|147493162674290688|5070602400912917623583293833216"
def inputClause2567 : CNF.NClause := [(102,true),(32,false),(38,true),(44,true),(50,false),(51,false),(57,false)]
theorem inputList2567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2567 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2567 (by decide) v hb
mask_input "2567|147492892091351040|5070602400912917623853876772864"
def inputClause2568 : CNF.NClause := [(102,true),(32,true),(38,true),(44,true),(50,false),(51,false),(57,false)]
theorem inputList2568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2568 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2568 (by decide) v hb
mask_input "2568|147492887796383744|5070602400912917623858171740160"
def inputClause2569 : CNF.NClause := [(102,true),(32,false),(38,false),(44,false),(50,true),(51,false),(57,false)]
theorem inputList2569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2569 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2569 (by decide) v hb
mask_input "2569|146384859248459776|5070602400912918731886719664128"
def inputClause2570 : CNF.NClause := [(102,true),(32,true),(38,false),(44,false),(50,true),(51,false),(57,false)]
theorem inputList2570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2570 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2570 (by decide) v hb
mask_input "2570|146384854953492480|5070602400912918731891014631424"
def inputClause2571 : CNF.NClause := [(102,true),(32,false),(38,true),(44,false),(50,true),(51,false),(57,false)]
theorem inputList2571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2571 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2571 (by decide) v hb
mask_input "2571|146384584370552832|5070602400912918732161597571072"
def inputClause2572 : CNF.NClause := [(102,true),(32,true),(38,true),(44,false),(50,true),(51,false),(57,false)]
theorem inputList2572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2572 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2572 (by decide) v hb
mask_input "2572|146384580075585536|5070602400912918732165892538368"
def inputClause2573 : CNF.NClause := [(102,true),(32,false),(38,false),(44,true),(50,true),(51,false),(57,false)]
theorem inputList2573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2573 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2573 (by decide) v hb
mask_input "2573|146367267062415360|5070602400912918749478905708544"
def inputClause2574 : CNF.NClause := [(102,true),(32,true),(38,false),(44,true),(50,true),(51,false),(57,false)]
theorem inputList2574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2574 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2574 (by decide) v hb
mask_input "2574|146367262767448064|5070602400912918749483200675840"
def inputClause2575 : CNF.NClause := [(102,true),(32,false),(38,true),(44,true),(50,true),(51,false),(57,false)]
theorem inputList2575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2575 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2575 (by decide) v hb
mask_input "2575|146366992184508416|5070602400912918749753783615488"
def inputClause2576 : CNF.NClause := [(102,true),(32,true),(38,true),(44,true),(50,true),(51,false),(57,false)]
theorem inputList2576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2576 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2576 (by decide) v hb
mask_input "2576|146366987889541120|5070602400912918749758078582784"
def inputClause2577 : CNF.NClause := [(102,true),(32,false),(38,false),(44,false),(50,false),(51,true),(57,false)]
theorem inputList2577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2577 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2577 (by decide) v hb
mask_input "2577|145258959341617152|5070602400912919857786626506752"
def inputClause2578 : CNF.NClause := [(102,true),(32,true),(38,false),(44,false),(50,false),(51,true),(57,false)]
theorem inputList2578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2578 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2578 (by decide) v hb
mask_input "2578|145258955046649856|5070602400912919857790921474048"
def inputClause2579 : CNF.NClause := [(102,true),(32,false),(38,true),(44,false),(50,false),(51,true),(57,false)]
theorem inputList2579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2579 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2579 (by decide) v hb
mask_input "2579|145258684463710208|5070602400912919858061504413696"
def inputClause2580 : CNF.NClause := [(102,true),(32,true),(38,true),(44,false),(50,false),(51,true),(57,false)]
theorem inputList2580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2580 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2580 (by decide) v hb
mask_input "2580|145258680168742912|5070602400912919858065799380992"
def inputClause2581 : CNF.NClause := [(102,true),(32,false),(38,false),(44,true),(50,false),(51,true),(57,false)]
theorem inputList2581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2581 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2581 (by decide) v hb
mask_input "2581|145241367155572736|5070602400912919875378812551168"
def inputClause2582 : CNF.NClause := [(102,true),(32,true),(38,false),(44,true),(50,false),(51,true),(57,false)]
theorem inputList2582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2582 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2582 (by decide) v hb
mask_input "2582|145241362860605440|5070602400912919875383107518464"
def inputClause2583 : CNF.NClause := [(102,true),(32,false),(38,true),(44,true),(50,false),(51,true),(57,false)]
theorem inputList2583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2583 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2583 (by decide) v hb
mask_input "2583|145241092277665792|5070602400912919875653690458112"
def inputClause2584 : CNF.NClause := [(102,true),(32,true),(38,true),(44,true),(50,false),(51,true),(57,false)]
theorem inputList2584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2584 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2584 (by decide) v hb
mask_input "2584|145241087982698496|5070602400912919875657985425408"
def inputClause2585 : CNF.NClause := [(102,true),(32,false),(38,false),(44,false),(50,true),(51,true),(57,false)]
theorem inputList2585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2585 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2585 (by decide) v hb
mask_input "2585|144133059434774528|5070602400912920983686533349376"
def inputClause2586 : CNF.NClause := [(102,true),(32,true),(38,false),(44,false),(50,true),(51,true),(57,false)]
theorem inputList2586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2586 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2586 (by decide) v hb
mask_input "2586|144133055139807232|5070602400912920983690828316672"
def inputClause2587 : CNF.NClause := [(102,true),(32,false),(38,true),(44,false),(50,true),(51,true),(57,false)]
theorem inputList2587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2587 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2587 (by decide) v hb
mask_input "2587|144132784556867584|5070602400912920983961411256320"
def inputClause2588 : CNF.NClause := [(102,true),(32,true),(38,true),(44,false),(50,true),(51,true),(57,false)]
theorem inputList2588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2588 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2588 (by decide) v hb
mask_input "2588|144132780261900288|5070602400912920983965706223616"
def inputClause2589 : CNF.NClause := [(102,true),(32,false),(38,false),(44,true),(50,true),(51,true),(57,false)]
theorem inputList2589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2589 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2589 (by decide) v hb
mask_input "2589|144115467248730112|5070602400912921001278719393792"
def inputClause2590 : CNF.NClause := [(102,true),(32,true),(38,false),(44,true),(50,true),(51,true),(57,false)]
theorem inputList2590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2590 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2590 (by decide) v hb
mask_input "2590|144115462953762816|5070602400912921001283014361088"
def inputClause2591 : CNF.NClause := [(102,true),(32,false),(38,true),(44,true),(50,true),(51,true),(57,false)]
theorem inputList2591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause2591 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 9) 9) (activationX_mem 9) inputClause2591 (by decide) v hb
mask_input "2591|144115192370823168|5070602400912921001553597300736"
end Percolation.MaskChain
