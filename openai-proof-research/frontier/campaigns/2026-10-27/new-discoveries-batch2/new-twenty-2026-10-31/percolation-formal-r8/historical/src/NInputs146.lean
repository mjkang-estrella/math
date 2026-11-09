import NInputs145
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_8508 : CNF.NClause := [(186,true),(194,true),(197,true),(205,true),(208,true),(214,false)]
theorem inp_8508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8508 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 28) (closed_mem 2 28) cl_8508 (by decide) v hb
def cl_8509 : CNF.NClause := [(186,true),(194,true),(197,true),(205,true),(208,false),(214,true)]
theorem inp_8509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8509 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 28) (closed_mem 2 28) cl_8509 (by decide) v hb
def cl_8510 : CNF.NClause := [(186,true),(194,true),(197,true),(205,false),(208,true),(214,true)]
theorem inp_8510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8510 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 28) (closed_mem 2 28) cl_8510 (by decide) v hb
def cl_8511 : CNF.NClause := [(186,true),(194,true),(197,false),(205,true),(208,true),(214,true)]
theorem inp_8511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8511 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 28) (closed_mem 2 28) cl_8511 (by decide) v hb
def cl_8512 : CNF.NClause := [(186,true),(194,false),(197,true),(205,true),(208,true),(214,true)]
theorem inp_8512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8512 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 28) (closed_mem 2 28) cl_8512 (by decide) v hb
def cl_8515 : CNF.NClause := [(186,true),(192,true),(198,true),(204,true),(210,false),(212,true)]
theorem inp_8515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8515 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 29) (closed_mem 2 29) cl_8515 (by decide) v hb
def cl_8516 : CNF.NClause := [(186,true),(192,true),(198,true),(204,false),(210,true),(212,true)]
theorem inp_8516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8516 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 29) (closed_mem 2 29) cl_8516 (by decide) v hb
def cl_8517 : CNF.NClause := [(186,true),(192,true),(198,false),(204,true),(210,true),(212,true)]
theorem inp_8517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8517 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 29) (closed_mem 2 29) cl_8517 (by decide) v hb
def cl_8518 : CNF.NClause := [(186,true),(192,false),(198,true),(204,true),(210,true),(212,true)]
theorem inp_8518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8518 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 29) (closed_mem 2 29) cl_8518 (by decide) v hb
def cl_8521 : CNF.NClause := [(186,true),(191,true),(196,true),(201,true),(206,false),(211,true)]
theorem inp_8521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8521 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 30) (closed_mem 2 30) cl_8521 (by decide) v hb
def cl_8522 : CNF.NClause := [(186,true),(191,true),(196,true),(201,false),(206,true),(211,true)]
theorem inp_8522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8522 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 30) (closed_mem 2 30) cl_8522 (by decide) v hb
def cl_8523 : CNF.NClause := [(186,true),(191,true),(196,false),(201,true),(206,true),(211,true)]
theorem inp_8523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8523 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 30) (closed_mem 2 30) cl_8523 (by decide) v hb
def cl_8524 : CNF.NClause := [(186,true),(191,false),(196,true),(201,true),(206,true),(211,true)]
theorem inp_8524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8524 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 2 30) (closed_mem 2 30) cl_8524 (by decide) v hb
def cl_8527 : CNF.NClause := [(242,true),(243,true),(244,true),(245,true),(246,false),(247,true)]
theorem inp_8527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8527 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 0) (closed_mem 3 0) cl_8527 (by decide) v hb
def cl_8528 : CNF.NClause := [(242,true),(243,true),(244,true),(245,false),(246,true),(247,true)]
theorem inp_8528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8528 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 0) (closed_mem 3 0) cl_8528 (by decide) v hb
def cl_8529 : CNF.NClause := [(242,true),(243,true),(244,false),(245,true),(246,true),(247,true)]
theorem inp_8529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8529 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 0) (closed_mem 3 0) cl_8529 (by decide) v hb
def cl_8530 : CNF.NClause := [(242,true),(243,false),(244,true),(245,true),(246,true),(247,true)]
theorem inp_8530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8530 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 0) (closed_mem 3 0) cl_8530 (by decide) v hb
def cl_8533 : CNF.NClause := [(221,true),(226,true),(231,true),(236,true),(241,false),(242,true)]
theorem inp_8533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8533 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 1) (closed_mem 3 1) cl_8533 (by decide) v hb
def cl_8534 : CNF.NClause := [(221,true),(226,true),(231,true),(236,false),(241,true),(242,true)]
theorem inp_8534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8534 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 1) (closed_mem 3 1) cl_8534 (by decide) v hb
def cl_8535 : CNF.NClause := [(221,true),(226,true),(231,false),(236,true),(241,true),(242,true)]
theorem inp_8535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8535 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 1) (closed_mem 3 1) cl_8535 (by decide) v hb
def cl_8536 : CNF.NClause := [(221,true),(226,false),(231,true),(236,true),(241,true),(242,true)]
theorem inp_8536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8536 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 1) (closed_mem 3 1) cl_8536 (by decide) v hb
def cl_8537 : CNF.NClause := [(221,false),(226,true),(231,true),(236,true),(241,true),(242,true)]
theorem inp_8537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8537 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 1) (closed_mem 3 1) cl_8537 (by decide) v hb
def cl_8539 : CNF.NClause := [(219,true),(224,true),(229,true),(234,true),(239,false),(242,true)]
theorem inp_8539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8539 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 2) (closed_mem 3 2) cl_8539 (by decide) v hb
def cl_8540 : CNF.NClause := [(219,true),(224,true),(229,true),(234,false),(239,true),(242,true)]
theorem inp_8540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8540 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 2) (closed_mem 3 2) cl_8540 (by decide) v hb
def cl_8541 : CNF.NClause := [(219,true),(224,true),(229,false),(234,true),(239,true),(242,true)]
theorem inp_8541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8541 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 2) (closed_mem 3 2) cl_8541 (by decide) v hb
def cl_8542 : CNF.NClause := [(219,true),(224,false),(229,true),(234,true),(239,true),(242,true)]
theorem inp_8542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8542 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 2) (closed_mem 3 2) cl_8542 (by decide) v hb
def cl_8543 : CNF.NClause := [(219,false),(224,true),(229,true),(234,true),(239,true),(242,true)]
theorem inp_8543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8543 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 2) (closed_mem 3 2) cl_8543 (by decide) v hb
def cl_8549 : CNF.NClause := [(220,false),(225,true),(230,true),(235,true),(240,true),(242,true)]
theorem inp_8549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8549 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 3) (closed_mem 3 3) cl_8549 (by decide) v hb
def cl_8551 : CNF.NClause := [(218,true),(223,true),(228,true),(233,true),(238,false),(242,true)]
theorem inp_8551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8551 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 4) (closed_mem 3 4) cl_8551 (by decide) v hb
def cl_8552 : CNF.NClause := [(218,true),(223,true),(228,true),(233,false),(238,true),(242,true)]
theorem inp_8552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8552 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 4) (closed_mem 3 4) cl_8552 (by decide) v hb
def cl_8553 : CNF.NClause := [(218,true),(223,true),(228,false),(233,true),(238,true),(242,true)]
theorem inp_8553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8553 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 4) (closed_mem 3 4) cl_8553 (by decide) v hb
def cl_8554 : CNF.NClause := [(218,true),(223,false),(228,true),(233,true),(238,true),(242,true)]
theorem inp_8554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8554 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 4) (closed_mem 3 4) cl_8554 (by decide) v hb
def cl_8555 : CNF.NClause := [(218,false),(223,true),(228,true),(233,true),(238,true),(242,true)]
theorem inp_8555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8555 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 4) (closed_mem 3 4) cl_8555 (by decide) v hb
def cl_8557 : CNF.NClause := [(237,true),(238,true),(239,true),(240,true),(241,false),(247,true)]
theorem inp_8557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8557 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 5) (closed_mem 3 5) cl_8557 (by decide) v hb
def cl_8558 : CNF.NClause := [(237,true),(238,true),(239,true),(240,false),(241,true),(247,true)]
theorem inp_8558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8558 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 5) (closed_mem 3 5) cl_8558 (by decide) v hb
def cl_8559 : CNF.NClause := [(237,true),(238,true),(239,false),(240,true),(241,true),(247,true)]
theorem inp_8559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8559 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 5) (closed_mem 3 5) cl_8559 (by decide) v hb
def cl_8560 : CNF.NClause := [(237,true),(238,false),(239,true),(240,true),(241,true),(247,true)]
theorem inp_8560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8560 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 5) (closed_mem 3 5) cl_8560 (by decide) v hb
def cl_8561 : CNF.NClause := [(237,false),(238,true),(239,true),(240,true),(241,true),(247,true)]
theorem inp_8561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8561 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 5) (closed_mem 3 5) cl_8561 (by decide) v hb
def cl_8562 : CNF.NClause := [(221,true),(225,true),(229,true),(233,true),(237,true),(246,false)]
theorem inp_8562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8562 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 6) (closed_mem 3 6) cl_8562 (by decide) v hb
def cl_8563 : CNF.NClause := [(221,true),(225,true),(229,true),(233,true),(237,false),(246,true)]
theorem inp_8563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8563 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 6) (closed_mem 3 6) cl_8563 (by decide) v hb
def cl_8564 : CNF.NClause := [(221,true),(225,true),(229,true),(233,false),(237,true),(246,true)]
theorem inp_8564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8564 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 6) (closed_mem 3 6) cl_8564 (by decide) v hb
def cl_8565 : CNF.NClause := [(221,true),(225,true),(229,false),(233,true),(237,true),(246,true)]
theorem inp_8565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8565 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 6) (closed_mem 3 6) cl_8565 (by decide) v hb
def cl_8566 : CNF.NClause := [(221,true),(225,false),(229,true),(233,true),(237,true),(246,true)]
theorem inp_8566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8566 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 6) (closed_mem 3 6) cl_8566 (by decide) v hb
def cl_8569 : CNF.NClause := [(219,true),(226,true),(228,true),(235,true),(237,false),(244,true)]
theorem inp_8569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8569 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 7) (closed_mem 3 7) cl_8569 (by decide) v hb
def cl_8571 : CNF.NClause := [(219,true),(226,true),(228,false),(235,true),(237,true),(244,true)]
theorem inp_8571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8571 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 7) (closed_mem 3 7) cl_8571 (by decide) v hb
def cl_8572 : CNF.NClause := [(219,true),(226,false),(228,true),(235,true),(237,true),(244,true)]
theorem inp_8572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8572 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_8572 v hb
def cl_8573 : CNF.NClause := [(219,false),(226,true),(228,true),(235,true),(237,true),(244,true)]
theorem inp_8573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8573 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 7) (closed_mem 3 7) cl_8573 (by decide) v hb
def cl_8579 : CNF.NClause := [(220,false),(223,true),(231,true),(234,true),(237,true),(245,true)]
theorem inp_8579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8579 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 8) (closed_mem 3 8) cl_8579 (by decide) v hb
def cl_8580 : CNF.NClause := [(218,true),(224,true),(230,true),(236,true),(237,true),(243,false)]
theorem inp_8580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8580 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 9) (closed_mem 3 9) cl_8580 (by decide) v hb
def cl_8581 : CNF.NClause := [(218,true),(224,true),(230,true),(236,true),(237,false),(243,true)]
theorem inp_8581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8581 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 3 9) (closed_mem 3 9) cl_8581 (by decide) v hb
end Percolation.NReplay
