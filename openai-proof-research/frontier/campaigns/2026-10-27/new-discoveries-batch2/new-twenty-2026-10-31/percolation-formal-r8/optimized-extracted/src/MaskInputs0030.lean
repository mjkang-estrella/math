import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause1585 : CNF.NClause := [(86,true),(1,false),(5,false),(14,false),(18,false),(22,true),(29,true)]
theorem inputList1585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1585 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1585 (by decide) v hb
mask_input "1585|278562|77371252455336267722260480"
def inputClause1586 : CNF.NClause := [(86,true),(1,true),(5,false),(14,false),(18,false),(22,true),(29,true)]
theorem inputList1586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1586 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1586 (by decide) v hb
mask_input "1586|278560|77371252455336267722260482"
def inputClause1587 : CNF.NClause := [(86,true),(1,false),(5,true),(14,false),(18,false),(22,true),(29,true)]
theorem inputList1587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1587 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1587 (by decide) v hb
mask_input "1587|278530|77371252455336267722260512"
def inputClause1588 : CNF.NClause := [(86,true),(1,true),(5,true),(14,false),(18,false),(22,true),(29,true)]
theorem inputList1588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1588 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1588 (by decide) v hb
mask_input "1588|278528|77371252455336267722260514"
def inputClause1589 : CNF.NClause := [(86,true),(1,false),(5,false),(14,true),(18,false),(22,true),(29,true)]
theorem inputList1589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1589 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1589 (by decide) v hb
mask_input "1589|262178|77371252455336267722276864"
def inputClause1590 : CNF.NClause := [(86,true),(1,true),(5,false),(14,true),(18,false),(22,true),(29,true)]
theorem inputList1590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1590 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1590 (by decide) v hb
mask_input "1590|262176|77371252455336267722276866"
def inputClause1591 : CNF.NClause := [(86,true),(1,false),(5,true),(14,true),(18,false),(22,true),(29,true)]
theorem inputList1591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1591 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1591 (by decide) v hb
mask_input "1591|262146|77371252455336267722276896"
def inputClause1593 : CNF.NClause := [(86,true),(1,false),(5,false),(14,false),(18,true),(22,true),(29,true)]
theorem inputList1593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1593 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1593 (by decide) v hb
mask_input "1593|16418|77371252455336267722522624"
def inputClause1594 : CNF.NClause := [(86,true),(1,true),(5,false),(14,false),(18,true),(22,true),(29,true)]
theorem inputList1594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1594 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1594 (by decide) v hb
mask_input "1594|16416|77371252455336267722522626"
def inputClause1595 : CNF.NClause := [(86,true),(1,false),(5,true),(14,false),(18,true),(22,true),(29,true)]
theorem inputList1595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1595 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1595 (by decide) v hb
mask_input "1595|16386|77371252455336267722522656"
def inputClause1597 : CNF.NClause := [(86,true),(1,false),(5,false),(14,true),(18,true),(22,true),(29,true)]
theorem inputList1597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1597 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 24) 24) (activationA_mem 24) inputClause1597 (by decide) v hb
mask_input "1597|34|77371252455336267722539008"
def inputClause1634 : CNF.NClause := [(87,true),(0,true),(1,false),(2,false),(3,false),(4,false),(30,true)]
theorem inputList1634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1634 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) inputClause1634 (by decide) v hb
mask_input "1634|30|154742504910672535436132353"
def inputClause1636 : CNF.NClause := [(87,true),(0,true),(1,true),(2,false),(3,false),(4,false),(30,true)]
theorem inputList1636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1636 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) inputClause1636 (by decide) v hb
mask_input "1636|28|154742504910672535436132355"
def inputClause1638 : CNF.NClause := [(87,true),(0,true),(1,false),(2,true),(3,false),(4,false),(30,true)]
theorem inputList1638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1638 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) inputClause1638 (by decide) v hb
mask_input "1638|26|154742504910672535436132357"
def inputClause1640 : CNF.NClause := [(87,true),(0,true),(1,true),(2,true),(3,false),(4,false),(30,true)]
theorem inputList1640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1640 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) inputClause1640 (by decide) v hb
mask_input "1640|24|154742504910672535436132359"
def inputClause1642 : CNF.NClause := [(87,true),(0,true),(1,false),(2,false),(3,true),(4,false),(30,true)]
theorem inputList1642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1642 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) inputClause1642 (by decide) v hb
mask_input "1642|22|154742504910672535436132361"
def inputClause1644 : CNF.NClause := [(87,true),(0,true),(1,true),(2,false),(3,true),(4,false),(30,true)]
theorem inputList1644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1644 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) inputClause1644 (by decide) v hb
mask_input "1644|20|154742504910672535436132363"
def inputClause1646 : CNF.NClause := [(87,true),(0,true),(1,false),(2,true),(3,true),(4,false),(30,true)]
theorem inputList1646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1646 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) inputClause1646 (by decide) v hb
mask_input "1646|18|154742504910672535436132365"
def inputClause1648 : CNF.NClause := [(87,false),(0,true),(1,true),(2,true),(3,true),(4,false),(30,true)]
theorem inputList1648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1648 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) inputClause1648 (by decide) v hb
mask_input "1648|154742504910672534362390544|1073741839"
def inputClause1650 : CNF.NClause := [(87,true),(0,true),(1,false),(2,false),(3,false),(4,true),(30,true)]
theorem inputList1650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1650 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) inputClause1650 (by decide) v hb
mask_input "1650|14|154742504910672535436132369"
def inputClause1652 : CNF.NClause := [(87,true),(0,true),(1,true),(2,false),(3,false),(4,true),(30,true)]
theorem inputList1652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1652 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) inputClause1652 (by decide) v hb
mask_input "1652|12|154742504910672535436132371"
def inputClause1654 : CNF.NClause := [(87,true),(0,true),(1,false),(2,true),(3,false),(4,true),(30,true)]
theorem inputList1654 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1654 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) inputClause1654 (by decide) v hb
mask_input "1654|10|154742504910672535436132373"
def inputClause1656 : CNF.NClause := [(87,false),(0,true),(1,true),(2,true),(3,false),(4,true),(30,true)]
theorem inputList1656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1656 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) inputClause1656 (by decide) v hb
mask_input "1656|154742504910672534362390536|1073741847"
def inputClause1658 : CNF.NClause := [(87,true),(0,true),(1,false),(2,false),(3,true),(4,true),(30,true)]
theorem inputList1658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1658 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) inputClause1658 (by decide) v hb
mask_input "1658|6|154742504910672535436132377"
def inputClause1660 : CNF.NClause := [(87,false),(0,true),(1,true),(2,false),(3,true),(4,true),(30,true)]
theorem inputList1660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1660 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) inputClause1660 (by decide) v hb
mask_input "1660|154742504910672534362390532|1073741851"
def inputClause1662 : CNF.NClause := [(87,false),(0,true),(1,false),(2,true),(3,true),(4,true),(30,true)]
theorem inputList1662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1662 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 25) 25) (activationA_mem 25) inputClause1662 (by decide) v hb
mask_input "1662|154742504910672534362390530|1073741853"
def inputClause1666 : CNF.NClause := [(88,true),(0,true),(9,false),(13,false),(17,false),(21,false),(29,false)]
theorem inputList1666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1666 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) inputClause1666 (by decide) v hb
mask_input "1666|539107840|309485009821345068724781057"
def inputClause1668 : CNF.NClause := [(88,true),(0,true),(9,true),(13,false),(17,false),(21,false),(29,false)]
theorem inputList1668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1668 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) inputClause1668 (by decide) v hb
mask_input "1668|539107328|309485009821345068724781569"
def inputClause1670 : CNF.NClause := [(88,true),(0,true),(9,false),(13,true),(17,false),(21,false),(29,false)]
theorem inputList1670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1670 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) inputClause1670 (by decide) v hb
mask_input "1670|539099648|309485009821345068724789249"
def inputClause1672 : CNF.NClause := [(88,true),(0,true),(9,true),(13,true),(17,false),(21,false),(29,false)]
theorem inputList1672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1672 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) inputClause1672 (by decide) v hb
mask_input "1672|539099136|309485009821345068724789761"
def inputClause1674 : CNF.NClause := [(88,true),(0,true),(9,false),(13,false),(17,true),(21,false),(29,false)]
theorem inputList1674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1674 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) inputClause1674 (by decide) v hb
mask_input "1674|538976768|309485009821345068724912129"
def inputClause1676 : CNF.NClause := [(88,true),(0,true),(9,true),(13,false),(17,true),(21,false),(29,false)]
theorem inputList1676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1676 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) inputClause1676 (by decide) v hb
mask_input "1676|538976256|309485009821345068724912641"
def inputClause1678 : CNF.NClause := [(88,true),(0,true),(9,false),(13,true),(17,true),(21,false),(29,false)]
theorem inputList1678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1678 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) inputClause1678 (by decide) v hb
mask_input "1678|538968576|309485009821345068724920321"
def inputClause1680 : CNF.NClause := [(88,true),(0,true),(9,true),(13,true),(17,true),(21,false),(29,false)]
theorem inputList1680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1680 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) inputClause1680 (by decide) v hb
mask_input "1680|538968064|309485009821345068724920833"
def inputClause1682 : CNF.NClause := [(88,true),(0,true),(9,false),(13,false),(17,false),(21,true),(29,false)]
theorem inputList1682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1682 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) inputClause1682 (by decide) v hb
mask_input "1682|537010688|309485009821345068726878209"
def inputClause1684 : CNF.NClause := [(88,true),(0,true),(9,true),(13,false),(17,false),(21,true),(29,false)]
theorem inputList1684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1684 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) inputClause1684 (by decide) v hb
mask_input "1684|537010176|309485009821345068726878721"
def inputClause1686 : CNF.NClause := [(88,true),(0,true),(9,false),(13,true),(17,false),(21,true),(29,false)]
theorem inputList1686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1686 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) inputClause1686 (by decide) v hb
mask_input "1686|537002496|309485009821345068726886401"
def inputClause1688 : CNF.NClause := [(88,true),(0,true),(9,true),(13,true),(17,false),(21,true),(29,false)]
theorem inputList1688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1688 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) inputClause1688 (by decide) v hb
mask_input "1688|537001984|309485009821345068726886913"
def inputClause1690 : CNF.NClause := [(88,true),(0,true),(9,false),(13,false),(17,true),(21,true),(29,false)]
theorem inputList1690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1690 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) inputClause1690 (by decide) v hb
mask_input "1690|536879616|309485009821345068727009281"
def inputClause1692 : CNF.NClause := [(88,true),(0,true),(9,true),(13,false),(17,true),(21,true),(29,false)]
theorem inputList1692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1692 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) inputClause1692 (by decide) v hb
mask_input "1692|536879104|309485009821345068727009793"
end Percolation.MaskChain
