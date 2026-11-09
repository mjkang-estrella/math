import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause1694 : CNF.NClause := [(88,true),(0,true),(9,false),(13,true),(17,true),(21,true),(29,false)]
theorem inputList1694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1694 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) inputClause1694 (by decide) v hb
mask_input "1694|536871424|309485009821345068727017473"
def inputClause1696 : CNF.NClause := [(88,false),(0,true),(9,true),(13,true),(17,true),(21,true),(29,false)]
theorem inputList1696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1696 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) inputClause1696 (by decide) v hb
mask_input "1696|309485009821345069261651968|2236929"
def inputClause1698 : CNF.NClause := [(88,true),(0,true),(9,false),(13,false),(17,false),(21,false),(29,true)]
theorem inputList1698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1698 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) inputClause1698 (by decide) v hb
mask_input "1698|2236928|309485009821345069261651969"
def inputClause1700 : CNF.NClause := [(88,true),(0,true),(9,true),(13,false),(17,false),(21,false),(29,true)]
theorem inputList1700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1700 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) inputClause1700 (by decide) v hb
mask_input "1700|2236416|309485009821345069261652481"
def inputClause1702 : CNF.NClause := [(88,true),(0,true),(9,false),(13,true),(17,false),(21,false),(29,true)]
theorem inputList1702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1702 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) inputClause1702 (by decide) v hb
mask_input "1702|2228736|309485009821345069261660161"
def inputClause1704 : CNF.NClause := [(88,true),(0,true),(9,true),(13,true),(17,false),(21,false),(29,true)]
theorem inputList1704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1704 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) inputClause1704 (by decide) v hb
mask_input "1704|2228224|309485009821345069261660673"
def inputClause1706 : CNF.NClause := [(88,true),(0,true),(9,false),(13,false),(17,true),(21,false),(29,true)]
theorem inputList1706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1706 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) inputClause1706 (by decide) v hb
mask_input "1706|2105856|309485009821345069261783041"
def inputClause1708 : CNF.NClause := [(88,true),(0,true),(9,true),(13,false),(17,true),(21,false),(29,true)]
theorem inputList1708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1708 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) inputClause1708 (by decide) v hb
mask_input "1708|2105344|309485009821345069261783553"
def inputClause1710 : CNF.NClause := [(88,true),(0,true),(9,false),(13,true),(17,true),(21,false),(29,true)]
theorem inputList1710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1710 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) inputClause1710 (by decide) v hb
mask_input "1710|2097664|309485009821345069261791233"
def inputClause1712 : CNF.NClause := [(88,false),(0,true),(9,true),(13,true),(17,true),(21,false),(29,true)]
theorem inputList1712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1712 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) inputClause1712 (by decide) v hb
mask_input "1712|309485009821345068726878208|537010689"
def inputClause1714 : CNF.NClause := [(88,true),(0,true),(9,false),(13,false),(17,false),(21,true),(29,true)]
theorem inputList1714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1714 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) inputClause1714 (by decide) v hb
mask_input "1714|139776|309485009821345069263749121"
def inputClause1716 : CNF.NClause := [(88,true),(0,true),(9,true),(13,false),(17,false),(21,true),(29,true)]
theorem inputList1716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1716 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) inputClause1716 (by decide) v hb
mask_input "1716|139264|309485009821345069263749633"
def inputClause1718 : CNF.NClause := [(88,true),(0,true),(9,false),(13,true),(17,false),(21,true),(29,true)]
theorem inputList1718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1718 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) inputClause1718 (by decide) v hb
mask_input "1718|131584|309485009821345069263757313"
def inputClause1720 : CNF.NClause := [(88,false),(0,true),(9,true),(13,true),(17,false),(21,true),(29,true)]
theorem inputList1720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1720 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) inputClause1720 (by decide) v hb
mask_input "1720|309485009821345068724912128|538976769"
def inputClause1722 : CNF.NClause := [(88,true),(0,true),(9,false),(13,false),(17,true),(21,true),(29,true)]
theorem inputList1722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1722 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) inputClause1722 (by decide) v hb
mask_input "1722|8704|309485009821345069263880193"
def inputClause1724 : CNF.NClause := [(88,false),(0,true),(9,true),(13,false),(17,true),(21,true),(29,true)]
theorem inputList1724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1724 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) inputClause1724 (by decide) v hb
mask_input "1724|309485009821345068724789248|539099649"
def inputClause1726 : CNF.NClause := [(88,false),(0,true),(9,false),(13,true),(17,true),(21,true),(29,true)]
theorem inputList1726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1726 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 26) 26) (activationA_mem 26) inputClause1726 (by decide) v hb
mask_input "1726|309485009821345068724781568|539107329"
def inputClause1730 : CNF.NClause := [(89,true),(0,true),(7,false),(14,false),(16,false),(23,false),(27,false)]
theorem inputList1730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1730 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) inputClause1730 (by decide) v hb
mask_input "1730|142688384|618970019642690137449562113"
def inputClause1732 : CNF.NClause := [(89,true),(0,true),(7,true),(14,false),(16,false),(23,false),(27,false)]
theorem inputList1732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1732 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) inputClause1732 (by decide) v hb
mask_input "1732|142688256|618970019642690137449562241"
def inputClause1734 : CNF.NClause := [(89,true),(0,true),(7,false),(14,true),(16,false),(23,false),(27,false)]
theorem inputList1734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1734 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) inputClause1734 (by decide) v hb
mask_input "1734|142672000|618970019642690137449578497"
def inputClause1736 : CNF.NClause := [(89,true),(0,true),(7,true),(14,true),(16,false),(23,false),(27,false)]
theorem inputList1736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1736 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) inputClause1736 (by decide) v hb
mask_input "1736|142671872|618970019642690137449578625"
def inputClause1738 : CNF.NClause := [(89,true),(0,true),(7,false),(14,false),(16,true),(23,false),(27,false)]
theorem inputList1738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1738 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) inputClause1738 (by decide) v hb
mask_input "1738|142622848|618970019642690137449627649"
def inputClause1740 : CNF.NClause := [(89,true),(0,true),(7,true),(14,false),(16,true),(23,false),(27,false)]
theorem inputList1740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1740 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) inputClause1740 (by decide) v hb
mask_input "1740|142622720|618970019642690137449627777"
def inputClause1742 : CNF.NClause := [(89,true),(0,true),(7,false),(14,true),(16,true),(23,false),(27,false)]
theorem inputList1742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1742 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) inputClause1742 (by decide) v hb
mask_input "1742|142606464|618970019642690137449644033"
def inputClause1744 : CNF.NClause := [(89,true),(0,true),(7,true),(14,true),(16,true),(23,false),(27,false)]
theorem inputList1744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1744 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) inputClause1744 (by decide) v hb
mask_input "1744|142606336|618970019642690137449644161"
def inputClause1746 : CNF.NClause := [(89,true),(0,true),(7,false),(14,false),(16,false),(23,true),(27,false)]
theorem inputList1746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1746 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) inputClause1746 (by decide) v hb
mask_input "1746|134299776|618970019642690137457950721"
def inputClause1748 : CNF.NClause := [(89,true),(0,true),(7,true),(14,false),(16,false),(23,true),(27,false)]
theorem inputList1748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1748 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) inputClause1748 (by decide) v hb
mask_input "1748|134299648|618970019642690137457950849"
def inputClause1750 : CNF.NClause := [(89,true),(0,true),(7,false),(14,true),(16,false),(23,true),(27,false)]
theorem inputList1750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1750 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) inputClause1750 (by decide) v hb
mask_input "1750|134283392|618970019642690137457967105"
def inputClause1752 : CNF.NClause := [(89,true),(0,true),(7,true),(14,true),(16,false),(23,true),(27,false)]
theorem inputList1752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1752 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) inputClause1752 (by decide) v hb
mask_input "1752|134283264|618970019642690137457967233"
def inputClause1754 : CNF.NClause := [(89,true),(0,true),(7,false),(14,false),(16,true),(23,true),(27,false)]
theorem inputList1754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1754 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) inputClause1754 (by decide) v hb
mask_input "1754|134234240|618970019642690137458016257"
def inputClause1756 : CNF.NClause := [(89,true),(0,true),(7,true),(14,false),(16,true),(23,true),(27,false)]
theorem inputList1756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1756 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) inputClause1756 (by decide) v hb
mask_input "1756|134234112|618970019642690137458016385"
def inputClause1758 : CNF.NClause := [(89,true),(0,true),(7,false),(14,true),(16,true),(23,true),(27,false)]
theorem inputList1758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1758 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) inputClause1758 (by decide) v hb
mask_input "1758|134217856|618970019642690137458032641"
def inputClause1760 : CNF.NClause := [(89,false),(0,true),(7,true),(14,true),(16,true),(23,true),(27,false)]
theorem inputList1760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1760 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) inputClause1760 (by decide) v hb
mask_input "1760|618970019642690137583779840|8470657"
def inputClause1762 : CNF.NClause := [(89,true),(0,true),(7,false),(14,false),(16,false),(23,false),(27,true)]
theorem inputList1762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1762 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) inputClause1762 (by decide) v hb
mask_input "1762|8470656|618970019642690137583779841"
def inputClause1764 : CNF.NClause := [(89,true),(0,true),(7,true),(14,false),(16,false),(23,false),(27,true)]
theorem inputList1764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1764 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) inputClause1764 (by decide) v hb
mask_input "1764|8470528|618970019642690137583779969"
def inputClause1766 : CNF.NClause := [(89,true),(0,true),(7,false),(14,true),(16,false),(23,false),(27,true)]
theorem inputList1766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1766 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) inputClause1766 (by decide) v hb
mask_input "1766|8454272|618970019642690137583796225"
def inputClause1768 : CNF.NClause := [(89,true),(0,true),(7,true),(14,true),(16,false),(23,false),(27,true)]
theorem inputList1768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1768 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) inputClause1768 (by decide) v hb
mask_input "1768|8454144|618970019642690137583796353"
def inputClause1770 : CNF.NClause := [(89,true),(0,true),(7,false),(14,false),(16,true),(23,false),(27,true)]
theorem inputList1770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1770 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) inputClause1770 (by decide) v hb
mask_input "1770|8405120|618970019642690137583845377"
def inputClause1772 : CNF.NClause := [(89,true),(0,true),(7,true),(14,false),(16,true),(23,false),(27,true)]
theorem inputList1772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1772 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) inputClause1772 (by decide) v hb
mask_input "1772|8404992|618970019642690137583845505"
def inputClause1774 : CNF.NClause := [(89,true),(0,true),(7,false),(14,true),(16,true),(23,false),(27,true)]
theorem inputList1774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1774 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) inputClause1774 (by decide) v hb
mask_input "1774|8388736|618970019642690137583861761"
end Percolation.MaskChain
