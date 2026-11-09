import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause1776 : CNF.NClause := [(89,false),(0,true),(7,true),(14,true),(16,true),(23,false),(27,true)]
theorem inputList1776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1776 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) inputClause1776 (by decide) v hb
mask_input "1776|618970019642690137457950720|134299777"
def inputClause1778 : CNF.NClause := [(89,true),(0,true),(7,false),(14,false),(16,false),(23,true),(27,true)]
theorem inputList1778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1778 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) inputClause1778 (by decide) v hb
mask_input "1778|82048|618970019642690137592168449"
def inputClause1780 : CNF.NClause := [(89,true),(0,true),(7,true),(14,false),(16,false),(23,true),(27,true)]
theorem inputList1780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1780 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) inputClause1780 (by decide) v hb
mask_input "1780|81920|618970019642690137592168577"
def inputClause1782 : CNF.NClause := [(89,true),(0,true),(7,false),(14,true),(16,false),(23,true),(27,true)]
theorem inputList1782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1782 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) inputClause1782 (by decide) v hb
mask_input "1782|65664|618970019642690137592184833"
def inputClause1784 : CNF.NClause := [(89,false),(0,true),(7,true),(14,true),(16,false),(23,true),(27,true)]
theorem inputList1784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1784 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) inputClause1784 (by decide) v hb
mask_input "1784|618970019642690137449627648|142622849"
def inputClause1786 : CNF.NClause := [(89,true),(0,true),(7,false),(14,false),(16,true),(23,true),(27,true)]
theorem inputList1786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1786 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) inputClause1786 (by decide) v hb
mask_input "1786|16512|618970019642690137592233985"
def inputClause1788 : CNF.NClause := [(89,false),(0,true),(7,true),(14,false),(16,true),(23,true),(27,true)]
theorem inputList1788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1788 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) inputClause1788 (by decide) v hb
mask_input "1788|618970019642690137449578496|142672001"
def inputClause1790 : CNF.NClause := [(89,false),(0,true),(7,false),(14,true),(16,true),(23,true),(27,true)]
theorem inputList1790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1790 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 27) 27) (activationA_mem 27) inputClause1790 (by decide) v hb
mask_input "1790|618970019642690137449562240|142688257"
def inputClause1794 : CNF.NClause := [(90,true),(0,true),(8,false),(11,false),(19,false),(22,false),(28,false)]
theorem inputList1794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1794 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) inputClause1794 (by decide) v hb
mask_input "1794|273156352|1237940039285380274899124225"
def inputClause1796 : CNF.NClause := [(90,true),(0,true),(8,true),(11,false),(19,false),(22,false),(28,false)]
theorem inputList1796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1796 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) inputClause1796 (by decide) v hb
mask_input "1796|273156096|1237940039285380274899124481"
def inputClause1798 : CNF.NClause := [(90,true),(0,true),(8,false),(11,true),(19,false),(22,false),(28,false)]
theorem inputList1798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1798 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) inputClause1798 (by decide) v hb
mask_input "1798|273154304|1237940039285380274899126273"
def inputClause1800 : CNF.NClause := [(90,true),(0,true),(8,true),(11,true),(19,false),(22,false),(28,false)]
theorem inputList1800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1800 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) inputClause1800 (by decide) v hb
mask_input "1800|273154048|1237940039285380274899126529"
def inputClause1802 : CNF.NClause := [(90,true),(0,true),(8,false),(11,false),(19,true),(22,false),(28,false)]
theorem inputList1802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1802 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) inputClause1802 (by decide) v hb
mask_input "1802|272632064|1237940039285380274899648513"
def inputClause1804 : CNF.NClause := [(90,true),(0,true),(8,true),(11,false),(19,true),(22,false),(28,false)]
theorem inputList1804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1804 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) inputClause1804 (by decide) v hb
mask_input "1804|272631808|1237940039285380274899648769"
def inputClause1806 : CNF.NClause := [(90,true),(0,true),(8,false),(11,true),(19,true),(22,false),(28,false)]
theorem inputList1806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1806 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) inputClause1806 (by decide) v hb
mask_input "1806|272630016|1237940039285380274899650561"
def inputClause1808 : CNF.NClause := [(90,true),(0,true),(8,true),(11,true),(19,true),(22,false),(28,false)]
theorem inputList1808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1808 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) inputClause1808 (by decide) v hb
mask_input "1808|272629760|1237940039285380274899650817"
def inputClause1810 : CNF.NClause := [(90,true),(0,true),(8,false),(11,false),(19,false),(22,true),(28,false)]
theorem inputList1810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1810 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) inputClause1810 (by decide) v hb
mask_input "1810|268962048|1237940039285380274903318529"
def inputClause1812 : CNF.NClause := [(90,true),(0,true),(8,true),(11,false),(19,false),(22,true),(28,false)]
theorem inputList1812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1812 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) inputClause1812 (by decide) v hb
mask_input "1812|268961792|1237940039285380274903318785"
def inputClause1814 : CNF.NClause := [(90,true),(0,true),(8,false),(11,true),(19,false),(22,true),(28,false)]
theorem inputList1814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1814 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) inputClause1814 (by decide) v hb
mask_input "1814|268960000|1237940039285380274903320577"
def inputClause1816 : CNF.NClause := [(90,true),(0,true),(8,true),(11,true),(19,false),(22,true),(28,false)]
theorem inputList1816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1816 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) inputClause1816 (by decide) v hb
mask_input "1816|268959744|1237940039285380274903320833"
def inputClause1818 : CNF.NClause := [(90,true),(0,true),(8,false),(11,false),(19,true),(22,true),(28,false)]
theorem inputList1818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1818 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) inputClause1818 (by decide) v hb
mask_input "1818|268437760|1237940039285380274903842817"
def inputClause1820 : CNF.NClause := [(90,true),(0,true),(8,true),(11,false),(19,true),(22,true),(28,false)]
theorem inputList1820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1820 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) inputClause1820 (by decide) v hb
mask_input "1820|268437504|1237940039285380274903843073"
def inputClause1822 : CNF.NClause := [(90,true),(0,true),(8,false),(11,true),(19,true),(22,true),(28,false)]
theorem inputList1822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1822 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) inputClause1822 (by decide) v hb
mask_input "1822|268435712|1237940039285380274903844865"
def inputClause1824 : CNF.NClause := [(90,false),(0,true),(8,true),(11,true),(19,true),(22,true),(28,false)]
theorem inputList1824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1824 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) inputClause1824 (by decide) v hb
mask_input "1824|1237940039285380275167559680|4720897"
def inputClause1826 : CNF.NClause := [(90,true),(0,true),(8,false),(11,false),(19,false),(22,false),(28,true)]
theorem inputList1826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1826 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) inputClause1826 (by decide) v hb
mask_input "1826|4720896|1237940039285380275167559681"
def inputClause1828 : CNF.NClause := [(90,true),(0,true),(8,true),(11,false),(19,false),(22,false),(28,true)]
theorem inputList1828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1828 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) inputClause1828 (by decide) v hb
mask_input "1828|4720640|1237940039285380275167559937"
def inputClause1830 : CNF.NClause := [(90,true),(0,true),(8,false),(11,true),(19,false),(22,false),(28,true)]
theorem inputList1830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1830 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) inputClause1830 (by decide) v hb
mask_input "1830|4718848|1237940039285380275167561729"
def inputClause1832 : CNF.NClause := [(90,true),(0,true),(8,true),(11,true),(19,false),(22,false),(28,true)]
theorem inputList1832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1832 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) inputClause1832 (by decide) v hb
mask_input "1832|4718592|1237940039285380275167561985"
def inputClause1834 : CNF.NClause := [(90,true),(0,true),(8,false),(11,false),(19,true),(22,false),(28,true)]
theorem inputList1834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1834 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) inputClause1834 (by decide) v hb
mask_input "1834|4196608|1237940039285380275168083969"
def inputClause1836 : CNF.NClause := [(90,true),(0,true),(8,true),(11,false),(19,true),(22,false),(28,true)]
theorem inputList1836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1836 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) inputClause1836 (by decide) v hb
mask_input "1836|4196352|1237940039285380275168084225"
def inputClause1838 : CNF.NClause := [(90,true),(0,true),(8,false),(11,true),(19,true),(22,false),(28,true)]
theorem inputList1838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1838 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) inputClause1838 (by decide) v hb
mask_input "1838|4194560|1237940039285380275168086017"
def inputClause1840 : CNF.NClause := [(90,false),(0,true),(8,true),(11,true),(19,true),(22,false),(28,true)]
theorem inputList1840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1840 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) inputClause1840 (by decide) v hb
mask_input "1840|1237940039285380274903318528|268962049"
def inputClause1842 : CNF.NClause := [(90,true),(0,true),(8,false),(11,false),(19,false),(22,true),(28,true)]
theorem inputList1842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1842 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) inputClause1842 (by decide) v hb
mask_input "1842|526592|1237940039285380275171753985"
def inputClause1844 : CNF.NClause := [(90,true),(0,true),(8,true),(11,false),(19,false),(22,true),(28,true)]
theorem inputList1844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1844 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) inputClause1844 (by decide) v hb
mask_input "1844|526336|1237940039285380275171754241"
def inputClause1846 : CNF.NClause := [(90,true),(0,true),(8,false),(11,true),(19,false),(22,true),(28,true)]
theorem inputList1846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1846 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) inputClause1846 (by decide) v hb
mask_input "1846|524544|1237940039285380275171756033"
def inputClause1848 : CNF.NClause := [(90,false),(0,true),(8,true),(11,true),(19,false),(22,true),(28,true)]
theorem inputList1848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1848 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) inputClause1848 (by decide) v hb
mask_input "1848|1237940039285380274899648512|272632065"
def inputClause1850 : CNF.NClause := [(90,true),(0,true),(8,false),(11,false),(19,true),(22,true),(28,true)]
theorem inputList1850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1850 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) inputClause1850 (by decide) v hb
mask_input "1850|2304|1237940039285380275172278273"
def inputClause1852 : CNF.NClause := [(90,false),(0,true),(8,true),(11,false),(19,true),(22,true),(28,true)]
theorem inputList1852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1852 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) inputClause1852 (by decide) v hb
mask_input "1852|1237940039285380274899126272|273154305"
def inputClause1854 : CNF.NClause := [(90,false),(0,true),(8,false),(11,true),(19,true),(22,true),(28,true)]
theorem inputList1854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1854 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 28) 28) (activationA_mem 28) inputClause1854 (by decide) v hb
mask_input "1854|1237940039285380274899124480|273156097"
def inputClause1858 : CNF.NClause := [(91,true),(0,true),(6,false),(12,false),(18,false),(24,false),(26,false)]
theorem inputList1858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1858 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) inputClause1858 (by decide) v hb
mask_input "1858|84152384|2475880078570760549798248449"
end Percolation.MaskChain
