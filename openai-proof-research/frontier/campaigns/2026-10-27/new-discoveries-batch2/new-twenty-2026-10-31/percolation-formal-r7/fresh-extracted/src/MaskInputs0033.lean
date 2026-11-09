import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause1860 : CNF.NClause := [(91,true),(0,true),(6,true),(12,false),(18,false),(24,false),(26,false)]
theorem inputList1860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1860 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) inputClause1860 (by decide) v hb
mask_input "1860|84152320|2475880078570760549798248513"
def inputClause1862 : CNF.NClause := [(91,true),(0,true),(6,false),(12,true),(18,false),(24,false),(26,false)]
theorem inputList1862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1862 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) inputClause1862 (by decide) v hb
mask_input "1862|84148288|2475880078570760549798252545"
def inputClause1864 : CNF.NClause := [(91,true),(0,true),(6,true),(12,true),(18,false),(24,false),(26,false)]
theorem inputList1864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1864 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) inputClause1864 (by decide) v hb
mask_input "1864|84148224|2475880078570760549798252609"
def inputClause1866 : CNF.NClause := [(91,true),(0,true),(6,false),(12,false),(18,true),(24,false),(26,false)]
theorem inputList1866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1866 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) inputClause1866 (by decide) v hb
mask_input "1866|83890240|2475880078570760549798510593"
def inputClause1868 : CNF.NClause := [(91,true),(0,true),(6,true),(12,false),(18,true),(24,false),(26,false)]
theorem inputList1868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1868 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) inputClause1868 (by decide) v hb
mask_input "1868|83890176|2475880078570760549798510657"
def inputClause1870 : CNF.NClause := [(91,true),(0,true),(6,false),(12,true),(18,true),(24,false),(26,false)]
theorem inputList1870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1870 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) inputClause1870 (by decide) v hb
mask_input "1870|83886144|2475880078570760549798514689"
def inputClause1872 : CNF.NClause := [(91,true),(0,true),(6,true),(12,true),(18,true),(24,false),(26,false)]
theorem inputList1872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1872 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) inputClause1872 (by decide) v hb
mask_input "1872|83886080|2475880078570760549798514753"
def inputClause1874 : CNF.NClause := [(91,true),(0,true),(6,false),(12,false),(18,false),(24,true),(26,false)]
theorem inputList1874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1874 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) inputClause1874 (by decide) v hb
mask_input "1874|67375168|2475880078570760549815025665"
def inputClause1876 : CNF.NClause := [(91,true),(0,true),(6,true),(12,false),(18,false),(24,true),(26,false)]
theorem inputList1876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1876 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) inputClause1876 (by decide) v hb
mask_input "1876|67375104|2475880078570760549815025729"
def inputClause1878 : CNF.NClause := [(91,true),(0,true),(6,false),(12,true),(18,false),(24,true),(26,false)]
theorem inputList1878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1878 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) inputClause1878 (by decide) v hb
mask_input "1878|67371072|2475880078570760549815029761"
def inputClause1880 : CNF.NClause := [(91,true),(0,true),(6,true),(12,true),(18,false),(24,true),(26,false)]
theorem inputList1880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1880 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) inputClause1880 (by decide) v hb
mask_input "1880|67371008|2475880078570760549815029825"
def inputClause1882 : CNF.NClause := [(91,true),(0,true),(6,false),(12,false),(18,true),(24,true),(26,false)]
theorem inputList1882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1882 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) inputClause1882 (by decide) v hb
mask_input "1882|67113024|2475880078570760549815287809"
def inputClause1884 : CNF.NClause := [(91,true),(0,true),(6,true),(12,false),(18,true),(24,true),(26,false)]
theorem inputList1884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1884 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) inputClause1884 (by decide) v hb
mask_input "1884|67112960|2475880078570760549815287873"
def inputClause1886 : CNF.NClause := [(91,true),(0,true),(6,false),(12,true),(18,true),(24,true),(26,false)]
theorem inputList1886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1886 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) inputClause1886 (by decide) v hb
mask_input "1886|67108928|2475880078570760549815291905"
def inputClause1888 : CNF.NClause := [(91,false),(0,true),(6,true),(12,true),(18,true),(24,true),(26,false)]
theorem inputList1888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1888 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) inputClause1888 (by decide) v hb
mask_input "1888|2475880078570760549865357312|17043521"
def inputClause1890 : CNF.NClause := [(91,true),(0,true),(6,false),(12,false),(18,false),(24,false),(26,true)]
theorem inputList1890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1890 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) inputClause1890 (by decide) v hb
mask_input "1890|17043520|2475880078570760549865357313"
def inputClause1892 : CNF.NClause := [(91,true),(0,true),(6,true),(12,false),(18,false),(24,false),(26,true)]
theorem inputList1892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1892 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) inputClause1892 (by decide) v hb
mask_input "1892|17043456|2475880078570760549865357377"
def inputClause1894 : CNF.NClause := [(91,true),(0,true),(6,false),(12,true),(18,false),(24,false),(26,true)]
theorem inputList1894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1894 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) inputClause1894 (by decide) v hb
mask_input "1894|17039424|2475880078570760549865361409"
def inputClause1896 : CNF.NClause := [(91,true),(0,true),(6,true),(12,true),(18,false),(24,false),(26,true)]
theorem inputList1896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1896 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) inputClause1896 (by decide) v hb
mask_input "1896|17039360|2475880078570760549865361473"
def inputClause1898 : CNF.NClause := [(91,true),(0,true),(6,false),(12,false),(18,true),(24,false),(26,true)]
theorem inputList1898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1898 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) inputClause1898 (by decide) v hb
mask_input "1898|16781376|2475880078570760549865619457"
def inputClause1900 : CNF.NClause := [(91,true),(0,true),(6,true),(12,false),(18,true),(24,false),(26,true)]
theorem inputList1900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1900 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) inputClause1900 (by decide) v hb
mask_input "1900|16781312|2475880078570760549865619521"
def inputClause1902 : CNF.NClause := [(91,true),(0,true),(6,false),(12,true),(18,true),(24,false),(26,true)]
theorem inputList1902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1902 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) inputClause1902 (by decide) v hb
mask_input "1902|16777280|2475880078570760549865623553"
def inputClause1904 : CNF.NClause := [(91,false),(0,true),(6,true),(12,true),(18,true),(24,false),(26,true)]
theorem inputList1904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1904 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) inputClause1904 (by decide) v hb
mask_input "1904|2475880078570760549815025664|67375169"
def inputClause1906 : CNF.NClause := [(91,true),(0,true),(6,false),(12,false),(18,false),(24,true),(26,true)]
theorem inputList1906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1906 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) inputClause1906 (by decide) v hb
mask_input "1906|266304|2475880078570760549882134529"
def inputClause1908 : CNF.NClause := [(91,true),(0,true),(6,true),(12,false),(18,false),(24,true),(26,true)]
theorem inputList1908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1908 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) inputClause1908 (by decide) v hb
mask_input "1908|266240|2475880078570760549882134593"
def inputClause1910 : CNF.NClause := [(91,true),(0,true),(6,false),(12,true),(18,false),(24,true),(26,true)]
theorem inputList1910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1910 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) inputClause1910 (by decide) v hb
mask_input "1910|262208|2475880078570760549882138625"
def inputClause1912 : CNF.NClause := [(91,false),(0,true),(6,true),(12,true),(18,false),(24,true),(26,true)]
theorem inputList1912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1912 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) inputClause1912 (by decide) v hb
mask_input "1912|2475880078570760549798510592|83890241"
def inputClause1914 : CNF.NClause := [(91,true),(0,true),(6,false),(12,false),(18,true),(24,true),(26,true)]
theorem inputList1914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1914 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) inputClause1914 (by decide) v hb
mask_input "1914|4160|2475880078570760549882396673"
def inputClause1916 : CNF.NClause := [(91,false),(0,true),(6,true),(12,false),(18,true),(24,true),(26,true)]
theorem inputList1916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1916 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) inputClause1916 (by decide) v hb
mask_input "1916|2475880078570760549798252544|84148289"
def inputClause1918 : CNF.NClause := [(91,false),(0,true),(6,false),(12,true),(18,true),(24,true),(26,true)]
theorem inputList1918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1918 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) inputClause1918 (by decide) v hb
mask_input "1918|2475880078570760549798248512|84152321"
def inputClause1920 : CNF.NClause := [(91,false),(0,true),(6,true),(12,true),(18,true),(24,true),(26,true)]
theorem inputList1920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1920 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 29) 29) (activationA_mem 29) inputClause1920 (by decide) v hb
mask_input "1920|2475880078570760549798248448|84152385"
def inputClause1954 : CNF.NClause := [(92,true),(0,true),(5,false),(10,false),(15,false),(20,false),(25,true)]
theorem inputList1954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1954 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) inputClause1954 (by decide) v hb
mask_input "1954|1082400|4951760157141521099630051329"
def inputClause1956 : CNF.NClause := [(92,true),(0,true),(5,true),(10,false),(15,false),(20,false),(25,true)]
theorem inputList1956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1956 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) inputClause1956 (by decide) v hb
mask_input "1956|1082368|4951760157141521099630051361"
def inputClause1958 : CNF.NClause := [(92,true),(0,true),(5,false),(10,true),(15,false),(20,false),(25,true)]
theorem inputList1958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1958 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) inputClause1958 (by decide) v hb
mask_input "1958|1081376|4951760157141521099630052353"
def inputClause1960 : CNF.NClause := [(92,true),(0,true),(5,true),(10,true),(15,false),(20,false),(25,true)]
theorem inputList1960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1960 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) inputClause1960 (by decide) v hb
mask_input "1960|1081344|4951760157141521099630052385"
def inputClause1962 : CNF.NClause := [(92,true),(0,true),(5,false),(10,false),(15,true),(20,false),(25,true)]
theorem inputList1962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1962 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) inputClause1962 (by decide) v hb
mask_input "1962|1049632|4951760157141521099630084097"
def inputClause1964 : CNF.NClause := [(92,true),(0,true),(5,true),(10,false),(15,true),(20,false),(25,true)]
theorem inputList1964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1964 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) inputClause1964 (by decide) v hb
mask_input "1964|1049600|4951760157141521099630084129"
def inputClause1966 : CNF.NClause := [(92,true),(0,true),(5,false),(10,true),(15,true),(20,false),(25,true)]
theorem inputList1966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1966 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) inputClause1966 (by decide) v hb
mask_input "1966|1048608|4951760157141521099630085121"
def inputClause1968 : CNF.NClause := [(92,false),(0,true),(5,true),(10,true),(15,true),(20,false),(25,true)]
theorem inputList1968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1968 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) inputClause1968 (by decide) v hb
mask_input "1968|4951760157141521099597545472|33588257"
def inputClause1970 : CNF.NClause := [(92,true),(0,true),(5,false),(10,false),(15,false),(20,true),(25,true)]
theorem inputList1970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1970 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 30) 30) (activationA_mem 30) inputClause1970 (by decide) v hb
mask_input "1970|33824|4951760157141521099631099905"
end Percolation.MaskChain
