import NInputs149
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_8813 : CNF.NClause := [(252,false),(254,true),(261,true),(263,true),(270,true),(275,true)]
theorem inp_8813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8813 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 16) (closed_mem 4 16) cl_8813 (by decide) v hb
def cl_8814 : CNF.NClause := [(250,true),(256,true),(262,true),(263,true),(269,true),(274,false)]
theorem inp_8814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8814 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 17) (closed_mem 4 17) cl_8814 (by decide) v hb
def cl_8818 : CNF.NClause := [(250,true),(256,false),(262,true),(263,true),(269,true),(274,true)]
theorem inp_8818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8818 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 17) (closed_mem 4 17) cl_8818 (by decide) v hb
def cl_8819 : CNF.NClause := [(250,false),(256,true),(262,true),(263,true),(269,true),(274,true)]
theorem inp_8819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8819 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 17) (closed_mem 4 17) cl_8819 (by decide) v hb
def cl_8820 : CNF.NClause := [(251,true),(255,true),(259,true),(263,true),(272,true),(277,false)]
theorem inp_8820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8820 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 18) (closed_mem 4 18) cl_8820 (by decide) v hb
def cl_8821 : CNF.NClause := [(251,true),(255,true),(259,true),(263,true),(272,false),(277,true)]
theorem inp_8821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8821 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 18) (closed_mem 4 18) cl_8821 (by decide) v hb
def cl_8822 : CNF.NClause := [(251,true),(255,true),(259,true),(263,false),(272,true),(277,true)]
theorem inp_8822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8822 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 18) (closed_mem 4 18) cl_8822 (by decide) v hb
def cl_8823 : CNF.NClause := [(251,true),(255,true),(259,false),(263,true),(272,true),(277,true)]
theorem inp_8823 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8823 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 18) (closed_mem 4 18) cl_8823 (by decide) v hb
def cl_8825 : CNF.NClause := [(251,false),(255,true),(259,true),(263,true),(272,true),(277,true)]
theorem inp_8825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8825 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 18) (closed_mem 4 18) cl_8825 (by decide) v hb
def cl_8826 : CNF.NClause := [(249,true),(257,true),(260,true),(263,true),(271,true),(276,false)]
theorem inp_8826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8826 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 19) (closed_mem 4 19) cl_8826 (by decide) v hb
def cl_8828 : CNF.NClause := [(249,true),(257,true),(260,true),(263,false),(271,true),(276,true)]
theorem inp_8828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8828 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 19) (closed_mem 4 19) cl_8828 (by decide) v hb
def cl_8831 : CNF.NClause := [(249,false),(257,true),(260,true),(263,true),(271,true),(276,true)]
theorem inp_8831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8831 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 19) (closed_mem 4 19) cl_8831 (by decide) v hb
def cl_8833 : CNF.NClause := [(253,true),(254,true),(255,true),(256,true),(257,false),(278,true)]
theorem inp_8833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8833 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 20) (closed_mem 4 20) cl_8833 (by decide) v hb
def cl_8834 : CNF.NClause := [(253,true),(254,true),(255,true),(256,false),(257,true),(278,true)]
theorem inp_8834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8834 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 20) (closed_mem 4 20) cl_8834 (by decide) v hb
def cl_8835 : CNF.NClause := [(253,true),(254,true),(255,false),(256,true),(257,true),(278,true)]
theorem inp_8835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8835 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 20) (closed_mem 4 20) cl_8835 (by decide) v hb
def cl_8836 : CNF.NClause := [(253,true),(254,false),(255,true),(256,true),(257,true),(278,true)]
theorem inp_8836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8836 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 20) (closed_mem 4 20) cl_8836 (by decide) v hb
def cl_8843 : CNF.NClause := [(252,false),(253,true),(259,true),(265,true),(271,true),(274,true)]
theorem inp_8843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8843 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 21) (closed_mem 4 21) cl_8843 (by decide) v hb
def cl_8844 : CNF.NClause := [(250,true),(253,true),(261,true),(264,true),(272,true),(276,false)]
theorem inp_8844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8844 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 22) (closed_mem 4 22) cl_8844 (by decide) v hb
def cl_8847 : CNF.NClause := [(250,true),(253,true),(261,false),(264,true),(272,true),(276,true)]
theorem inp_8847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8847 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 22) (closed_mem 4 22) cl_8847 (by decide) v hb
def cl_8848 : CNF.NClause := [(250,true),(253,false),(261,true),(264,true),(272,true),(276,true)]
theorem inp_8848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8848 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 22) (closed_mem 4 22) cl_8848 (by decide) v hb
def cl_8852 : CNF.NClause := [(251,true),(253,true),(260,true),(267,false),(269,true),(275,true)]
theorem inp_8852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8852 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 23) (closed_mem 4 23) cl_8852 (by decide) v hb
def cl_8853 : CNF.NClause := [(251,true),(253,true),(260,false),(267,true),(269,true),(275,true)]
theorem inp_8853 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8853 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 23) (closed_mem 4 23) cl_8853 (by decide) v hb
def cl_8855 : CNF.NClause := [(251,false),(253,true),(260,true),(267,true),(269,true),(275,true)]
theorem inp_8855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8855 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 23) (closed_mem 4 23) cl_8855 (by decide) v hb
def cl_8857 : CNF.NClause := [(249,true),(253,true),(262,true),(266,true),(270,false),(277,true)]
theorem inp_8857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8857 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 24) (closed_mem 4 24) cl_8857 (by decide) v hb
def cl_8858 : CNF.NClause := [(249,true),(253,true),(262,true),(266,false),(270,true),(277,true)]
theorem inp_8858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8858 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 24) (closed_mem 4 24) cl_8858 (by decide) v hb
def cl_8859 : CNF.NClause := [(249,true),(253,true),(262,false),(266,true),(270,true),(277,true)]
theorem inp_8859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8859 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 24) (closed_mem 4 24) cl_8859 (by decide) v hb
def cl_8860 : CNF.NClause := [(249,true),(253,false),(262,true),(266,true),(270,true),(277,true)]
theorem inp_8860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8860 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 24) (closed_mem 4 24) cl_8860 (by decide) v hb
def cl_8861 : CNF.NClause := [(249,false),(253,true),(262,true),(266,true),(270,true),(277,true)]
theorem inp_8861 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8861 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 24) (closed_mem 4 24) cl_8861 (by decide) v hb
def cl_8863 : CNF.NClause := [(248,true),(249,true),(250,true),(251,true),(252,false),(278,true)]
theorem inp_8863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8863 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 25) (closed_mem 4 25) cl_8863 (by decide) v hb
def cl_8868 : CNF.NClause := [(248,true),(257,true),(261,true),(265,true),(269,true),(277,false)]
theorem inp_8868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8868 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 26) (closed_mem 4 26) cl_8868 (by decide) v hb
def cl_8869 : CNF.NClause := [(248,true),(257,true),(261,true),(265,true),(269,false),(277,true)]
theorem inp_8869 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8869 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 26) (closed_mem 4 26) cl_8869 (by decide) v hb
def cl_8870 : CNF.NClause := [(248,true),(257,true),(261,true),(265,false),(269,true),(277,true)]
theorem inp_8870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8870 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 26) (closed_mem 4 26) cl_8870 (by decide) v hb
def cl_8871 : CNF.NClause := [(248,true),(257,true),(261,false),(265,true),(269,true),(277,true)]
theorem inp_8871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8871 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 26) (closed_mem 4 26) cl_8871 (by decide) v hb
def cl_8872 : CNF.NClause := [(248,true),(257,false),(261,true),(265,true),(269,true),(277,true)]
theorem inp_8872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8872 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 26) (closed_mem 4 26) cl_8872 (by decide) v hb
def cl_8876 : CNF.NClause := [(248,true),(255,true),(262,true),(264,false),(271,true),(275,true)]
theorem inp_8876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8876 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 27) (closed_mem 4 27) cl_8876 (by decide) v hb
def cl_8877 : CNF.NClause := [(248,true),(255,true),(262,false),(264,true),(271,true),(275,true)]
theorem inp_8877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8877 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 27) (closed_mem 4 27) cl_8877 (by decide) v hb
def cl_8881 : CNF.NClause := [(248,true),(256,true),(259,true),(267,true),(270,false),(276,true)]
theorem inp_8881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8881 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 28) (closed_mem 4 28) cl_8881 (by decide) v hb
def cl_8883 : CNF.NClause := [(248,true),(256,true),(259,false),(267,true),(270,true),(276,true)]
theorem inp_8883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8883 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 28) (closed_mem 4 28) cl_8883 (by decide) v hb
def cl_8884 : CNF.NClause := [(248,true),(256,false),(259,true),(267,true),(270,true),(276,true)]
theorem inp_8884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8884 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 28) (closed_mem 4 28) cl_8884 (by decide) v hb
def cl_8886 : CNF.NClause := [(248,true),(254,true),(260,true),(266,true),(272,true),(274,false)]
theorem inp_8886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8886 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 29) (closed_mem 4 29) cl_8886 (by decide) v hb
def cl_8887 : CNF.NClause := [(248,true),(254,true),(260,true),(266,true),(272,false),(274,true)]
theorem inp_8887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8887 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 29) (closed_mem 4 29) cl_8887 (by decide) v hb
def cl_8888 : CNF.NClause := [(248,true),(254,true),(260,true),(266,false),(272,true),(274,true)]
theorem inp_8888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8888 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 29) (closed_mem 4 29) cl_8888 (by decide) v hb
def cl_8890 : CNF.NClause := [(248,true),(254,false),(260,true),(266,true),(272,true),(274,true)]
theorem inp_8890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8890 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 29) (closed_mem 4 29) cl_8890 (by decide) v hb
def cl_8893 : CNF.NClause := [(248,true),(253,true),(258,true),(263,true),(268,false),(273,true)]
theorem inp_8893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8893 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 30) (closed_mem 4 30) cl_8893 (by decide) v hb
def cl_8894 : CNF.NClause := [(248,true),(253,true),(258,true),(263,false),(268,true),(273,true)]
theorem inp_8894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8894 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 30) (closed_mem 4 30) cl_8894 (by decide) v hb
def cl_8895 : CNF.NClause := [(248,true),(253,true),(258,false),(263,true),(268,true),(273,true)]
theorem inp_8895 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8895 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 30) (closed_mem 4 30) cl_8895 (by decide) v hb
def cl_8896 : CNF.NClause := [(248,true),(253,false),(258,true),(263,true),(268,true),(273,true)]
theorem inp_8896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8896 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 4 30) (closed_mem 4 30) cl_8896 (by decide) v hb
def cl_8899 : CNF.NClause := [(304,true),(305,true),(306,true),(307,true),(308,false),(309,true)]
theorem inp_8899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8899 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 0) (closed_mem 5 0) cl_8899 (by decide) v hb
def cl_8900 : CNF.NClause := [(304,true),(305,true),(306,true),(307,false),(308,true),(309,true)]
theorem inp_8900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8900 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 0) (closed_mem 5 0) cl_8900 (by decide) v hb
def cl_8901 : CNF.NClause := [(304,true),(305,true),(306,false),(307,true),(308,true),(309,true)]
theorem inp_8901 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8901 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 0) (closed_mem 5 0) cl_8901 (by decide) v hb
end Percolation.NReplay
