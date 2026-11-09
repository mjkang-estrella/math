import NInputs150
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_8905 : CNF.NClause := [(283,true),(288,true),(293,true),(298,true),(303,false),(304,true)]
theorem inp_8905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8905 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 1) (closed_mem 5 1) cl_8905 (by decide) v hb
def cl_8906 : CNF.NClause := [(283,true),(288,true),(293,true),(298,false),(303,true),(304,true)]
theorem inp_8906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8906 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 1) (closed_mem 5 1) cl_8906 (by decide) v hb
def cl_8907 : CNF.NClause := [(283,true),(288,true),(293,false),(298,true),(303,true),(304,true)]
theorem inp_8907 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8907 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 1) (closed_mem 5 1) cl_8907 (by decide) v hb
def cl_8908 : CNF.NClause := [(283,true),(288,false),(293,true),(298,true),(303,true),(304,true)]
theorem inp_8908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8908 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_8908 v hb
def cl_8909 : CNF.NClause := [(283,false),(288,true),(293,true),(298,true),(303,true),(304,true)]
theorem inp_8909 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8909 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 1) (closed_mem 5 1) cl_8909 (by decide) v hb
def cl_8911 : CNF.NClause := [(281,true),(286,true),(291,true),(296,true),(301,false),(304,true)]
theorem inp_8911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8911 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 2) (closed_mem 5 2) cl_8911 (by decide) v hb
def cl_8912 : CNF.NClause := [(281,true),(286,true),(291,true),(296,false),(301,true),(304,true)]
theorem inp_8912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8912 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 2) (closed_mem 5 2) cl_8912 (by decide) v hb
def cl_8913 : CNF.NClause := [(281,true),(286,true),(291,false),(296,true),(301,true),(304,true)]
theorem inp_8913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8913 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 2) (closed_mem 5 2) cl_8913 (by decide) v hb
def cl_8914 : CNF.NClause := [(281,true),(286,false),(291,true),(296,true),(301,true),(304,true)]
theorem inp_8914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8914 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 2) (closed_mem 5 2) cl_8914 (by decide) v hb
def cl_8915 : CNF.NClause := [(281,false),(286,true),(291,true),(296,true),(301,true),(304,true)]
theorem inp_8915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8915 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 2) (closed_mem 5 2) cl_8915 (by decide) v hb
def cl_8917 : CNF.NClause := [(282,true),(287,true),(292,true),(297,true),(302,false),(304,true)]
theorem inp_8917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8917 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 3) (closed_mem 5 3) cl_8917 (by decide) v hb
def cl_8921 : CNF.NClause := [(282,false),(287,true),(292,true),(297,true),(302,true),(304,true)]
theorem inp_8921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8921 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 3) (closed_mem 5 3) cl_8921 (by decide) v hb
def cl_8923 : CNF.NClause := [(280,true),(285,true),(290,true),(295,true),(300,false),(304,true)]
theorem inp_8923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8923 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 4) (closed_mem 5 4) cl_8923 (by decide) v hb
def cl_8924 : CNF.NClause := [(280,true),(285,true),(290,true),(295,false),(300,true),(304,true)]
theorem inp_8924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8924 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 4) (closed_mem 5 4) cl_8924 (by decide) v hb
def cl_8925 : CNF.NClause := [(280,true),(285,true),(290,false),(295,true),(300,true),(304,true)]
theorem inp_8925 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8925 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 4) (closed_mem 5 4) cl_8925 (by decide) v hb
def cl_8926 : CNF.NClause := [(280,true),(285,false),(290,true),(295,true),(300,true),(304,true)]
theorem inp_8926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8926 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 4) (closed_mem 5 4) cl_8926 (by decide) v hb
def cl_8927 : CNF.NClause := [(280,false),(285,true),(290,true),(295,true),(300,true),(304,true)]
theorem inp_8927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8927 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 4) (closed_mem 5 4) cl_8927 (by decide) v hb
def cl_8929 : CNF.NClause := [(299,true),(300,true),(301,true),(302,true),(303,false),(309,true)]
theorem inp_8929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8929 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 5) (closed_mem 5 5) cl_8929 (by decide) v hb
def cl_8932 : CNF.NClause := [(299,true),(300,false),(301,true),(302,true),(303,true),(309,true)]
theorem inp_8932 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8932 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 5) (closed_mem 5 5) cl_8932 (by decide) v hb
def cl_8933 : CNF.NClause := [(299,false),(300,true),(301,true),(302,true),(303,true),(309,true)]
theorem inp_8933 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8933 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 5) (closed_mem 5 5) cl_8933 (by decide) v hb
def cl_8934 : CNF.NClause := [(283,true),(287,true),(291,true),(295,true),(299,true),(308,false)]
theorem inp_8934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8934 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 6) (closed_mem 5 6) cl_8934 (by decide) v hb
def cl_8936 : CNF.NClause := [(283,true),(287,true),(291,true),(295,false),(299,true),(308,true)]
theorem inp_8936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8936 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 6) (closed_mem 5 6) cl_8936 (by decide) v hb
def cl_8937 : CNF.NClause := [(283,true),(287,true),(291,false),(295,true),(299,true),(308,true)]
theorem inp_8937 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8937 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 6) (closed_mem 5 6) cl_8937 (by decide) v hb
def cl_8938 : CNF.NClause := [(283,true),(287,false),(291,true),(295,true),(299,true),(308,true)]
theorem inp_8938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8938 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 6) (closed_mem 5 6) cl_8938 (by decide) v hb
def cl_8939 : CNF.NClause := [(283,false),(287,true),(291,true),(295,true),(299,true),(308,true)]
theorem inp_8939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8939 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 6) (closed_mem 5 6) cl_8939 (by decide) v hb
def cl_8940 : CNF.NClause := [(281,true),(288,true),(290,true),(297,true),(299,true),(306,false)]
theorem inp_8940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8940 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 7) (closed_mem 5 7) cl_8940 (by decide) v hb
def cl_8941 : CNF.NClause := [(281,true),(288,true),(290,true),(297,true),(299,false),(306,true)]
theorem inp_8941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8941 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_8941 v hb
def cl_8942 : CNF.NClause := [(281,true),(288,true),(290,true),(297,false),(299,true),(306,true)]
theorem inp_8942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8942 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 7) (closed_mem 5 7) cl_8942 (by decide) v hb
def cl_8943 : CNF.NClause := [(281,true),(288,true),(290,false),(297,true),(299,true),(306,true)]
theorem inp_8943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8943 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 7) (closed_mem 5 7) cl_8943 (by decide) v hb
def cl_8944 : CNF.NClause := [(281,true),(288,false),(290,true),(297,true),(299,true),(306,true)]
theorem inp_8944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8944 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 7) (closed_mem 5 7) cl_8944 (by decide) v hb
def cl_8945 : CNF.NClause := [(281,false),(288,true),(290,true),(297,true),(299,true),(306,true)]
theorem inp_8945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8945 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 7) (closed_mem 5 7) cl_8945 (by decide) v hb
def cl_8946 : CNF.NClause := [(282,true),(285,true),(293,true),(296,true),(299,true),(307,false)]
theorem inp_8946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8946 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 8) (closed_mem 5 8) cl_8946 (by decide) v hb
def cl_8948 : CNF.NClause := [(282,true),(285,true),(293,true),(296,false),(299,true),(307,true)]
theorem inp_8948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8948 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 8) (closed_mem 5 8) cl_8948 (by decide) v hb
def cl_8949 : CNF.NClause := [(282,true),(285,true),(293,false),(296,true),(299,true),(307,true)]
theorem inp_8949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8949 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 8) (closed_mem 5 8) cl_8949 (by decide) v hb
def cl_8950 : CNF.NClause := [(282,true),(285,false),(293,true),(296,true),(299,true),(307,true)]
theorem inp_8950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8950 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 8) (closed_mem 5 8) cl_8950 (by decide) v hb
def cl_8953 : CNF.NClause := [(280,true),(286,true),(292,true),(298,true),(299,false),(305,true)]
theorem inp_8953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8953 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 9) (closed_mem 5 9) cl_8953 (by decide) v hb
def cl_8954 : CNF.NClause := [(280,true),(286,true),(292,true),(298,false),(299,true),(305,true)]
theorem inp_8954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8954 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_8954 v hb
def cl_8956 : CNF.NClause := [(280,true),(286,false),(292,true),(298,true),(299,true),(305,true)]
theorem inp_8956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8956 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 9) (closed_mem 5 9) cl_8956 (by decide) v hb
def cl_8959 : CNF.NClause := [(289,true),(290,true),(291,true),(292,true),(293,false),(309,true)]
theorem inp_8959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8959 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 10) (closed_mem 5 10) cl_8959 (by decide) v hb
def cl_8960 : CNF.NClause := [(289,true),(290,true),(291,true),(292,false),(293,true),(309,true)]
theorem inp_8960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8960 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 10) (closed_mem 5 10) cl_8960 (by decide) v hb
def cl_8961 : CNF.NClause := [(289,true),(290,true),(291,false),(292,true),(293,true),(309,true)]
theorem inp_8961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8961 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 10) (closed_mem 5 10) cl_8961 (by decide) v hb
def cl_8962 : CNF.NClause := [(289,true),(290,false),(291,true),(292,true),(293,true),(309,true)]
theorem inp_8962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8962 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 10) (closed_mem 5 10) cl_8962 (by decide) v hb
def cl_8963 : CNF.NClause := [(289,false),(290,true),(291,true),(292,true),(293,true),(309,true)]
theorem inp_8963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8963 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 10) (closed_mem 5 10) cl_8963 (by decide) v hb
def cl_8964 : CNF.NClause := [(283,true),(286,true),(289,true),(297,true),(300,true),(307,false)]
theorem inp_8964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8964 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 11) (closed_mem 5 11) cl_8964 (by decide) v hb
def cl_8965 : CNF.NClause := [(283,true),(286,true),(289,true),(297,true),(300,false),(307,true)]
theorem inp_8965 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8965 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 11) (closed_mem 5 11) cl_8965 (by decide) v hb
def cl_8967 : CNF.NClause := [(283,true),(286,true),(289,false),(297,true),(300,true),(307,true)]
theorem inp_8967 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8967 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 11) (closed_mem 5 11) cl_8967 (by decide) v hb
def cl_8968 : CNF.NClause := [(283,true),(286,false),(289,true),(297,true),(300,true),(307,true)]
theorem inp_8968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8968 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 11) (closed_mem 5 11) cl_8968 (by decide) v hb
def cl_8969 : CNF.NClause := [(283,false),(286,true),(289,true),(297,true),(300,true),(307,true)]
theorem inp_8969 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8969 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_8969 v hb
def cl_8971 : CNF.NClause := [(281,true),(285,true),(289,true),(298,true),(302,false),(308,true)]
theorem inp_8971 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8971 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 12) (closed_mem 5 12) cl_8971 (by decide) v hb
def cl_8972 : CNF.NClause := [(281,true),(285,true),(289,true),(298,false),(302,true),(308,true)]
theorem inp_8972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_8972 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 5 12) (closed_mem 5 12) cl_8972 (by decide) v hb
end Percolation.NReplay
