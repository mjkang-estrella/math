import NInputs196
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_12888 : CNF.NClause := [(931,true),(938,true),(940,true),(947,true),(954,true),(957,false)]
theorem inp_12888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12888 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 14) (closed_mem 26 14) cl_12888 (by decide) v hb
def cl_12889 : CNF.NClause := [(931,true),(938,true),(940,true),(947,true),(954,false),(957,true)]
theorem inp_12889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12889 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 14) (closed_mem 26 14) cl_12889 (by decide) v hb
def cl_12893 : CNF.NClause := [(931,false),(938,true),(940,true),(947,true),(954,true),(957,true)]
theorem inp_12893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12893 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 14) (closed_mem 26 14) cl_12893 (by decide) v hb
def cl_12895 : CNF.NClause := [(945,true),(946,true),(947,true),(948,true),(949,false),(960,true)]
theorem inp_12895 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12895 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 15) (closed_mem 26 15) cl_12895 (by decide) v hb
def cl_12896 : CNF.NClause := [(945,true),(946,true),(947,true),(948,false),(949,true),(960,true)]
theorem inp_12896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12896 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 15) (closed_mem 26 15) cl_12896 (by decide) v hb
def cl_12897 : CNF.NClause := [(945,true),(946,true),(947,false),(948,true),(949,true),(960,true)]
theorem inp_12897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12897 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 15) (closed_mem 26 15) cl_12897 (by decide) v hb
def cl_12898 : CNF.NClause := [(945,true),(946,false),(947,true),(948,true),(949,true),(960,true)]
theorem inp_12898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12898 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 15) (closed_mem 26 15) cl_12898 (by decide) v hb
def cl_12899 : CNF.NClause := [(945,false),(946,true),(947,true),(948,true),(949,true),(960,true)]
theorem inp_12899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12899 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 15) (closed_mem 26 15) cl_12899 (by decide) v hb
def cl_12900 : CNF.NClause := [(934,true),(936,true),(943,true),(945,true),(952,true),(957,false)]
theorem inp_12900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12900 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 16) (closed_mem 26 16) cl_12900 (by decide) v hb
def cl_12901 : CNF.NClause := [(934,true),(936,true),(943,true),(945,true),(952,false),(957,true)]
theorem inp_12901 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12901 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 16) (closed_mem 26 16) cl_12901 (by decide) v hb
def cl_12902 : CNF.NClause := [(934,true),(936,true),(943,true),(945,false),(952,true),(957,true)]
theorem inp_12902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12902 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 16) (closed_mem 26 16) cl_12902 (by decide) v hb
def cl_12905 : CNF.NClause := [(934,false),(936,true),(943,true),(945,true),(952,true),(957,true)]
theorem inp_12905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12905 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 16) (closed_mem 26 16) cl_12905 (by decide) v hb
def cl_12906 : CNF.NClause := [(932,true),(938,true),(944,true),(945,true),(951,true),(956,false)]
theorem inp_12906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12906 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 17) (closed_mem 26 17) cl_12906 (by decide) v hb
def cl_12912 : CNF.NClause := [(933,true),(937,true),(941,true),(945,true),(954,true),(959,false)]
theorem inp_12912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12912 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 18) (closed_mem 26 18) cl_12912 (by decide) v hb
def cl_12913 : CNF.NClause := [(933,true),(937,true),(941,true),(945,true),(954,false),(959,true)]
theorem inp_12913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12913 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 18) (closed_mem 26 18) cl_12913 (by decide) v hb
def cl_12915 : CNF.NClause := [(933,true),(937,true),(941,false),(945,true),(954,true),(959,true)]
theorem inp_12915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12915 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 18) (closed_mem 26 18) cl_12915 (by decide) v hb
def cl_12920 : CNF.NClause := [(931,true),(939,true),(942,true),(945,false),(953,true),(958,true)]
theorem inp_12920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12920 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 19) (closed_mem 26 19) cl_12920 (by decide) v hb
def cl_12922 : CNF.NClause := [(931,true),(939,false),(942,true),(945,true),(953,true),(958,true)]
theorem inp_12922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12922 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 19) (closed_mem 26 19) cl_12922 (by decide) v hb
def cl_12926 : CNF.NClause := [(935,true),(936,true),(937,true),(938,false),(939,true),(960,true)]
theorem inp_12926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12926 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 20) (closed_mem 26 20) cl_12926 (by decide) v hb
def cl_12927 : CNF.NClause := [(935,true),(936,true),(937,false),(938,true),(939,true),(960,true)]
theorem inp_12927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12927 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 20) (closed_mem 26 20) cl_12927 (by decide) v hb
def cl_12928 : CNF.NClause := [(935,true),(936,false),(937,true),(938,true),(939,true),(960,true)]
theorem inp_12928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12928 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 20) (closed_mem 26 20) cl_12928 (by decide) v hb
def cl_12929 : CNF.NClause := [(935,false),(936,true),(937,true),(938,true),(939,true),(960,true)]
theorem inp_12929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12929 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 20) (closed_mem 26 20) cl_12929 (by decide) v hb
def cl_12930 : CNF.NClause := [(934,true),(935,true),(941,true),(947,true),(953,true),(956,false)]
theorem inp_12930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12930 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 21) (closed_mem 26 21) cl_12930 (by decide) v hb
def cl_12936 : CNF.NClause := [(932,true),(935,true),(943,true),(946,true),(954,true),(958,false)]
theorem inp_12936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12936 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 22) (closed_mem 26 22) cl_12936 (by decide) v hb
def cl_12937 : CNF.NClause := [(932,true),(935,true),(943,true),(946,true),(954,false),(958,true)]
theorem inp_12937 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12937 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 22) (closed_mem 26 22) cl_12937 (by decide) v hb
def cl_12940 : CNF.NClause := [(932,true),(935,false),(943,true),(946,true),(954,true),(958,true)]
theorem inp_12940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12940 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 22) (closed_mem 26 22) cl_12940 (by decide) v hb
def cl_12945 : CNF.NClause := [(933,true),(935,true),(942,false),(949,true),(951,true),(957,true)]
theorem inp_12945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12945 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 23) (closed_mem 26 23) cl_12945 (by decide) v hb
def cl_12946 : CNF.NClause := [(933,true),(935,false),(942,true),(949,true),(951,true),(957,true)]
theorem inp_12946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12946 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 23) (closed_mem 26 23) cl_12946 (by decide) v hb
def cl_12948 : CNF.NClause := [(931,true),(935,true),(944,true),(948,true),(952,true),(959,false)]
theorem inp_12948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12948 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 24) (closed_mem 26 24) cl_12948 (by decide) v hb
def cl_12949 : CNF.NClause := [(931,true),(935,true),(944,true),(948,true),(952,false),(959,true)]
theorem inp_12949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12949 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 24) (closed_mem 26 24) cl_12949 (by decide) v hb
def cl_12951 : CNF.NClause := [(931,true),(935,true),(944,false),(948,true),(952,true),(959,true)]
theorem inp_12951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12951 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 24) (closed_mem 26 24) cl_12951 (by decide) v hb
def cl_12952 : CNF.NClause := [(931,true),(935,false),(944,true),(948,true),(952,true),(959,true)]
theorem inp_12952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12952 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 24) (closed_mem 26 24) cl_12952 (by decide) v hb
def cl_12953 : CNF.NClause := [(931,false),(935,true),(944,true),(948,true),(952,true),(959,true)]
theorem inp_12953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12953 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 24) (closed_mem 26 24) cl_12953 (by decide) v hb
def cl_12956 : CNF.NClause := [(930,true),(931,true),(932,true),(933,false),(934,true),(960,true)]
theorem inp_12956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12956 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 25) (closed_mem 26 25) cl_12956 (by decide) v hb
def cl_12957 : CNF.NClause := [(930,true),(931,true),(932,false),(933,true),(934,true),(960,true)]
theorem inp_12957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12957 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 25) (closed_mem 26 25) cl_12957 (by decide) v hb
def cl_12958 : CNF.NClause := [(930,true),(931,false),(932,true),(933,true),(934,true),(960,true)]
theorem inp_12958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12958 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 25) (closed_mem 26 25) cl_12958 (by decide) v hb
def cl_12960 : CNF.NClause := [(930,true),(939,true),(943,true),(947,true),(951,true),(959,false)]
theorem inp_12960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12960 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 26) (closed_mem 26 26) cl_12960 (by decide) v hb
def cl_12961 : CNF.NClause := [(930,true),(939,true),(943,true),(947,true),(951,false),(959,true)]
theorem inp_12961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12961 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 26) (closed_mem 26 26) cl_12961 (by decide) v hb
def cl_12962 : CNF.NClause := [(930,true),(939,true),(943,true),(947,false),(951,true),(959,true)]
theorem inp_12962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12962 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 26) (closed_mem 26 26) cl_12962 (by decide) v hb
def cl_12963 : CNF.NClause := [(930,true),(939,true),(943,false),(947,true),(951,true),(959,true)]
theorem inp_12963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12963 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 26) (closed_mem 26 26) cl_12963 (by decide) v hb
def cl_12964 : CNF.NClause := [(930,true),(939,false),(943,true),(947,true),(951,true),(959,true)]
theorem inp_12964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12964 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 26) (closed_mem 26 26) cl_12964 (by decide) v hb
def cl_12966 : CNF.NClause := [(930,true),(937,true),(944,true),(946,true),(953,true),(957,false)]
theorem inp_12966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12966 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 27) (closed_mem 26 27) cl_12966 (by decide) v hb
def cl_12967 : CNF.NClause := [(930,true),(937,true),(944,true),(946,true),(953,false),(957,true)]
theorem inp_12967 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12967 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 27) (closed_mem 26 27) cl_12967 (by decide) v hb
def cl_12968 : CNF.NClause := [(930,true),(937,true),(944,true),(946,false),(953,true),(957,true)]
theorem inp_12968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12968 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 27) (closed_mem 26 27) cl_12968 (by decide) v hb
def cl_12969 : CNF.NClause := [(930,true),(937,true),(944,false),(946,true),(953,true),(957,true)]
theorem inp_12969 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12969 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 27) (closed_mem 26 27) cl_12969 (by decide) v hb
def cl_12970 : CNF.NClause := [(930,true),(937,false),(944,true),(946,true),(953,true),(957,true)]
theorem inp_12970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12970 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 27) (closed_mem 26 27) cl_12970 (by decide) v hb
def cl_12972 : CNF.NClause := [(930,true),(938,true),(941,true),(949,true),(952,true),(958,false)]
theorem inp_12972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12972 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 28) (closed_mem 26 28) cl_12972 (by decide) v hb
def cl_12973 : CNF.NClause := [(930,true),(938,true),(941,true),(949,true),(952,false),(958,true)]
theorem inp_12973 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12973 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 28) (closed_mem 26 28) cl_12973 (by decide) v hb
def cl_12974 : CNF.NClause := [(930,true),(938,true),(941,true),(949,false),(952,true),(958,true)]
theorem inp_12974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12974 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 28) (closed_mem 26 28) cl_12974 (by decide) v hb
def cl_12975 : CNF.NClause := [(930,true),(938,true),(941,false),(949,true),(952,true),(958,true)]
theorem inp_12975 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12975 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 26 28) (closed_mem 26 28) cl_12975 (by decide) v hb
end Percolation.NReplay
