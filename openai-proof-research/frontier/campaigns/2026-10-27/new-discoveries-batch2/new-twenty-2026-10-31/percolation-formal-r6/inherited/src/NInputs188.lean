import NInputs187
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_12122 : CNF.NClause := [(816,true),(817,true),(818,true),(819,false),(820,true),(836,true)]
theorem inp_12122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12122 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 10) (closed_mem 22 10) cl_12122 (by decide) v hb
def cl_12123 : CNF.NClause := [(816,true),(817,true),(818,false),(819,true),(820,true),(836,true)]
theorem inp_12123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12123 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 10) (closed_mem 22 10) cl_12123 (by decide) v hb
def cl_12124 : CNF.NClause := [(816,true),(817,false),(818,true),(819,true),(820,true),(836,true)]
theorem inp_12124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12124 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 10) (closed_mem 22 10) cl_12124 (by decide) v hb
def cl_12125 : CNF.NClause := [(816,false),(817,true),(818,true),(819,true),(820,true),(836,true)]
theorem inp_12125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12125 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 10) (closed_mem 22 10) cl_12125 (by decide) v hb
def cl_12127 : CNF.NClause := [(810,true),(813,true),(816,true),(824,true),(827,false),(834,true)]
theorem inp_12127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12127 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 11) (closed_mem 22 11) cl_12127 (by decide) v hb
def cl_12128 : CNF.NClause := [(810,true),(813,true),(816,true),(824,false),(827,true),(834,true)]
theorem inp_12128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12128 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 11) (closed_mem 22 11) cl_12128 (by decide) v hb
def cl_12129 : CNF.NClause := [(810,true),(813,true),(816,false),(824,true),(827,true),(834,true)]
theorem inp_12129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12129 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 11) (closed_mem 22 11) cl_12129 (by decide) v hb
def cl_12130 : CNF.NClause := [(810,true),(813,false),(816,true),(824,true),(827,true),(834,true)]
theorem inp_12130 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12130 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 11) (closed_mem 22 11) cl_12130 (by decide) v hb
def cl_12131 : CNF.NClause := [(810,false),(813,true),(816,true),(824,true),(827,true),(834,true)]
theorem inp_12131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12131 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 11) (closed_mem 22 11) cl_12131 (by decide) v hb
def cl_12133 : CNF.NClause := [(808,true),(812,true),(816,true),(825,true),(829,false),(835,true)]
theorem inp_12133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12133 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_12133 v hb
def cl_12134 : CNF.NClause := [(808,true),(812,true),(816,true),(825,false),(829,true),(835,true)]
theorem inp_12134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12134 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 12) (closed_mem 22 12) cl_12134 (by decide) v hb
def cl_12135 : CNF.NClause := [(808,true),(812,true),(816,false),(825,true),(829,true),(835,true)]
theorem inp_12135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12135 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 12) (closed_mem 22 12) cl_12135 (by decide) v hb
def cl_12136 : CNF.NClause := [(808,true),(812,false),(816,true),(825,true),(829,true),(835,true)]
theorem inp_12136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12136 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 12) (closed_mem 22 12) cl_12136 (by decide) v hb
def cl_12137 : CNF.NClause := [(808,false),(812,true),(816,true),(825,true),(829,true),(835,true)]
theorem inp_12137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12137 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 12) (closed_mem 22 12) cl_12137 (by decide) v hb
def cl_12139 : CNF.NClause := [(809,true),(815,true),(816,true),(822,true),(828,false),(832,true)]
theorem inp_12139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12139 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 13) (closed_mem 22 13) cl_12139 (by decide) v hb
def cl_12144 : CNF.NClause := [(807,true),(814,true),(816,true),(823,true),(830,true),(833,false)]
theorem inp_12144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12144 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 14) (closed_mem 22 14) cl_12144 (by decide) v hb
def cl_12146 : CNF.NClause := [(807,true),(814,true),(816,true),(823,false),(830,true),(833,true)]
theorem inp_12146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12146 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 14) (closed_mem 22 14) cl_12146 (by decide) v hb
def cl_12147 : CNF.NClause := [(807,true),(814,true),(816,false),(823,true),(830,true),(833,true)]
theorem inp_12147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12147 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 14) (closed_mem 22 14) cl_12147 (by decide) v hb
def cl_12148 : CNF.NClause := [(807,true),(814,false),(816,true),(823,true),(830,true),(833,true)]
theorem inp_12148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12148 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 14) (closed_mem 22 14) cl_12148 (by decide) v hb
def cl_12149 : CNF.NClause := [(807,false),(814,true),(816,true),(823,true),(830,true),(833,true)]
theorem inp_12149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12149 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 14) (closed_mem 22 14) cl_12149 (by decide) v hb
def cl_12151 : CNF.NClause := [(821,true),(822,true),(823,true),(824,true),(825,false),(836,true)]
theorem inp_12151 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12151 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 15) (closed_mem 22 15) cl_12151 (by decide) v hb
def cl_12153 : CNF.NClause := [(821,true),(822,true),(823,false),(824,true),(825,true),(836,true)]
theorem inp_12153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12153 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 15) (closed_mem 22 15) cl_12153 (by decide) v hb
def cl_12154 : CNF.NClause := [(821,true),(822,false),(823,true),(824,true),(825,true),(836,true)]
theorem inp_12154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12154 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 15) (closed_mem 22 15) cl_12154 (by decide) v hb
def cl_12155 : CNF.NClause := [(821,false),(822,true),(823,true),(824,true),(825,true),(836,true)]
theorem inp_12155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12155 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 15) (closed_mem 22 15) cl_12155 (by decide) v hb
def cl_12157 : CNF.NClause := [(810,true),(812,true),(819,true),(821,true),(828,false),(833,true)]
theorem inp_12157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12157 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 16) (closed_mem 22 16) cl_12157 (by decide) v hb
def cl_12162 : CNF.NClause := [(808,true),(814,true),(820,true),(821,true),(827,true),(832,false)]
theorem inp_12162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12162 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 17) (closed_mem 22 17) cl_12162 (by decide) v hb
def cl_12163 : CNF.NClause := [(808,true),(814,true),(820,true),(821,true),(827,false),(832,true)]
theorem inp_12163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12163 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 17) (closed_mem 22 17) cl_12163 (by decide) v hb
def cl_12164 : CNF.NClause := [(808,true),(814,true),(820,true),(821,false),(827,true),(832,true)]
theorem inp_12164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12164 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 17) (closed_mem 22 17) cl_12164 (by decide) v hb
def cl_12165 : CNF.NClause := [(808,true),(814,true),(820,false),(821,true),(827,true),(832,true)]
theorem inp_12165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12165 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 17) (closed_mem 22 17) cl_12165 (by decide) v hb
def cl_12167 : CNF.NClause := [(808,false),(814,true),(820,true),(821,true),(827,true),(832,true)]
theorem inp_12167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12167 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 17) (closed_mem 22 17) cl_12167 (by decide) v hb
def cl_12168 : CNF.NClause := [(809,true),(813,true),(817,true),(821,true),(830,true),(835,false)]
theorem inp_12168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12168 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 18) (closed_mem 22 18) cl_12168 (by decide) v hb
def cl_12170 : CNF.NClause := [(809,true),(813,true),(817,true),(821,false),(830,true),(835,true)]
theorem inp_12170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12170 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 18) (closed_mem 22 18) cl_12170 (by decide) v hb
def cl_12171 : CNF.NClause := [(809,true),(813,true),(817,false),(821,true),(830,true),(835,true)]
theorem inp_12171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12171 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 18) (closed_mem 22 18) cl_12171 (by decide) v hb
def cl_12172 : CNF.NClause := [(809,true),(813,false),(817,true),(821,true),(830,true),(835,true)]
theorem inp_12172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12172 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 18) (closed_mem 22 18) cl_12172 (by decide) v hb
def cl_12173 : CNF.NClause := [(809,false),(813,true),(817,true),(821,true),(830,true),(835,true)]
theorem inp_12173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12173 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 18) (closed_mem 22 18) cl_12173 (by decide) v hb
def cl_12174 : CNF.NClause := [(807,true),(815,true),(818,true),(821,true),(829,true),(834,false)]
theorem inp_12174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12174 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 19) (closed_mem 22 19) cl_12174 (by decide) v hb
def cl_12177 : CNF.NClause := [(807,true),(815,true),(818,false),(821,true),(829,true),(834,true)]
theorem inp_12177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12177 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 19) (closed_mem 22 19) cl_12177 (by decide) v hb
def cl_12178 : CNF.NClause := [(807,true),(815,false),(818,true),(821,true),(829,true),(834,true)]
theorem inp_12178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12178 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 19) (closed_mem 22 19) cl_12178 (by decide) v hb
def cl_12179 : CNF.NClause := [(807,false),(815,true),(818,true),(821,true),(829,true),(834,true)]
theorem inp_12179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12179 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 19) (closed_mem 22 19) cl_12179 (by decide) v hb
def cl_12181 : CNF.NClause := [(811,true),(812,true),(813,true),(814,true),(815,false),(836,true)]
theorem inp_12181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12181 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 20) (closed_mem 22 20) cl_12181 (by decide) v hb
def cl_12182 : CNF.NClause := [(811,true),(812,true),(813,true),(814,false),(815,true),(836,true)]
theorem inp_12182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12182 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 20) (closed_mem 22 20) cl_12182 (by decide) v hb
def cl_12183 : CNF.NClause := [(811,true),(812,true),(813,false),(814,true),(815,true),(836,true)]
theorem inp_12183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12183 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 20) (closed_mem 22 20) cl_12183 (by decide) v hb
def cl_12184 : CNF.NClause := [(811,true),(812,false),(813,true),(814,true),(815,true),(836,true)]
theorem inp_12184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12184 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 20) (closed_mem 22 20) cl_12184 (by decide) v hb
def cl_12185 : CNF.NClause := [(811,false),(812,true),(813,true),(814,true),(815,true),(836,true)]
theorem inp_12185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12185 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 20) (closed_mem 22 20) cl_12185 (by decide) v hb
def cl_12186 : CNF.NClause := [(810,true),(811,true),(817,true),(823,true),(829,true),(832,false)]
theorem inp_12186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12186 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 21) (closed_mem 22 21) cl_12186 (by decide) v hb
def cl_12187 : CNF.NClause := [(810,true),(811,true),(817,true),(823,true),(829,false),(832,true)]
theorem inp_12187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12187 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 21) (closed_mem 22 21) cl_12187 (by decide) v hb
def cl_12190 : CNF.NClause := [(810,true),(811,false),(817,true),(823,true),(829,true),(832,true)]
theorem inp_12190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12190 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 21) (closed_mem 22 21) cl_12190 (by decide) v hb
def cl_12191 : CNF.NClause := [(810,false),(811,true),(817,true),(823,true),(829,true),(832,true)]
theorem inp_12191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12191 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 21) (closed_mem 22 21) cl_12191 (by decide) v hb
def cl_12192 : CNF.NClause := [(808,true),(811,true),(819,true),(822,true),(830,true),(834,false)]
theorem inp_12192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12192 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 22) (closed_mem 22 22) cl_12192 (by decide) v hb
def cl_12193 : CNF.NClause := [(808,true),(811,true),(819,true),(822,true),(830,false),(834,true)]
theorem inp_12193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_12193 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 22 22) (closed_mem 22 22) cl_12193 (by decide) v hb
end Percolation.NReplay
