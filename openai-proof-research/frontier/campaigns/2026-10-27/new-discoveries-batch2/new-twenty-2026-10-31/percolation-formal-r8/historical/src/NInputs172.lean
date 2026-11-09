import NInputs171
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_10673 : CNF.NClause := [(562,false),(564,true),(571,true),(573,true),(580,true),(585,true)]
theorem inp_10673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10673 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 16) (closed_mem 14 16) cl_10673 (by decide) v hb
def cl_10677 : CNF.NClause := [(560,true),(566,true),(572,false),(573,true),(579,true),(584,true)]
theorem inp_10677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10677 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 17) (closed_mem 14 17) cl_10677 (by decide) v hb
def cl_10680 : CNF.NClause := [(561,true),(565,true),(569,true),(573,true),(582,true),(587,false)]
theorem inp_10680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10680 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 18) (closed_mem 14 18) cl_10680 (by decide) v hb
def cl_10681 : CNF.NClause := [(561,true),(565,true),(569,true),(573,true),(582,false),(587,true)]
theorem inp_10681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10681 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 18) (closed_mem 14 18) cl_10681 (by decide) v hb
def cl_10682 : CNF.NClause := [(561,true),(565,true),(569,true),(573,false),(582,true),(587,true)]
theorem inp_10682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10682 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 18) (closed_mem 14 18) cl_10682 (by decide) v hb
def cl_10683 : CNF.NClause := [(561,true),(565,true),(569,false),(573,true),(582,true),(587,true)]
theorem inp_10683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10683 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 18) (closed_mem 14 18) cl_10683 (by decide) v hb
def cl_10684 : CNF.NClause := [(561,true),(565,false),(569,true),(573,true),(582,true),(587,true)]
theorem inp_10684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10684 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 18) (closed_mem 14 18) cl_10684 (by decide) v hb
def cl_10686 : CNF.NClause := [(559,true),(567,true),(570,true),(573,true),(581,true),(586,false)]
theorem inp_10686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10686 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 19) (closed_mem 14 19) cl_10686 (by decide) v hb
def cl_10687 : CNF.NClause := [(559,true),(567,true),(570,true),(573,true),(581,false),(586,true)]
theorem inp_10687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10687 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 19) (closed_mem 14 19) cl_10687 (by decide) v hb
def cl_10688 : CNF.NClause := [(559,true),(567,true),(570,true),(573,false),(581,true),(586,true)]
theorem inp_10688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10688 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 19) (closed_mem 14 19) cl_10688 (by decide) v hb
def cl_10689 : CNF.NClause := [(559,true),(567,true),(570,false),(573,true),(581,true),(586,true)]
theorem inp_10689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10689 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 19) (closed_mem 14 19) cl_10689 (by decide) v hb
def cl_10690 : CNF.NClause := [(559,true),(567,false),(570,true),(573,true),(581,true),(586,true)]
theorem inp_10690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10690 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 19) (closed_mem 14 19) cl_10690 (by decide) v hb
def cl_10691 : CNF.NClause := [(559,false),(567,true),(570,true),(573,true),(581,true),(586,true)]
theorem inp_10691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10691 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 19) (closed_mem 14 19) cl_10691 (by decide) v hb
def cl_10693 : CNF.NClause := [(563,true),(564,true),(565,true),(566,true),(567,false),(588,true)]
theorem inp_10693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10693 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 20) (closed_mem 14 20) cl_10693 (by decide) v hb
def cl_10694 : CNF.NClause := [(563,true),(564,true),(565,true),(566,false),(567,true),(588,true)]
theorem inp_10694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10694 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 20) (closed_mem 14 20) cl_10694 (by decide) v hb
def cl_10695 : CNF.NClause := [(563,true),(564,true),(565,false),(566,true),(567,true),(588,true)]
theorem inp_10695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10695 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 20) (closed_mem 14 20) cl_10695 (by decide) v hb
def cl_10696 : CNF.NClause := [(563,true),(564,false),(565,true),(566,true),(567,true),(588,true)]
theorem inp_10696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10696 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 20) (closed_mem 14 20) cl_10696 (by decide) v hb
def cl_10697 : CNF.NClause := [(563,false),(564,true),(565,true),(566,true),(567,true),(588,true)]
theorem inp_10697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10697 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 20) (closed_mem 14 20) cl_10697 (by decide) v hb
def cl_10699 : CNF.NClause := [(562,true),(563,true),(569,true),(575,true),(581,false),(584,true)]
theorem inp_10699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10699 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 21) (closed_mem 14 21) cl_10699 (by decide) v hb
def cl_10703 : CNF.NClause := [(562,false),(563,true),(569,true),(575,true),(581,true),(584,true)]
theorem inp_10703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10703 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 21) (closed_mem 14 21) cl_10703 (by decide) v hb
def cl_10704 : CNF.NClause := [(560,true),(563,true),(571,true),(574,true),(582,true),(586,false)]
theorem inp_10704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10704 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 22) (closed_mem 14 22) cl_10704 (by decide) v hb
def cl_10705 : CNF.NClause := [(560,true),(563,true),(571,true),(574,true),(582,false),(586,true)]
theorem inp_10705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10705 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 22) (closed_mem 14 22) cl_10705 (by decide) v hb
def cl_10706 : CNF.NClause := [(560,true),(563,true),(571,true),(574,false),(582,true),(586,true)]
theorem inp_10706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10706 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 22) (closed_mem 14 22) cl_10706 (by decide) v hb
def cl_10707 : CNF.NClause := [(560,true),(563,true),(571,false),(574,true),(582,true),(586,true)]
theorem inp_10707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10707 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 22) (closed_mem 14 22) cl_10707 (by decide) v hb
def cl_10708 : CNF.NClause := [(560,true),(563,false),(571,true),(574,true),(582,true),(586,true)]
theorem inp_10708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10708 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 22) (closed_mem 14 22) cl_10708 (by decide) v hb
def cl_10709 : CNF.NClause := [(560,false),(563,true),(571,true),(574,true),(582,true),(586,true)]
theorem inp_10709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10709 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 22) (closed_mem 14 22) cl_10709 (by decide) v hb
def cl_10711 : CNF.NClause := [(561,true),(563,true),(570,true),(577,true),(579,false),(585,true)]
theorem inp_10711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10711 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 23) (closed_mem 14 23) cl_10711 (by decide) v hb
def cl_10712 : CNF.NClause := [(561,true),(563,true),(570,true),(577,false),(579,true),(585,true)]
theorem inp_10712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10712 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 23) (closed_mem 14 23) cl_10712 (by decide) v hb
def cl_10713 : CNF.NClause := [(561,true),(563,true),(570,false),(577,true),(579,true),(585,true)]
theorem inp_10713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10713 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 23) (closed_mem 14 23) cl_10713 (by decide) v hb
def cl_10714 : CNF.NClause := [(561,true),(563,false),(570,true),(577,true),(579,true),(585,true)]
theorem inp_10714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10714 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 23) (closed_mem 14 23) cl_10714 (by decide) v hb
def cl_10715 : CNF.NClause := [(561,false),(563,true),(570,true),(577,true),(579,true),(585,true)]
theorem inp_10715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10715 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 23) (closed_mem 14 23) cl_10715 (by decide) v hb
def cl_10719 : CNF.NClause := [(559,true),(563,true),(572,false),(576,true),(580,true),(587,true)]
theorem inp_10719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10719 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 24) (closed_mem 14 24) cl_10719 (by decide) v hb
def cl_10723 : CNF.NClause := [(558,true),(559,true),(560,true),(561,true),(562,false),(588,true)]
theorem inp_10723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10723 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 25) (closed_mem 14 25) cl_10723 (by decide) v hb
def cl_10724 : CNF.NClause := [(558,true),(559,true),(560,true),(561,false),(562,true),(588,true)]
theorem inp_10724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10724 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 25) (closed_mem 14 25) cl_10724 (by decide) v hb
def cl_10725 : CNF.NClause := [(558,true),(559,true),(560,false),(561,true),(562,true),(588,true)]
theorem inp_10725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10725 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 25) (closed_mem 14 25) cl_10725 (by decide) v hb
def cl_10726 : CNF.NClause := [(558,true),(559,false),(560,true),(561,true),(562,true),(588,true)]
theorem inp_10726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10726 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 25) (closed_mem 14 25) cl_10726 (by decide) v hb
def cl_10728 : CNF.NClause := [(558,true),(567,true),(571,true),(575,true),(579,true),(587,false)]
theorem inp_10728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10728 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 26) (closed_mem 14 26) cl_10728 (by decide) v hb
def cl_10729 : CNF.NClause := [(558,true),(567,true),(571,true),(575,true),(579,false),(587,true)]
theorem inp_10729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10729 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 26) (closed_mem 14 26) cl_10729 (by decide) v hb
def cl_10730 : CNF.NClause := [(558,true),(567,true),(571,true),(575,false),(579,true),(587,true)]
theorem inp_10730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10730 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 26) (closed_mem 14 26) cl_10730 (by decide) v hb
def cl_10731 : CNF.NClause := [(558,true),(567,true),(571,false),(575,true),(579,true),(587,true)]
theorem inp_10731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10731 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 26) (closed_mem 14 26) cl_10731 (by decide) v hb
def cl_10732 : CNF.NClause := [(558,true),(567,false),(571,true),(575,true),(579,true),(587,true)]
theorem inp_10732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10732 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 26) (closed_mem 14 26) cl_10732 (by decide) v hb
def cl_10737 : CNF.NClause := [(558,true),(565,true),(572,false),(574,true),(581,true),(585,true)]
theorem inp_10737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10737 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 27) (closed_mem 14 27) cl_10737 (by decide) v hb
def cl_10740 : CNF.NClause := [(558,true),(566,true),(569,true),(577,true),(580,true),(586,false)]
theorem inp_10740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10740 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 28) (closed_mem 14 28) cl_10740 (by decide) v hb
def cl_10741 : CNF.NClause := [(558,true),(566,true),(569,true),(577,true),(580,false),(586,true)]
theorem inp_10741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10741 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 28) (closed_mem 14 28) cl_10741 (by decide) v hb
def cl_10742 : CNF.NClause := [(558,true),(566,true),(569,true),(577,false),(580,true),(586,true)]
theorem inp_10742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10742 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 28) (closed_mem 14 28) cl_10742 (by decide) v hb
def cl_10743 : CNF.NClause := [(558,true),(566,true),(569,false),(577,true),(580,true),(586,true)]
theorem inp_10743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10743 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 28) (closed_mem 14 28) cl_10743 (by decide) v hb
def cl_10744 : CNF.NClause := [(558,true),(566,false),(569,true),(577,true),(580,true),(586,true)]
theorem inp_10744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10744 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 28) (closed_mem 14 28) cl_10744 (by decide) v hb
def cl_10746 : CNF.NClause := [(558,true),(564,true),(570,true),(576,true),(582,true),(584,false)]
theorem inp_10746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10746 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 29) (closed_mem 14 29) cl_10746 (by decide) v hb
def cl_10747 : CNF.NClause := [(558,true),(564,true),(570,true),(576,true),(582,false),(584,true)]
theorem inp_10747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10747 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 29) (closed_mem 14 29) cl_10747 (by decide) v hb
def cl_10748 : CNF.NClause := [(558,true),(564,true),(570,true),(576,false),(582,true),(584,true)]
theorem inp_10748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_10748 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (closedGate5 14 29) (closed_mem 14 29) cl_10748 (by decide) v hb
end Percolation.NReplay
