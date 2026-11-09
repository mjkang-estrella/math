import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause4795 : CNF.NClause := [(37,false),(6,false),(66,true),(70,false),(74,true),(78,true),(82,true),(91,false)]
theorem inputList4795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4795 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4795 (by decide) v hb
mask_input "4795|2475881259162381404648505408|5156897986269947411562496"
def inputClause4796 : CNF.NClause := [(37,false),(6,true),(66,true),(70,false),(74,true),(78,true),(82,true),(91,false)]
theorem inputList4796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4796 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4796 (by decide) v hb
mask_input "4796|2475881259162381404648505344|5156897986269947411562560"
def inputClause4797 : CNF.NClause := [(37,false),(6,false),(66,false),(70,true),(74,true),(78,true),(82,true),(91,false)]
theorem inputList4797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4797 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4797 (by decide) v hb
mask_input "4797|2475880152357736982075408448|5158004790914369984659456"
def inputClause4798 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,true),(78,true),(82,true),(91,false)]
theorem inputList4798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4798 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4798 (by decide) v hb
mask_input "4798|2475880152357736982075408384|5158004790914369984659520"
def inputClause4799 : CNF.NClause := [(37,false),(6,false),(66,true),(70,true),(74,true),(78,true),(82,true),(91,false)]
theorem inputList4799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4799 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4799 (by decide) v hb
mask_input "4799|2475880078570760687237201984|5158078577890664822865920"
def inputClause4800 : CNF.NClause := [(37,false),(6,true),(66,true),(70,true),(74,true),(78,true),(82,true),(91,false)]
theorem inputList4800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4800 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4800 (by decide) v hb
mask_input "4800|2475880078570760687237201920|5158078577890664822865984"
def inputClause4802 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,false),(78,false),(82,false),(91,true)]
theorem inputList4802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4802 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4802 (by decide) v hb
mask_input "4802|5158078577890802261819392|2475880078570760549798248512"
def inputClause4803 : CNF.NClause := [(37,false),(6,false),(66,true),(70,false),(74,false),(78,false),(82,false),(91,true)]
theorem inputList4803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4803 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4803 (by decide) v hb
mask_input "4803|5158004790914507423612992|2475880152357736844636454912"
def inputClause4804 : CNF.NClause := [(37,false),(6,true),(66,true),(70,false),(74,false),(78,false),(82,false),(91,true)]
theorem inputList4804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4804 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4804 (by decide) v hb
mask_input "4804|5158004790914507423612928|2475880152357736844636454976"
def inputClause4805 : CNF.NClause := [(37,false),(6,false),(66,false),(70,true),(74,false),(78,false),(82,false),(91,true)]
theorem inputList4805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4805 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4805 (by decide) v hb
mask_input "4805|5156897986270084850516032|2475881259162381267209551872"
def inputClause4806 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,false),(78,false),(82,false),(91,true)]
theorem inputList4806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4806 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4806 (by decide) v hb
mask_input "4806|5156897986270084850515968|2475881259162381267209551936"
def inputClause4807 : CNF.NClause := [(37,false),(6,false),(66,true),(70,true),(74,false),(78,false),(82,false),(91,true)]
theorem inputList4807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4807 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4807 (by decide) v hb
mask_input "4807|5156824199293790012309568|2475881332949357562047758336"
def inputClause4808 : CNF.NClause := [(37,false),(6,true),(66,true),(70,true),(74,false),(78,false),(82,false),(91,true)]
theorem inputList4808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4808 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4808 (by decide) v hb
mask_input "4808|5156824199293790012309504|2475881332949357562047758400"
def inputClause4809 : CNF.NClause := [(37,false),(6,false),(66,false),(70,false),(74,true),(78,false),(82,false),(91,true)]
theorem inputList4809 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4809 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4809 (by decide) v hb
mask_input "4809|5139189111959323680964672|2475898968036692028379103232"
def inputClause4810 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,true),(78,false),(82,false),(91,true)]
theorem inputList4810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4810 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4810 (by decide) v hb
mask_input "4810|5139189111959323680964608|2475898968036692028379103296"
def inputClause4811 : CNF.NClause := [(37,false),(6,false),(66,true),(70,false),(74,true),(78,false),(82,false),(91,true)]
theorem inputList4811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4811 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4811 (by decide) v hb
mask_input "4811|5139115324983028842758208|2475899041823668323217309696"
def inputClause4812 : CNF.NClause := [(37,false),(6,true),(66,true),(70,false),(74,true),(78,false),(82,false),(91,true)]
theorem inputList4812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4812 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4812 (by decide) v hb
mask_input "4812|5139115324983028842758144|2475899041823668323217309760"
def inputClause4814 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,true),(78,false),(82,false),(91,true)]
theorem inputList4814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4814 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4814 (by decide) v hb
mask_input "4814|5138008520338606269661184|2475900148628312745790406720"
def inputClause4815 : CNF.NClause := [(37,false),(6,false),(66,true),(70,true),(74,true),(78,false),(82,false),(91,true)]
theorem inputList4815 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4815 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4815 (by decide) v hb
mask_input "4815|5137934733362311431454784|2475900222415289040628613120"
def inputClause4816 : CNF.NClause := [(37,false),(6,true),(66,true),(70,true),(74,true),(78,false),(82,false),(91,true)]
theorem inputList4816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4816 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4816 (by decide) v hb
mask_input "4816|5137934733362311431454720|2475900222415289040628613184"
def inputClause4817 : CNF.NClause := [(37,false),(6,false),(66,false),(70,false),(74,false),(78,true),(82,false),(91,true)]
theorem inputList4817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4817 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4817 (by decide) v hb
mask_input "4817|4855847122987144968142912|2476182310025664207091924992"
def inputClause4818 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,false),(78,true),(82,false),(91,true)]
theorem inputList4818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4818 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4818 (by decide) v hb
mask_input "4818|4855847122987144968142848|2476182310025664207091925056"
def inputClause4819 : CNF.NClause := [(37,false),(6,false),(66,true),(70,false),(74,false),(78,true),(82,false),(91,true)]
theorem inputList4819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4819 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4819 (by decide) v hb
mask_input "4819|4855773336010850129936448|2476182383812640501930131456"
def inputClause4820 : CNF.NClause := [(37,false),(6,true),(66,true),(70,false),(74,false),(78,true),(82,false),(91,true)]
theorem inputList4820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4820 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4820 (by decide) v hb
mask_input "4820|4855773336010850129936384|2476182383812640501930131520"
def inputClause4821 : CNF.NClause := [(37,false),(6,false),(66,false),(70,true),(74,false),(78,true),(82,false),(91,true)]
theorem inputList4821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4821 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4821 (by decide) v hb
mask_input "4821|4854666531366427556839488|2476183490617284924503228416"
def inputClause4822 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,false),(78,true),(82,false),(91,true)]
theorem inputList4822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4822 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4822 (by decide) v hb
mask_input "4822|4854666531366427556839424|2476183490617284924503228480"
def inputClause4824 : CNF.NClause := [(37,false),(6,true),(66,true),(70,true),(74,false),(78,true),(82,false),(91,true)]
theorem inputList4824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4824 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4824 (by decide) v hb
mask_input "4824|4854592744390132718632960|2476183564404261219341434944"
def inputClause4825 : CNF.NClause := [(37,false),(6,false),(66,false),(70,false),(74,true),(78,true),(82,false),(91,true)]
theorem inputList4825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4825 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4825 (by decide) v hb
mask_input "4825|4836957657055666387288128|2476201199491595685672779776"
def inputClause4826 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,true),(78,true),(82,false),(91,true)]
theorem inputList4826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4826 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4826 (by decide) v hb
mask_input "4826|4836957657055666387288064|2476201199491595685672779840"
def inputClause4827 : CNF.NClause := [(37,false),(6,false),(66,true),(70,false),(74,true),(78,true),(82,false),(91,true)]
theorem inputList4827 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4827 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4827 (by decide) v hb
mask_input "4827|4836883870079371549081664|2476201273278571980510986240"
def inputClause4828 : CNF.NClause := [(37,false),(6,true),(66,true),(70,false),(74,true),(78,true),(82,false),(91,true)]
theorem inputList4828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4828 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4828 (by decide) v hb
mask_input "4828|4836883870079371549081600|2476201273278571980510986304"
def inputClause4829 : CNF.NClause := [(37,false),(6,false),(66,false),(70,true),(74,true),(78,true),(82,false),(91,true)]
theorem inputList4829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4829 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4829 (by decide) v hb
mask_input "4829|4835777065434948975984704|2476202380083216403084083200"
def inputClause4830 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,true),(78,true),(82,false),(91,true)]
theorem inputList4830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4830 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4830 (by decide) v hb
mask_input "4830|4835777065434948975984640|2476202380083216403084083264"
def inputClause4832 : CNF.NClause := [(37,false),(6,true),(66,true),(70,true),(74,true),(78,true),(82,false),(91,true)]
theorem inputList4832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4832 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4832 (by decide) v hb
mask_input "4832|4835703278458654137778176|2476202453870192697922289728"
def inputClause4833 : CNF.NClause := [(37,false),(6,false),(66,false),(70,false),(74,false),(78,false),(82,true),(91,true)]
theorem inputList4833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4833 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4833 (by decide) v hb
mask_input "4833|322375299432285562994752|2480715781849219066497073152"
def inputClause4834 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,false),(78,false),(82,true),(91,true)]
theorem inputList4834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4834 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4834 (by decide) v hb
mask_input "4834|322375299432285562994688|2480715781849219066497073216"
def inputClause4835 : CNF.NClause := [(37,false),(6,false),(66,true),(70,false),(74,false),(78,false),(82,true),(91,true)]
theorem inputList4835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4835 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4835 (by decide) v hb
mask_input "4835|322301512455990724788288|2480715855636195361335279616"
def inputClause4836 : CNF.NClause := [(37,false),(6,true),(66,true),(70,false),(74,false),(78,false),(82,true),(91,true)]
theorem inputList4836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4836 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4836 (by decide) v hb
mask_input "4836|322301512455990724788224|2480715855636195361335279680"
def inputClause4837 : CNF.NClause := [(37,false),(6,false),(66,false),(70,true),(74,false),(78,false),(82,true),(91,true)]
theorem inputList4837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4837 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4837 (by decide) v hb
mask_input "4837|321194707811568151691328|2480716962440839783908376576"
def inputClause4838 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,false),(78,false),(82,true),(91,true)]
theorem inputList4838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4838 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4838 (by decide) v hb
mask_input "4838|321194707811568151691264|2480716962440839783908376640"
end Percolation.MaskChain
