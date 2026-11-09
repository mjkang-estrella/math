import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause3875 : CNF.NClause := [(122,true),(31,false),(37,true),(43,false),(49,false),(55,false),(57,true)]
theorem inputList3875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3875 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3875 (by decide) v hb
mask_input "3875|36600545212891136|5316911983139663491759343566636187648"
def inputClause3876 : CNF.NClause := [(122,true),(31,true),(37,true),(43,false),(49,false),(55,false),(57,true)]
theorem inputList3876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3876 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3876 (by decide) v hb
mask_input "3876|36600543065407488|5316911983139663491759343568783671296"
def inputClause3877 : CNF.NClause := [(122,true),(31,false),(37,false),(43,true),(49,false),(55,false),(57,true)]
theorem inputList3877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3877 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3877 (by decide) v hb
mask_input "3877|36591886558822400|5316911983139663491759352225290256384"
def inputClause3878 : CNF.NClause := [(122,true),(31,true),(37,false),(43,true),(49,false),(55,false),(57,true)]
theorem inputList3878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3878 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3878 (by decide) v hb
mask_input "3878|36591884411338752|5316911983139663491759352227437740032"
def inputClause3879 : CNF.NClause := [(122,true),(31,false),(37,true),(43,true),(49,false),(55,false),(57,true)]
theorem inputList3879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3879 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3879 (by decide) v hb
mask_input "3879|36591749119868928|5316911983139663491759352362729209856"
def inputClause3880 : CNF.NClause := [(122,true),(31,true),(37,true),(43,true),(49,false),(55,false),(57,true)]
theorem inputList3880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3880 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3880 (by decide) v hb
mask_input "3880|36591746972385280|5316911983139663491759352364876693504"
def inputClause3881 : CNF.NClause := [(122,true),(31,false),(37,false),(43,false),(49,true),(55,false),(57,true)]
theorem inputList3881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3881 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3881 (by decide) v hb
mask_input "3881|36037732698423296|5316911983139663491759906379150655488"
def inputClause3882 : CNF.NClause := [(122,true),(31,true),(37,false),(43,false),(49,true),(55,false),(57,true)]
theorem inputList3882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3882 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3882 (by decide) v hb
mask_input "3882|36037730550939648|5316911983139663491759906381298139136"
def inputClause3884 : CNF.NClause := [(122,true),(31,true),(37,true),(43,false),(49,true),(55,false),(57,true)]
theorem inputList3884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3884 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3884 (by decide) v hb
mask_input "3884|36037593111986176|5316911983139663491759906518737092608"
def inputClause3885 : CNF.NClause := [(122,true),(31,false),(37,false),(43,true),(49,true),(55,false),(57,true)]
theorem inputList3885 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3885 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3885 (by decide) v hb
mask_input "3885|36028936605401088|5316911983139663491759915175243677696"
def inputClause3886 : CNF.NClause := [(122,true),(31,true),(37,false),(43,true),(49,true),(55,false),(57,true)]
theorem inputList3886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3886 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3886 (by decide) v hb
mask_input "3886|36028934457917440|5316911983139663491759915177391161344"
def inputClause3888 : CNF.NClause := [(122,false),(31,true),(37,true),(43,true),(49,true),(55,false),(57,true)]
theorem inputList3888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3888 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3888 (by decide) v hb
mask_input "3888|5316911983139663491651257038140342272|144687073708736512"
def inputClause3889 : CNF.NClause := [(122,true),(31,false),(37,false),(43,false),(49,false),(55,true),(57,true)]
theorem inputList3889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3889 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3889 (by decide) v hb
mask_input "3889|571885632880640|5316911983139663491795372226216198144"
def inputClause3890 : CNF.NClause := [(122,true),(31,true),(37,false),(43,false),(49,false),(55,true),(57,true)]
theorem inputList3890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3890 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3890 (by decide) v hb
mask_input "3890|571883485396992|5316911983139663491795372228363681792"
def inputClause3891 : CNF.NClause := [(122,true),(31,false),(37,true),(43,false),(49,false),(55,true),(57,true)]
theorem inputList3891 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3891 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3891 (by decide) v hb
mask_input "3891|571748193927168|5316911983139663491795372363655151616"
def inputClause3892 : CNF.NClause := [(122,true),(31,true),(37,true),(43,false),(49,false),(55,true),(57,true)]
theorem inputList3892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3892 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3892 (by decide) v hb
mask_input "3892|571746046443520|5316911983139663491795372365802635264"
def inputClause3894 : CNF.NClause := [(122,true),(31,true),(37,false),(43,true),(49,false),(55,true),(57,true)]
theorem inputList3894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3894 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3894 (by decide) v hb
mask_input "3894|563087392374784|5316911983139663491795381024456704000"
def inputClause3896 : CNF.NClause := [(122,false),(31,true),(37,true),(43,true),(49,false),(55,true),(57,true)]
theorem inputList3896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3896 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3896 (by decide) v hb
mask_input "3896|5316911983139663491615791191074799616|180152920774279168"
def inputClause3897 : CNF.NClause := [(122,true),(31,false),(37,false),(43,false),(49,true),(55,true),(57,true)]
theorem inputList3897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3897 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3897 (by decide) v hb
mask_input "3897|8935679459328|5316911983139663491795935176169619456"
def inputClause3898 : CNF.NClause := [(122,true),(31,true),(37,false),(43,false),(49,true),(55,true),(57,true)]
theorem inputList3898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3898 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3898 (by decide) v hb
mask_input "3898|8933531975680|5316911983139663491795935178317103104"
def inputClause3904 : CNF.NClause := [(122,false),(31,true),(37,true),(43,true),(49,true),(55,true),(57,true)]
theorem inputList3904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3904 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) inputClause3904 (by decide) v hb
mask_input "3904|5316911983139663491615228241121378304|180715870727700480"
def inputClause3905 : CNF.NClause := [(123,true),(31,false),(36,false),(41,false),(46,false),(51,false),(56,false)]
theorem inputList3905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3905 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3905 (by decide) v hb
mask_input "3905|74382032486006784|10633823966279326983230456482242756608"
def inputClause3906 : CNF.NClause := [(123,true),(31,true),(36,false),(41,false),(46,false),(51,false),(56,false)]
theorem inputList3906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3906 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3906 (by decide) v hb
mask_input "3906|74382030338523136|10633823966279326983230456484390240256"
def inputClause3907 : CNF.NClause := [(123,true),(31,false),(36,true),(41,false),(46,false),(51,false),(56,false)]
theorem inputList3907 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3907 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3907 (by decide) v hb
mask_input "3907|74381963766530048|10633823966279326983230456550962233344"
def inputClause3908 : CNF.NClause := [(123,true),(31,true),(36,true),(41,false),(46,false),(51,false),(56,false)]
theorem inputList3908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3908 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3908 (by decide) v hb
mask_input "3908|74381961619046400|10633823966279326983230456553109716992"
def inputClause3909 : CNF.NClause := [(123,true),(31,false),(36,false),(41,true),(46,false),(51,false),(56,false)]
theorem inputList3909 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3909 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3909 (by decide) v hb
mask_input "3909|74379833462751232|10633823966279326983230458681266012160"
def inputClause3910 : CNF.NClause := [(123,true),(31,true),(36,false),(41,true),(46,false),(51,false),(56,false)]
theorem inputList3910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3910 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3910 (by decide) v hb
mask_input "3910|74379831315267584|10633823966279326983230458683413495808"
def inputClause3911 : CNF.NClause := [(123,true),(31,false),(36,true),(41,true),(46,false),(51,false),(56,false)]
theorem inputList3911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3911 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3911 (by decide) v hb
mask_input "3911|74379764743274496|10633823966279326983230458749985488896"
def inputClause3912 : CNF.NClause := [(123,true),(31,true),(36,true),(41,true),(46,false),(51,false),(56,false)]
theorem inputList3912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3912 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3912 (by decide) v hb
mask_input "3912|74379762595790848|10633823966279326983230458752132972544"
def inputClause3913 : CNF.NClause := [(123,true),(31,false),(36,false),(41,false),(46,true),(51,false),(56,false)]
theorem inputList3913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3913 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3913 (by decide) v hb
mask_input "3913|74311663741829120|10633823966279326983230526850986934272"
def inputClause3914 : CNF.NClause := [(123,true),(31,true),(36,false),(41,false),(46,true),(51,false),(56,false)]
theorem inputList3914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3914 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3914 (by decide) v hb
mask_input "3914|74311661594345472|10633823966279326983230526853134417920"
def inputClause3915 : CNF.NClause := [(123,true),(31,false),(36,true),(41,false),(46,true),(51,false),(56,false)]
theorem inputList3915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3915 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3915 (by decide) v hb
mask_input "3915|74311595022352384|10633823966279326983230526919706411008"
def inputClause3918 : CNF.NClause := [(123,true),(31,true),(36,false),(41,true),(46,true),(51,false),(56,false)]
theorem inputList3918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3918 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3918 (by decide) v hb
mask_input "3918|74309462571089920|10633823966279326983230529052157673472"
def inputClause3919 : CNF.NClause := [(123,true),(31,false),(36,true),(41,true),(46,true),(51,false),(56,false)]
theorem inputList3919 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3919 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3919 (by decide) v hb
mask_input "3919|74309395999096832|10633823966279326983230529118729666560"
def inputClause3920 : CNF.NClause := [(123,true),(31,true),(36,true),(41,true),(46,true),(51,false),(56,false)]
theorem inputList3920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3920 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3920 (by decide) v hb
mask_input "3920|74309393851613184|10633823966279326983230529120877150208"
def inputClause3921 : CNF.NClause := [(123,true),(31,false),(36,false),(41,false),(46,false),(51,true),(56,false)]
theorem inputList3921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3921 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3921 (by decide) v hb
mask_input "3921|72130232672321536|10633823966279326983232708282056441856"
def inputClause3922 : CNF.NClause := [(123,true),(31,true),(36,false),(41,false),(46,false),(51,true),(56,false)]
theorem inputList3922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3922 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3922 (by decide) v hb
mask_input "3922|72130230524837888|10633823966279326983232708284203925504"
def inputClause3923 : CNF.NClause := [(123,true),(31,false),(36,true),(41,false),(46,false),(51,true),(56,false)]
theorem inputList3923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3923 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3923 (by decide) v hb
mask_input "3923|72130163952844800|10633823966279326983232708350775918592"
def inputClause3925 : CNF.NClause := [(123,true),(31,false),(36,false),(41,true),(46,false),(51,true),(56,false)]
theorem inputList3925 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3925 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3925 (by decide) v hb
mask_input "3925|72128033649065984|10633823966279326983232710481079697408"
def inputClause3926 : CNF.NClause := [(123,true),(31,true),(36,false),(41,true),(46,false),(51,true),(56,false)]
theorem inputList3926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3926 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3926 (by decide) v hb
mask_input "3926|72128031501582336|10633823966279326983232710483227181056"
end Percolation.MaskChain
