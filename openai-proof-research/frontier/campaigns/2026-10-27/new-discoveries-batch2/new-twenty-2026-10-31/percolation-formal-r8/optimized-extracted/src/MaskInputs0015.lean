import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause876 : CNF.NClause := [(75,true),(3,true),(9,true),(10,false),(16,true),(22,false),(26,true)]
theorem inputList876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause876 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause876 (by decide) v hb
mask_input "876|4195328|37778931862957228884488"
def inputClause877 : CNF.NClause := [(75,true),(3,false),(9,false),(10,true),(16,true),(22,false),(26,true)]
theorem inputList877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause877 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause877 (by decide) v hb
mask_input "877|4194824|37778931862957228884992"
def inputClause878 : CNF.NClause := [(75,true),(3,true),(9,false),(10,true),(16,true),(22,false),(26,true)]
theorem inputList878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause878 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause878 (by decide) v hb
mask_input "878|4194816|37778931862957228885000"
def inputClause879 : CNF.NClause := [(75,true),(3,false),(9,true),(10,true),(16,true),(22,false),(26,true)]
theorem inputList879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause879 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause879 (by decide) v hb
mask_input "879|4194312|37778931862957228885504"
def inputClause881 : CNF.NClause := [(75,true),(3,false),(9,false),(10,false),(16,false),(22,true),(26,true)]
theorem inputList881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause881 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause881 (by decide) v hb
mask_input "881|67080|37778931862957233012736"
def inputClause882 : CNF.NClause := [(75,true),(3,true),(9,false),(10,false),(16,false),(22,true),(26,true)]
theorem inputList882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause882 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause882 (by decide) v hb
mask_input "882|67072|37778931862957233012744"
def inputClause883 : CNF.NClause := [(75,true),(3,false),(9,true),(10,false),(16,false),(22,true),(26,true)]
theorem inputList883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause883 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause883 (by decide) v hb
mask_input "883|66568|37778931862957233013248"
def inputClause884 : CNF.NClause := [(75,true),(3,true),(9,true),(10,false),(16,false),(22,true),(26,true)]
theorem inputList884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause884 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause884 (by decide) v hb
mask_input "884|66560|37778931862957233013256"
def inputClause885 : CNF.NClause := [(75,true),(3,false),(9,false),(10,true),(16,false),(22,true),(26,true)]
theorem inputList885 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause885 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause885 (by decide) v hb
mask_input "885|66056|37778931862957233013760"
def inputClause886 : CNF.NClause := [(75,true),(3,true),(9,false),(10,true),(16,false),(22,true),(26,true)]
theorem inputList886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause886 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause886 (by decide) v hb
mask_input "886|66048|37778931862957233013768"
def inputClause887 : CNF.NClause := [(75,true),(3,false),(9,true),(10,true),(16,false),(22,true),(26,true)]
theorem inputList887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause887 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause887 (by decide) v hb
mask_input "887|65544|37778931862957233014272"
def inputClause889 : CNF.NClause := [(75,true),(3,false),(9,false),(10,false),(16,true),(22,true),(26,true)]
theorem inputList889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause889 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause889 (by decide) v hb
mask_input "889|1544|37778931862957233078272"
def inputClause890 : CNF.NClause := [(75,true),(3,true),(9,false),(10,false),(16,true),(22,true),(26,true)]
theorem inputList890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause890 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause890 (by decide) v hb
mask_input "890|1536|37778931862957233078280"
def inputClause891 : CNF.NClause := [(75,true),(3,false),(9,true),(10,false),(16,true),(22,true),(26,true)]
theorem inputList891 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause891 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause891 (by decide) v hb
mask_input "891|1032|37778931862957233078784"
def inputClause893 : CNF.NClause := [(75,true),(3,false),(9,false),(10,true),(16,true),(22,true),(26,true)]
theorem inputList893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause893 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause893 (by decide) v hb
mask_input "893|520|37778931862957233079296"
def inputClause894 : CNF.NClause := [(75,false),(3,true),(9,false),(10,true),(16,true),(22,true),(26,true)]
theorem inputList894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause894 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause894 (by decide) v hb
mask_input "894|37778931862957161710080|71369736"
def inputClause896 : CNF.NClause := [(75,false),(3,true),(9,true),(10,true),(16,true),(22,true),(26,true)]
theorem inputList896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause896 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) inputClause896 (by decide) v hb
mask_input "896|37778931862957161709568|71370248"
def inputClause897 : CNF.NClause := [(76,true),(1,false),(8,false),(10,false),(17,false),(24,false),(27,false)]
theorem inputList897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause897 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause897 (by decide) v hb
mask_input "897|151127298|75557863725914323419136"
def inputClause898 : CNF.NClause := [(76,true),(1,true),(8,false),(10,false),(17,false),(24,false),(27,false)]
theorem inputList898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause898 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause898 (by decide) v hb
mask_input "898|151127296|75557863725914323419138"
def inputClause899 : CNF.NClause := [(76,true),(1,false),(8,true),(10,false),(17,false),(24,false),(27,false)]
theorem inputList899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause899 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause899 (by decide) v hb
mask_input "899|151127042|75557863725914323419392"
def inputClause900 : CNF.NClause := [(76,true),(1,true),(8,true),(10,false),(17,false),(24,false),(27,false)]
theorem inputList900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause900 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause900 (by decide) v hb
mask_input "900|151127040|75557863725914323419394"
def inputClause901 : CNF.NClause := [(76,true),(1,false),(8,false),(10,true),(17,false),(24,false),(27,false)]
theorem inputList901 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause901 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause901 (by decide) v hb
mask_input "901|151126274|75557863725914323420160"
def inputClause902 : CNF.NClause := [(76,true),(1,true),(8,false),(10,true),(17,false),(24,false),(27,false)]
theorem inputList902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause902 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause902 (by decide) v hb
mask_input "902|151126272|75557863725914323420162"
def inputClause903 : CNF.NClause := [(76,true),(1,false),(8,true),(10,true),(17,false),(24,false),(27,false)]
theorem inputList903 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause903 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause903 (by decide) v hb
mask_input "903|151126018|75557863725914323420416"
def inputClause904 : CNF.NClause := [(76,true),(1,true),(8,true),(10,true),(17,false),(24,false),(27,false)]
theorem inputList904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause904 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause904 (by decide) v hb
mask_input "904|151126016|75557863725914323420418"
def inputClause905 : CNF.NClause := [(76,true),(1,false),(8,false),(10,false),(17,true),(24,false),(27,false)]
theorem inputList905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause905 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause905 (by decide) v hb
mask_input "905|150996226|75557863725914323550208"
def inputClause906 : CNF.NClause := [(76,true),(1,true),(8,false),(10,false),(17,true),(24,false),(27,false)]
theorem inputList906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause906 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause906 (by decide) v hb
mask_input "906|150996224|75557863725914323550210"
def inputClause907 : CNF.NClause := [(76,true),(1,false),(8,true),(10,false),(17,true),(24,false),(27,false)]
theorem inputList907 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause907 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause907 (by decide) v hb
mask_input "907|150995970|75557863725914323550464"
def inputClause908 : CNF.NClause := [(76,true),(1,true),(8,true),(10,false),(17,true),(24,false),(27,false)]
theorem inputList908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause908 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause908 (by decide) v hb
mask_input "908|150995968|75557863725914323550466"
def inputClause909 : CNF.NClause := [(76,true),(1,false),(8,false),(10,true),(17,true),(24,false),(27,false)]
theorem inputList909 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause909 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause909 (by decide) v hb
mask_input "909|150995202|75557863725914323551232"
def inputClause910 : CNF.NClause := [(76,true),(1,true),(8,false),(10,true),(17,true),(24,false),(27,false)]
theorem inputList910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause910 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause910 (by decide) v hb
mask_input "910|150995200|75557863725914323551234"
def inputClause911 : CNF.NClause := [(76,true),(1,false),(8,true),(10,true),(17,true),(24,false),(27,false)]
theorem inputList911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause911 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause911 (by decide) v hb
mask_input "911|150994946|75557863725914323551488"
def inputClause912 : CNF.NClause := [(76,true),(1,true),(8,true),(10,true),(17,true),(24,false),(27,false)]
theorem inputList912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause912 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause912 (by decide) v hb
mask_input "912|150994944|75557863725914323551490"
def inputClause913 : CNF.NClause := [(76,true),(1,false),(8,false),(10,false),(17,false),(24,true),(27,false)]
theorem inputList913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause913 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause913 (by decide) v hb
mask_input "913|134350082|75557863725914340196352"
def inputClause914 : CNF.NClause := [(76,true),(1,true),(8,false),(10,false),(17,false),(24,true),(27,false)]
theorem inputList914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause914 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause914 (by decide) v hb
mask_input "914|134350080|75557863725914340196354"
def inputClause915 : CNF.NClause := [(76,true),(1,false),(8,true),(10,false),(17,false),(24,true),(27,false)]
theorem inputList915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause915 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause915 (by decide) v hb
mask_input "915|134349826|75557863725914340196608"
def inputClause916 : CNF.NClause := [(76,true),(1,true),(8,true),(10,false),(17,false),(24,true),(27,false)]
theorem inputList916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause916 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause916 (by decide) v hb
mask_input "916|134349824|75557863725914340196610"
def inputClause917 : CNF.NClause := [(76,true),(1,false),(8,false),(10,true),(17,false),(24,true),(27,false)]
theorem inputList917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause917 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause917 (by decide) v hb
mask_input "917|134349058|75557863725914340197376"
def inputClause918 : CNF.NClause := [(76,true),(1,true),(8,false),(10,true),(17,false),(24,true),(27,false)]
theorem inputList918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause918 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause918 (by decide) v hb
mask_input "918|134349056|75557863725914340197378"
def inputClause919 : CNF.NClause := [(76,true),(1,false),(8,true),(10,true),(17,false),(24,true),(27,false)]
theorem inputList919 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause919 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 14) 14) (activationA_mem 14) inputClause919 (by decide) v hb
mask_input "919|134348802|75557863725914340197632"
end Percolation.MaskChain
