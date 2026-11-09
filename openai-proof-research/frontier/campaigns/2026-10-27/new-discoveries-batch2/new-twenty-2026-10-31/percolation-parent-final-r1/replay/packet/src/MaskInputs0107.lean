import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause7832 : CNF.NClause := [(61,false),(30,true),(62,true),(67,true),(72,false),(77,true),(82,false),(87,false)]
theorem inputList7832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7832 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7832 (by decide) v hb
mask_input "7832|159582932861456929920122880|151267913090437824380928"
def inputClause7834 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,true),(77,true),(82,false),(87,false)]
theorem inputList7834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7834 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7834 (by decide) v hb
mask_input "7834|159578362680612668378710016|155838093934699365793792"
def inputClause7836 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,true),(77,true),(82,false),(87,false)]
theorem inputList7836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7836 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7836 (by decide) v hb
mask_input "7836|159578358068926649951322112|155842705620717793181696"
def inputClause7838 : CNF.NClause := [(61,false),(30,true),(62,false),(67,true),(72,true),(77,true),(82,false),(87,false)]
theorem inputList7838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7838 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7838 (by decide) v hb
mask_input "7838|159578215106660078702297088|155985667887289042206720"
def inputClause7840 : CNF.NClause := [(61,false),(30,true),(62,true),(67,true),(72,true),(77,true),(82,false),(87,false)]
theorem inputList7840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7840 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7840 (by decide) v hb
mask_input "7840|159578210494974060274909184|155990279573307469594624"
def inputClause7842 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,false),(77,false),(82,true),(87,false)]
theorem inputList7842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7842 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7842 (by decide) v hb
mask_input "7842|154898497496088849971937280|4835703278458517772566528"
def inputClause7844 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,false),(77,false),(82,true),(87,false)]
theorem inputList7844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7844 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7844 (by decide) v hb
mask_input "7844|154898492884402831544549376|4835707890144536199954432"
def inputClause7846 : CNF.NClause := [(61,false),(30,true),(62,false),(67,true),(72,false),(77,false),(82,true),(87,false)]
theorem inputList7846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7846 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7846 (by decide) v hb
mask_input "7846|154898349922136260295524352|4835850852411107448979456"
def inputClause7848 : CNF.NClause := [(61,false),(30,true),(62,true),(67,true),(72,false),(77,false),(82,true),(87,false)]
theorem inputList7848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7848 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7848 (by decide) v hb
mask_input "7848|154898345310450241868136448|4835855464097125876367360"
def inputClause7850 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,true),(77,false),(82,true),(87,false)]
theorem inputList7850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7850 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7850 (by decide) v hb
mask_input "7850|154893775129605980326723584|4840425644941387417780224"
def inputClause7852 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,true),(77,false),(82,true),(87,false)]
theorem inputList7852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7852 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7852 (by decide) v hb
mask_input "7852|154893770517919961899335680|4840430256627405845168128"
def inputClause7854 : CNF.NClause := [(61,false),(30,true),(62,false),(67,true),(72,true),(77,false),(82,true),(87,false)]
theorem inputList7854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7854 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7854 (by decide) v hb
mask_input "7854|154893627555653390650310656|4840573218893977094193152"
def inputClause7856 : CNF.NClause := [(61,false),(30,true),(62,true),(67,true),(72,true),(77,false),(82,true),(87,false)]
theorem inputList7856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7856 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7856 (by decide) v hb
mask_input "7856|154893622943967372222922752|4840577830579995521581056"
def inputClause7858 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,false),(77,true),(82,true),(87,false)]
theorem inputList7858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7858 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7858 (by decide) v hb
mask_input "7858|154747381768637021325099008|4986819005910346419404800"
def inputClause7860 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,false),(77,true),(82,true),(87,false)]
theorem inputList7860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7860 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7860 (by decide) v hb
mask_input "7860|154747377156951002897711104|4986823617596364846792704"
def inputClause7862 : CNF.NClause := [(61,false),(30,true),(62,false),(67,true),(72,false),(77,true),(82,true),(87,false)]
theorem inputList7862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7862 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7862 (by decide) v hb
mask_input "7862|154747234194684431648686080|4986966579862936095817728"
def inputClause7864 : CNF.NClause := [(61,false),(30,true),(62,true),(67,true),(72,false),(77,true),(82,true),(87,false)]
theorem inputList7864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7864 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7864 (by decide) v hb
mask_input "7864|154747229582998413221298176|4986971191548954523205632"
def inputClause7866 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,true),(77,true),(82,true),(87,false)]
theorem inputList7866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7866 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7866 (by decide) v hb
mask_input "7866|154742659402154151679885312|4991541372393216064618496"
def inputClause7868 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,true),(77,true),(82,true),(87,false)]
theorem inputList7868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7868 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7868 (by decide) v hb
mask_input "7868|154742654790468133252497408|4991545984079234492006400"
def inputClause7870 : CNF.NClause := [(61,false),(30,true),(62,false),(67,true),(72,true),(77,true),(82,true),(87,false)]
theorem inputList7870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7870 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7870 (by decide) v hb
mask_input "7870|154742511828201562003472384|4991688946345805741031424"
def inputClause7872 : CNF.NClause := [(61,false),(30,true),(62,true),(67,true),(72,true),(77,true),(82,true),(87,false)]
theorem inputList7872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7872 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7872 (by decide) v hb
mask_input "7872|154742507216515543576084480|4991693558031824168419328"
def inputClause7874 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,false),(77,false),(82,false),(87,true)]
theorem inputList7874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7874 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7874 (by decide) v hb
mask_input "7874|4991695863874832308371456|154742504910672535436132352"
def inputClause7876 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,false),(77,false),(82,false),(87,true)]
theorem inputList7876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7876 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7876 (by decide) v hb
mask_input "7876|4991691252188813880983552|154742509522358553863520256"
def inputClause7878 : CNF.NClause := [(61,false),(30,true),(62,false),(67,true),(72,false),(77,false),(82,false),(87,true)]
theorem inputList7878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7878 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7878 (by decide) v hb
mask_input "7878|4991548289922242631958528|154742652484625125112545280"
def inputClause7880 : CNF.NClause := [(61,false),(30,true),(62,true),(67,true),(72,false),(77,false),(82,false),(87,true)]
theorem inputList7880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7880 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7880 (by decide) v hb
mask_input "7880|4991543678236224204570624|154742657096311143539933184"
def inputClause7882 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,true),(77,false),(82,false),(87,true)]
theorem inputList7882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7882 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7882 (by decide) v hb
mask_input "7882|4986973497391962663157760|154747227277155405081346048"
def inputClause7884 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,true),(77,false),(82,false),(87,true)]
theorem inputList7884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7884 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7884 (by decide) v hb
mask_input "7884|4986968885705944235769856|154747231888841423508733952"
def inputClause7886 : CNF.NClause := [(61,false),(30,true),(62,false),(67,true),(72,true),(77,false),(82,false),(87,true)]
theorem inputList7886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7886 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7886 (by decide) v hb
mask_input "7886|4986825923439372986744832|154747374851107994757758976"
def inputClause7888 : CNF.NClause := [(61,false),(30,true),(62,true),(67,true),(72,true),(77,false),(82,false),(87,true)]
theorem inputList7888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7888 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7888 (by decide) v hb
mask_input "7888|4986821311753354559356928|154747379462794013185146880"
def inputClause7890 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,false),(77,true),(82,false),(87,true)]
theorem inputList7890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7890 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7890 (by decide) v hb
mask_input "7890|4840580136423003661533184|154893620638124364082970624"
def inputClause7892 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,false),(77,true),(82,false),(87,true)]
theorem inputList7892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7892 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7892 (by decide) v hb
mask_input "7892|4840575524736985234145280|154893625249810382510358528"
def inputClause7894 : CNF.NClause := [(61,false),(30,true),(62,false),(67,true),(72,false),(77,true),(82,false),(87,true)]
theorem inputList7894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7894 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7894 (by decide) v hb
mask_input "7894|4840432562470413985120256|154893768212076953759383552"
def inputClause7896 : CNF.NClause := [(61,false),(30,true),(62,true),(67,true),(72,false),(77,true),(82,false),(87,true)]
theorem inputList7896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7896 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7896 (by decide) v hb
mask_input "7896|4840427950784395557732352|154893772823762972186771456"
def inputClause7898 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,true),(77,true),(82,false),(87,true)]
theorem inputList7898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7898 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7898 (by decide) v hb
mask_input "7898|4835857769940134016319488|154898343004607233728184320"
def inputClause7900 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,true),(77,true),(82,false),(87,true)]
theorem inputList7900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7900 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7900 (by decide) v hb
mask_input "7900|4835853158254115588931584|154898347616293252155572224"
def inputClause7902 : CNF.NClause := [(61,false),(30,true),(62,false),(67,true),(72,true),(77,true),(82,false),(87,true)]
theorem inputList7902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7902 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7902 (by decide) v hb
mask_input "7902|4835710195987544339906560|154898490578559823404597248"
def inputClause7904 : CNF.NClause := [(61,false),(30,true),(62,true),(67,true),(72,true),(77,true),(82,false),(87,true)]
theorem inputList7904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7904 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7904 (by decide) v hb
mask_input "7904|4835705584301525912518656|154898495190245841831985152"
def inputClause7906 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,false),(77,false),(82,true),(87,true)]
theorem inputList7906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7906 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7906 (by decide) v hb
mask_input "7906|155992585416315609546752|159578208189131052134957056"
def inputClause7908 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,false),(77,false),(82,true),(87,true)]
theorem inputList7908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7908 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7908 (by decide) v hb
mask_input "7908|155987973730297182158848|159578212800817070562344960"
def inputClause7910 : CNF.NClause := [(61,false),(30,true),(62,false),(67,true),(72,false),(77,false),(82,true),(87,true)]
theorem inputList7910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause7910 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) inputClause7910 (by decide) v hb
mask_input "7910|155845011463725933133824|159578355763083641811369984"
end Percolation.MaskChain
