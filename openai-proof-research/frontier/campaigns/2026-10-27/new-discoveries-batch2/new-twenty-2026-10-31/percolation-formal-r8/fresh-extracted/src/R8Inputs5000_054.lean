import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause6737 : CNF.NClause := [(52,false),(21,false),(66,false),(67,false),(73,false),(79,true),(85,false),(88,true)]
theorem inputList6737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6737 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6737 (by decide) v hb
mask_input "6737|38695292326066357025112064|310089472731152383312134144"
def inputClause6738 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,false),(79,true),(85,false),(88,true)]
theorem inputList6738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6738 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6738 (by decide) v hb
mask_input "6738|38695292326066357023014912|310089472731152383314231296"
def inputClause6739 : CNF.NClause := [(52,false),(21,false),(66,true),(67,false),(73,false),(79,true),(85,false),(88,true)]
theorem inputList6739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6739 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6739 (by decide) v hb
mask_input "6739|38695218539090062186905600|310089546518128678150340608"
def inputClause6740 : CNF.NClause := [(52,false),(21,true),(66,true),(67,false),(73,false),(79,true),(85,false),(88,true)]
theorem inputList6740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6740 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6740 (by decide) v hb
mask_input "6740|38695218539090062184808448|310089546518128678152437760"
def inputClause6741 : CNF.NClause := [(52,false),(21,false),(66,false),(67,true),(73,false),(79,true),(85,false),(88,true)]
theorem inputList6741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6741 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6741 (by decide) v hb
mask_input "6741|38695144752113767348699136|310089620305104972988547072"
def inputClause6744 : CNF.NClause := [(52,false),(21,true),(66,true),(67,true),(73,false),(79,true),(85,false),(88,true)]
theorem inputList6744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6744 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6744 (by decide) v hb
mask_input "6744|38695070965137472508395520|310089694092081267828850688"
def inputClause6745 : CNF.NClause := [(52,false),(21,false),(66,false),(67,false),(73,true),(79,true),(85,false),(88,true)]
theorem inputList6745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6745 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6745 (by decide) v hb
mask_input "6745|38685847593100617734684672|310098917464118122602561536"
def inputClause6746 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,true),(79,true),(85,false),(88,true)]
theorem inputList6746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6746 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6746 (by decide) v hb
mask_input "6746|38685847593100617732587520|310098917464118122604658688"
def inputClause6747 : CNF.NClause := [(52,false),(21,false),(66,true),(67,false),(73,true),(79,true),(85,false),(88,true)]
theorem inputList6747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6747 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6747 (by decide) v hb
mask_input "6747|38685773806124322896478208|310098991251094417440768000"
def inputClause6748 : CNF.NClause := [(52,false),(21,true),(66,true),(67,false),(73,true),(79,true),(85,false),(88,true)]
theorem inputList6748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6748 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6748 (by decide) v hb
mask_input "6748|38685773806124322894381056|310098991251094417442865152"
def inputClause6751 : CNF.NClause := [(52,false),(21,false),(66,true),(67,true),(73,true),(79,true),(85,false),(88,true)]
theorem inputList6751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6751 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6751 (by decide) v hb
mask_input "6751|38685626232171733220065280|310099138825047007117180928"
def inputClause6752 : CNF.NClause := [(52,false),(21,true),(66,true),(67,true),(73,true),(79,true),(85,false),(88,true)]
theorem inputList6752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6752 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6752 (by decide) v hb
mask_input "6752|38685626232171733217968128|310099138825047007119278080"
def inputClause6753 : CNF.NClause := [(52,false),(21,false),(66,false),(67,false),(73,false),(79,false),(85,true),(88,true)]
theorem inputList6753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6753 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6753 (by decide) v hb
mask_input "6753|614129008205538021867520|348170636049013202315378688"
def inputClause6754 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,false),(79,false),(85,true),(88,true)]
theorem inputList6754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6754 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6754 (by decide) v hb
mask_input "6754|614129008205538019770368|348170636049013202317475840"
def inputClause6755 : CNF.NClause := [(52,false),(21,false),(66,true),(67,false),(73,false),(79,false),(85,true),(88,true)]
theorem inputList6755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6755 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6755 (by decide) v hb
mask_input "6755|614055221229243183661056|348170709835989497153585152"
def inputClause6756 : CNF.NClause := [(52,false),(21,true),(66,true),(67,false),(73,false),(79,false),(85,true),(88,true)]
theorem inputList6756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6756 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6756 (by decide) v hb
mask_input "6756|614055221229243181563904|348170709835989497155682304"
def inputClause6757 : CNF.NClause := [(52,false),(21,false),(66,false),(67,true),(73,false),(79,false),(85,true),(88,true)]
theorem inputList6757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6757 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6757 (by decide) v hb
mask_input "6757|613981434252948345454592|348170783622965791991791616"
def inputClause6759 : CNF.NClause := [(52,false),(21,false),(66,true),(67,true),(73,false),(79,false),(85,true),(88,true)]
theorem inputList6759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6759 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6759 (by decide) v hb
mask_input "6759|613907647276653507248128|348170857409942086829998080"
def inputClause6760 : CNF.NClause := [(52,false),(21,true),(66,true),(67,true),(73,false),(79,false),(85,true),(88,true)]
theorem inputList6760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6760 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6760 (by decide) v hb
mask_input "6760|613907647276653505150976|348170857409942086832095232"
def inputClause6761 : CNF.NClause := [(52,false),(21,false),(66,false),(67,false),(73,true),(79,false),(85,true),(88,true)]
theorem inputList6761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6761 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6761 (by decide) v hb
mask_input "6761|604684275239798731440128|348180080781978941605806080"
def inputClause6762 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,true),(79,false),(85,true),(88,true)]
theorem inputList6762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6762 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6762 (by decide) v hb
mask_input "6762|604684275239798729342976|348180080781978941607903232"
def inputClause6763 : CNF.NClause := [(52,false),(21,false),(66,true),(67,false),(73,true),(79,false),(85,true),(88,true)]
theorem inputList6763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6763 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6763 (by decide) v hb
mask_input "6763|604610488263503893233664|348180154568955236444012544"
def inputClause6764 : CNF.NClause := [(52,false),(21,true),(66,true),(67,false),(73,true),(79,false),(85,true),(88,true)]
theorem inputList6764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6764 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6764 (by decide) v hb
mask_input "6764|604610488263503891136512|348180154568955236446109696"
def inputClause6765 : CNF.NClause := [(52,false),(21,false),(66,false),(67,true),(73,true),(79,false),(85,true),(88,true)]
theorem inputList6765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6765 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6765 (by decide) v hb
mask_input "6765|604536701287209055027200|348180228355931531282219008"
def inputClause6767 : CNF.NClause := [(52,false),(21,false),(66,true),(67,true),(73,true),(79,false),(85,true),(88,true)]
theorem inputList6767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6767 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6767 (by decide) v hb
mask_input "6767|604462914310914216820736|348180302142907826120425472"
def inputClause6768 : CNF.NClause := [(52,false),(21,true),(66,true),(67,true),(73,true),(79,false),(85,true),(88,true)]
theorem inputList6768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6768 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6768 (by decide) v hb
mask_input "6768|604462914310914214723584|348180302142907826122522624"
def inputClause6769 : CNF.NClause := [(52,false),(21,false),(66,false),(67,false),(73,false),(79,true),(85,true),(88,true)]
theorem inputList6769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6769 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6769 (by decide) v hb
mask_input "6769|9666098398223434514432|348775098958820516902731776"
def inputClause6770 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,false),(79,true),(85,true),(88,true)]
theorem inputList6770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6770 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6770 (by decide) v hb
mask_input "6770|9666098398223432417280|348775098958820516904828928"
def inputClause6771 : CNF.NClause := [(52,false),(21,false),(66,true),(67,false),(73,false),(79,true),(85,true),(88,true)]
theorem inputList6771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6771 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6771 (by decide) v hb
mask_input "6771|9592311421928596307968|348775172745796811740938240"
def inputClause6772 : CNF.NClause := [(52,false),(21,true),(66,true),(67,false),(73,false),(79,true),(85,true),(88,true)]
theorem inputList6772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6772 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6772 (by decide) v hb
mask_input "6772|9592311421928594210816|348775172745796811743035392"
def inputClause6776 : CNF.NClause := [(52,false),(21,true),(66,true),(67,true),(73,false),(79,true),(85,true),(88,true)]
theorem inputList6776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6776 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6776 (by decide) v hb
mask_input "6776|9444737469338917797888|348775320319749401419448320"
def inputClause6777 : CNF.NClause := [(52,false),(21,false),(66,false),(67,false),(73,true),(79,true),(85,true),(88,true)]
theorem inputList6777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6777 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6777 (by decide) v hb
mask_input "6777|221365432484144087040|348784543691786256193159168"
def inputClause6778 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,true),(79,true),(85,true),(88,true)]
theorem inputList6778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6778 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6778 (by decide) v hb
mask_input "6778|221365432484141989888|348784543691786256195256320"
def inputClause6779 : CNF.NClause := [(52,false),(21,false),(66,true),(67,false),(73,true),(79,true),(85,true),(88,true)]
theorem inputList6779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6779 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6779 (by decide) v hb
mask_input "6779|147578456189305880576|348784617478762551031365632"
def inputClause6780 : CNF.NClause := [(52,false),(21,true),(66,true),(67,false),(73,true),(79,true),(85,true),(88,true)]
theorem inputList6780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6780 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6780 (by decide) v hb
mask_input "6780|147578456189303783424|348784617478762551033462784"
def inputClause6784 : CNF.NClause := [(52,false),(21,true),(66,true),(67,true),(73,true),(79,true),(85,true),(88,true)]
theorem inputList6784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6784 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 21) (spread_mem 21) inputClause6784 (by decide) v hb
mask_input "6784|4503599627370496|348784765052715140709875712"
def inputClause6785 : CNF.NClause := [(53,true),(22,false),(64,false),(67,false),(75,false),(78,false),(86,false),(90,false)]
theorem inputList6785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6785 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6785 (by decide) v hb
mask_input "6785|1315651468148179819925864448|9007199254740992"
def inputClause6787 : CNF.NClause := [(53,false),(22,false),(64,true),(67,false),(75,false),(78,false),(86,false),(90,false)]
theorem inputList6787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6787 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6787 (by decide) v hb
mask_input "6787|1315651449710442945471053824|18446744073709551616"
def inputClause6788 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(75,false),(78,false),(86,false),(90,false)]
theorem inputList6788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6788 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6788 (by decide) v hb
mask_input "6788|1315651449710442945466859520|18446744073713745920"
def inputClause6789 : CNF.NClause := [(53,false),(22,false),(64,false),(67,true),(75,false),(78,false),(86,false),(90,false)]
theorem inputList6789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6789 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 22) (spread_mem 22) inputClause6789 (by decide) v hb
mask_input "6789|1315651320583234429504192512|147573952589676412928"
end Percolation.MaskChain
