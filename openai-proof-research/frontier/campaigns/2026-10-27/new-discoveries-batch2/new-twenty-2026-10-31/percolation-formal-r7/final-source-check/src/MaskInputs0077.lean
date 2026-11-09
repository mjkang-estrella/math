import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause3927 : CNF.NClause := [(123,true),(31,false),(36,true),(41,true),(46,false),(51,true),(56,false)]
theorem inputList3927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3927 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3927 (by decide) v hb
mask_input "3927|72127964929589248|10633823966279326983232710549799174144"
def inputClause3928 : CNF.NClause := [(123,true),(31,true),(36,true),(41,true),(46,false),(51,true),(56,false)]
theorem inputList3928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3928 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3928 (by decide) v hb
mask_input "3928|72127962782105600|10633823966279326983232710551946657792"
def inputClause3929 : CNF.NClause := [(123,true),(31,false),(36,false),(41,false),(46,true),(51,true),(56,false)]
theorem inputList3929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3929 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3929 (by decide) v hb
mask_input "3929|72059863928143872|10633823966279326983232778650800619520"
def inputClause3930 : CNF.NClause := [(123,true),(31,true),(36,false),(41,false),(46,true),(51,true),(56,false)]
theorem inputList3930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3930 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3930 (by decide) v hb
mask_input "3930|72059861780660224|10633823966279326983232778652948103168"
def inputClause3934 : CNF.NClause := [(123,true),(31,true),(36,false),(41,true),(46,true),(51,true),(56,false)]
theorem inputList3934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3934 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3934 (by decide) v hb
mask_input "3934|72057662757404672|10633823966279326983232780851971358720"
def inputClause3936 : CNF.NClause := [(123,false),(31,true),(36,true),(41,true),(46,true),(51,true),(56,false)]
theorem inputList3936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3936 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3936 (by decide) v hb
mask_input "3936|10633823966279326983302514076280684544|2324438448078848"
def inputClause3937 : CNF.NClause := [(123,true),(31,false),(36,false),(41,false),(46,false),(51,false),(56,true)]
theorem inputList3937 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3937 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3937 (by decide) v hb
mask_input "3937|2324438448078848|10633823966279326983302514076280684544"
def inputClause3938 : CNF.NClause := [(123,true),(31,true),(36,false),(41,false),(46,false),(51,false),(56,true)]
theorem inputList3938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3938 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3938 (by decide) v hb
mask_input "3938|2324436300595200|10633823966279326983302514078428168192"
def inputClause3939 : CNF.NClause := [(123,true),(31,false),(36,true),(41,false),(46,false),(51,false),(56,true)]
theorem inputList3939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3939 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3939 (by decide) v hb
mask_input "3939|2324369728602112|10633823966279326983302514145000161280"
def inputClause3940 : CNF.NClause := [(123,true),(31,true),(36,true),(41,false),(46,false),(51,false),(56,true)]
theorem inputList3940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3940 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3940 (by decide) v hb
mask_input "3940|2324367581118464|10633823966279326983302514147147644928"
def inputClause3941 : CNF.NClause := [(123,true),(31,false),(36,false),(41,true),(46,false),(51,false),(56,true)]
theorem inputList3941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3941 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3941 (by decide) v hb
mask_input "3941|2322239424823296|10633823966279326983302516275303940096"
def inputClause3942 : CNF.NClause := [(123,true),(31,true),(36,false),(41,true),(46,false),(51,false),(56,true)]
theorem inputList3942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3942 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3942 (by decide) v hb
mask_input "3942|2322237277339648|10633823966279326983302516277451423744"
def inputClause3943 : CNF.NClause := [(123,true),(31,false),(36,true),(41,true),(46,false),(51,false),(56,true)]
theorem inputList3943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3943 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3943 (by decide) v hb
mask_input "3943|2322170705346560|10633823966279326983302516344023416832"
def inputClause3944 : CNF.NClause := [(123,true),(31,true),(36,true),(41,true),(46,false),(51,false),(56,true)]
theorem inputList3944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3944 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3944 (by decide) v hb
mask_input "3944|2322168557862912|10633823966279326983302516346170900480"
def inputClause3945 : CNF.NClause := [(123,true),(31,false),(36,false),(41,false),(46,true),(51,false),(56,true)]
theorem inputList3945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3945 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3945 (by decide) v hb
mask_input "3945|2254069703901184|10633823966279326983302584445024862208"
def inputClause3946 : CNF.NClause := [(123,true),(31,true),(36,false),(41,false),(46,true),(51,false),(56,true)]
theorem inputList3946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3946 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3946 (by decide) v hb
mask_input "3946|2254067556417536|10633823966279326983302584447172345856"
def inputClause3947 : CNF.NClause := [(123,true),(31,false),(36,true),(41,false),(46,true),(51,false),(56,true)]
theorem inputList3947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3947 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3947 (by decide) v hb
mask_input "3947|2254000984424448|10633823966279326983302584513744338944"
def inputClause3948 : CNF.NClause := [(123,true),(31,true),(36,true),(41,false),(46,true),(51,false),(56,true)]
theorem inputList3948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3948 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3948 (by decide) v hb
mask_input "3948|2253998836940800|10633823966279326983302584515891822592"
def inputClause3950 : CNF.NClause := [(123,true),(31,true),(36,false),(41,true),(46,true),(51,false),(56,true)]
theorem inputList3950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3950 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3950 (by decide) v hb
mask_input "3950|2251868533161984|10633823966279326983302586646195601408"
def inputClause3953 : CNF.NClause := [(123,true),(31,false),(36,false),(41,false),(46,false),(51,true),(56,true)]
theorem inputList3953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3953 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3953 (by decide) v hb
mask_input "3953|72638634393600|10633823966279326983304765876094369792"
def inputClause3954 : CNF.NClause := [(123,true),(31,true),(36,false),(41,false),(46,false),(51,true),(56,true)]
theorem inputList3954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3954 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3954 (by decide) v hb
mask_input "3954|72636486909952|10633823966279326983304765878241853440"
def inputClause3955 : CNF.NClause := [(123,true),(31,false),(36,true),(41,false),(46,false),(51,true),(56,true)]
theorem inputList3955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3955 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3955 (by decide) v hb
mask_input "3955|72569914916864|10633823966279326983304765944813846528"
def inputClause3956 : CNF.NClause := [(123,true),(31,true),(36,true),(41,false),(46,false),(51,true),(56,true)]
theorem inputList3956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3956 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3956 (by decide) v hb
mask_input "3956|72567767433216|10633823966279326983304765946961330176"
def inputClause3957 : CNF.NClause := [(123,true),(31,false),(36,false),(41,true),(46,false),(51,true),(56,true)]
theorem inputList3957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3957 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3957 (by decide) v hb
mask_input "3957|70439611138048|10633823966279326983304768075117625344"
def inputClause3958 : CNF.NClause := [(123,true),(31,true),(36,false),(41,true),(46,false),(51,true),(56,true)]
theorem inputList3958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3958 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3958 (by decide) v hb
mask_input "3958|70437463654400|10633823966279326983304768077265108992"
def inputClause3959 : CNF.NClause := [(123,true),(31,false),(36,true),(41,true),(46,false),(51,true),(56,true)]
theorem inputList3959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3959 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3959 (by decide) v hb
mask_input "3959|70370891661312|10633823966279326983304768143837102080"
def inputClause3961 : CNF.NClause := [(123,true),(31,false),(36,false),(41,false),(46,true),(51,true),(56,true)]
theorem inputList3961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3961 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3961 (by decide) v hb
mask_input "3961|2269890215936|10633823966279326983304836244838547456"
def inputClause3962 : CNF.NClause := [(123,true),(31,true),(36,false),(41,false),(46,true),(51,true),(56,true)]
theorem inputList3962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3962 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3962 (by decide) v hb
mask_input "3962|2267742732288|10633823966279326983304836246986031104"
def inputClause3968 : CNF.NClause := [(123,false),(31,true),(36,true),(41,true),(46,true),(51,true),(56,true)]
theorem inputList3968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3968 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) inputClause3968 (by decide) v hb
mask_input "3968|10633823966279326983230456482242756608|74382032486006784"
def inputClause3970 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,false),(90,false),(91,false),(92,false)]
theorem inputList3970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3970 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause3970 (by decide) v hb
mask_input "3970|9748777809372369666978086912|1"
def inputClause3972 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,false),(90,false),(91,false),(92,false)]
theorem inputList3972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3972 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause3972 (by decide) v hb
mask_input "3972|9594035304461697132615696384|154742504910672534362390529"
def inputClause3974 : CNF.NClause := [(31,false),(0,true),(87,false),(88,true),(89,false),(90,false),(91,false),(92,false)]
theorem inputList3974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3974 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause3974 (by decide) v hb
mask_input "3974|9439292799551024598253305856|309485009821345068724781057"
def inputClause3976 : CNF.NClause := [(31,false),(0,true),(87,true),(88,true),(89,false),(90,false),(91,false),(92,false)]
theorem inputList3976 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3976 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause3976 (by decide) v hb
mask_input "3976|9284550294640352063890915328|464227514732017603087171585"
def inputClause3978 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,true),(90,false),(91,false),(92,false)]
theorem inputList3978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3978 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause3978 (by decide) v hb
mask_input "3978|9129807789729679529528524800|618970019642690137449562113"
def inputClause3980 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,true),(90,false),(91,false),(92,false)]
theorem inputList3980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3980 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause3980 (by decide) v hb
mask_input "3980|8975065284819006995166134272|773712524553362671811952641"
def inputClause3982 : CNF.NClause := [(31,false),(0,true),(87,false),(88,true),(89,true),(90,false),(91,false),(92,false)]
theorem inputList3982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3982 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause3982 (by decide) v hb
mask_input "3982|8820322779908334460803743744|928455029464035206174343169"
def inputClause3984 : CNF.NClause := [(31,false),(0,true),(87,true),(88,true),(89,true),(90,false),(91,false),(92,false)]
theorem inputList3984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3984 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause3984 (by decide) v hb
mask_input "3984|8665580274997661926441353216|1083197534374707740536733697"
def inputClause3986 : CNF.NClause := [(31,false),(0,true),(87,false),(88,false),(89,false),(90,true),(91,false),(92,false)]
theorem inputList3986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3986 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause3986 (by decide) v hb
mask_input "3986|8510837770086989392078962688|1237940039285380274899124225"
def inputClause3988 : CNF.NClause := [(31,false),(0,true),(87,true),(88,false),(89,false),(90,true),(91,false),(92,false)]
theorem inputList3988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3988 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause3988 (by decide) v hb
mask_input "3988|8356095265176316857716572160|1392682544196052809261514753"
def inputClause3990 : CNF.NClause := [(31,false),(0,true),(87,false),(88,true),(89,false),(90,true),(91,false),(92,false)]
theorem inputList3990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause3990 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 0) (spread_mem 0) inputClause3990 (by decide) v hb
mask_input "3990|8201352760265644323354181632|1547425049106725343623905281"
end Percolation.MaskChain
