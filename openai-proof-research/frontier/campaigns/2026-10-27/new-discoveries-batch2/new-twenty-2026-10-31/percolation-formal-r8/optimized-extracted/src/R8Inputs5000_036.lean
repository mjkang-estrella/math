import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause5924 : CNF.NClause := [(46,false),(15,true),(77,true),(78,false),(79,false),(80,false),(81,true),(92,false)]
theorem inputList5924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5924 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5924 (by decide) v hb
mask_input "5924|4953875777325917069396410368|2568967366681086996283392"
def inputClause5925 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(79,false),(80,false),(81,true),(92,false)]
theorem inputList5925 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5925 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5925 (by decide) v hb
mask_input "5925|4953724661598465240749604864|2720083094132915643088896"
def inputClause5926 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(79,false),(80,false),(81,true),(92,false)]
theorem inputList5926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5926 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5926 (by decide) v hb
mask_input "5926|4953724661598465240749572096|2720083094132915643121664"
def inputClause5927 : CNF.NClause := [(46,false),(15,false),(77,true),(78,true),(79,false),(80,false),(81,true),(92,false)]
theorem inputList5927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5927 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5927 (by decide) v hb
mask_input "5927|4953573545871013412102766592|2871198821584744289927168"
def inputClause5928 : CNF.NClause := [(46,false),(15,true),(77,true),(78,true),(79,false),(80,false),(81,true),(92,false)]
theorem inputList5928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5928 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5928 (by decide) v hb
mask_input "5928|4953573545871013412102733824|2871198821584744289959936"
def inputClause5929 : CNF.NClause := [(46,false),(15,false),(77,false),(78,false),(79,true),(80,false),(81,true),(92,false)]
theorem inputList5929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5929 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5929 (by decide) v hb
mask_input "5929|4953422430143561583455928320|3022314549036572936765440"
def inputClause5930 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,true),(80,false),(81,true),(92,false)]
theorem inputList5930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5930 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5930 (by decide) v hb
mask_input "5930|4953422430143561583455895552|3022314549036572936798208"
def inputClause5931 : CNF.NClause := [(46,false),(15,false),(77,true),(78,false),(79,true),(80,false),(81,true),(92,false)]
theorem inputList5931 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5931 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5931 (by decide) v hb
mask_input "5931|4953271314416109754809090048|3173430276488401583603712"
def inputClause5932 : CNF.NClause := [(46,false),(15,true),(77,true),(78,false),(79,true),(80,false),(81,true),(92,false)]
theorem inputList5932 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5932 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5932 (by decide) v hb
mask_input "5932|4953271314416109754809057280|3173430276488401583636480"
def inputClause5933 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(79,true),(80,false),(81,true),(92,false)]
theorem inputList5933 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5933 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5933 (by decide) v hb
mask_input "5933|4953120198688657926162251776|3324546003940230230441984"
def inputClause5934 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(79,true),(80,false),(81,true),(92,false)]
theorem inputList5934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5934 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5934 (by decide) v hb
mask_input "5934|4953120198688657926162219008|3324546003940230230474752"
def inputClause5935 : CNF.NClause := [(46,false),(15,false),(77,true),(78,true),(79,true),(80,false),(81,true),(92,false)]
theorem inputList5935 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5935 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5935 (by decide) v hb
mask_input "5935|4952969082961206097515413504|3475661731392058877280256"
def inputClause5936 : CNF.NClause := [(46,false),(15,true),(77,true),(78,true),(79,true),(80,false),(81,true),(92,false)]
theorem inputList5936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5936 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5936 (by decide) v hb
mask_input "5936|4952969082961206097515380736|3475661731392058877313024"
def inputClause5937 : CNF.NClause := [(46,false),(15,false),(77,false),(78,false),(79,false),(80,true),(81,true),(92,false)]
theorem inputList5937 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5937 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5937 (by decide) v hb
mask_input "5937|4952817967233754268868575232|3626777458843887524118528"
def inputClause5938 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,false),(80,true),(81,true),(92,false)]
theorem inputList5938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5938 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5938 (by decide) v hb
mask_input "5938|4952817967233754268868542464|3626777458843887524151296"
def inputClause5940 : CNF.NClause := [(46,false),(15,true),(77,true),(78,false),(79,false),(80,true),(81,true),(92,false)]
theorem inputList5940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5940 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5940 (by decide) v hb
mask_input "5940|4952666851506302440221704192|3777893186295716170989568"
def inputClause5941 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(79,false),(80,true),(81,true),(92,false)]
theorem inputList5941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5941 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5941 (by decide) v hb
mask_input "5941|4952515735778850611574898688|3929008913747544817795072"
def inputClause5942 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(79,false),(80,true),(81,true),(92,false)]
theorem inputList5942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5942 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5942 (by decide) v hb
mask_input "5942|4952515735778850611574865920|3929008913747544817827840"
def inputClause5943 : CNF.NClause := [(46,false),(15,false),(77,true),(78,true),(79,false),(80,true),(81,true),(92,false)]
theorem inputList5943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5943 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5943 (by decide) v hb
mask_input "5943|4952364620051398782928060416|4080124641199373464633344"
def inputClause5944 : CNF.NClause := [(46,false),(15,true),(77,true),(78,true),(79,false),(80,true),(81,true),(92,false)]
theorem inputList5944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5944 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5944 (by decide) v hb
mask_input "5944|4952364620051398782928027648|4080124641199373464666112"
def inputClause5945 : CNF.NClause := [(46,false),(15,false),(77,false),(78,false),(79,true),(80,true),(81,true),(92,false)]
theorem inputList5945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5945 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5945 (by decide) v hb
mask_input "5945|4952213504323946954281222144|4231240368651202111471616"
def inputClause5946 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,true),(80,true),(81,true),(92,false)]
theorem inputList5946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5946 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5946 (by decide) v hb
mask_input "5946|4952213504323946954281189376|4231240368651202111504384"
def inputClause5947 : CNF.NClause := [(46,false),(15,false),(77,true),(78,false),(79,true),(80,true),(81,true),(92,false)]
theorem inputList5947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5947 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5947 (by decide) v hb
mask_input "5947|4952062388596495125634383872|4382356096103030758309888"
def inputClause5948 : CNF.NClause := [(46,false),(15,true),(77,true),(78,false),(79,true),(80,true),(81,true),(92,false)]
theorem inputList5948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5948 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5948 (by decide) v hb
mask_input "5948|4952062388596495125634351104|4382356096103030758342656"
def inputClause5949 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(79,true),(80,true),(81,true),(92,false)]
theorem inputList5949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5949 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5949 (by decide) v hb
mask_input "5949|4951911272869043296987545600|4533471823554859405148160"
def inputClause5950 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(79,true),(80,true),(81,true),(92,false)]
theorem inputList5950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5950 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5950 (by decide) v hb
mask_input "5950|4951911272869043296987512832|4533471823554859405180928"
def inputClause5951 : CNF.NClause := [(46,false),(15,false),(77,true),(78,true),(79,true),(80,true),(81,true),(92,false)]
theorem inputList5951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5951 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5951 (by decide) v hb
mask_input "5951|4951760157141591468340707328|4684587551006688051986432"
def inputClause5952 : CNF.NClause := [(46,false),(15,true),(77,true),(78,true),(79,true),(80,true),(81,true),(92,false)]
theorem inputList5952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5952 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5952 (by decide) v hb
mask_input "5952|4951760157141591468340674560|4684587551006688052019200"
def inputClause5953 : CNF.NClause := [(46,false),(15,false),(77,false),(78,false),(79,false),(80,false),(81,false),(92,true)]
theorem inputList5953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5953 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5953 (by decide) v hb
mask_input "5953|4684587551077056796196864|4951760157141521099596496896"
def inputClause5954 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,false),(80,false),(81,false),(92,true)]
theorem inputList5954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5954 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5954 (by decide) v hb
mask_input "5954|4684587551077056796164096|4951760157141521099596529664"
def inputClause5956 : CNF.NClause := [(46,false),(15,true),(77,true),(78,false),(79,false),(80,false),(81,false),(92,true)]
theorem inputList5956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5956 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5956 (by decide) v hb
mask_input "5956|4533471823625228149325824|4951911272868972928243367936"
def inputClause5957 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(79,false),(80,false),(81,false),(92,true)]
theorem inputList5957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5957 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5957 (by decide) v hb
mask_input "5957|4382356096173399502520320|4952062388596424756890173440"
def inputClause5958 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(79,false),(80,false),(81,false),(92,true)]
theorem inputList5958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5958 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5958 (by decide) v hb
mask_input "5958|4382356096173399502487552|4952062388596424756890206208"
def inputClause5959 : CNF.NClause := [(46,false),(15,false),(77,true),(78,true),(79,false),(80,false),(81,false),(92,true)]
theorem inputList5959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5959 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5959 (by decide) v hb
mask_input "5959|4231240368721570855682048|4952213504323876585537011712"
def inputClause5960 : CNF.NClause := [(46,false),(15,true),(77,true),(78,true),(79,false),(80,false),(81,false),(92,true)]
theorem inputList5960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5960 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5960 (by decide) v hb
mask_input "5960|4231240368721570855649280|4952213504323876585537044480"
def inputClause5961 : CNF.NClause := [(46,false),(15,false),(77,false),(78,false),(79,true),(80,false),(81,false),(92,true)]
theorem inputList5961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5961 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5961 (by decide) v hb
mask_input "5961|4080124641269742208843776|4952364620051328414183849984"
def inputClause5962 : CNF.NClause := [(46,false),(15,true),(77,false),(78,false),(79,true),(80,false),(81,false),(92,true)]
theorem inputList5962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5962 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5962 (by decide) v hb
mask_input "5962|4080124641269742208811008|4952364620051328414183882752"
def inputClause5963 : CNF.NClause := [(46,false),(15,false),(77,true),(78,false),(79,true),(80,false),(81,false),(92,true)]
theorem inputList5963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5963 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5963 (by decide) v hb
mask_input "5963|3929008913817913562005504|4952515735778780242830688256"
def inputClause5964 : CNF.NClause := [(46,false),(15,true),(77,true),(78,false),(79,true),(80,false),(81,false),(92,true)]
theorem inputList5964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5964 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5964 (by decide) v hb
mask_input "5964|3929008913817913561972736|4952515735778780242830721024"
def inputClause5965 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(79,true),(80,false),(81,false),(92,true)]
theorem inputList5965 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5965 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 15) (spread_mem 15) inputClause5965 (by decide) v hb
mask_input "5965|3777893186366084915167232|4952666851506232071477526528"
end Percolation.MaskChain
