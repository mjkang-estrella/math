import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause6150 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,false),(77,false),(83,false),(88,false)]
theorem inputList6150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6150 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6150 (by decide) v hb
mask_input "6150|319383108416465393778950144|1180591620717411434496"
def inputClause6151 : CNF.NClause := [(48,false),(17,false),(64,true),(70,true),(76,false),(77,false),(83,false),(88,false)]
theorem inputList6151 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6151 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6151 (by decide) v hb
mask_input "6151|319383089969721320069529600|1199038364791120855040"
def inputClause6152 : CNF.NClause := [(48,false),(17,true),(64,true),(70,true),(76,false),(77,false),(83,false),(88,false)]
theorem inputList6152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6152 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6152 (by decide) v hb
mask_input "6152|319383089969721320069398528|1199038364791120986112"
def inputClause6153 : CNF.NClause := [(48,false),(17,false),(64,false),(70,false),(76,true),(77,false),(83,false),(88,false)]
theorem inputList6153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6153 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6153 (by decide) v hb
mask_input "6153|319308731144360196866965504|75557863725914323419136"
def inputClause6155 : CNF.NClause := [(48,false),(17,false),(64,true),(70,false),(76,true),(77,false),(83,false),(88,false)]
theorem inputList6155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6155 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6155 (by decide) v hb
mask_input "6155|319308712697616123157413888|75576310469988032970752"
def inputClause6156 : CNF.NClause := [(48,false),(17,true),(64,true),(70,false),(76,true),(77,false),(83,false),(88,false)]
theorem inputList6156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6156 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6156 (by decide) v hb
mask_input "6156|319308712697616123157282816|75576310469988033101824"
def inputClause6157 : CNF.NClause := [(48,false),(17,false),(64,false),(70,true),(76,true),(77,false),(83,false),(88,false)]
theorem inputList6157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6157 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6157 (by decide) v hb
mask_input "6157|319307550552739479455662080|76738455346631734722560"
def inputClause6158 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,true),(77,false),(83,false),(88,false)]
theorem inputList6158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6158 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6158 (by decide) v hb
mask_input "6158|319307550552739479455531008|76738455346631734853632"
def inputClause6159 : CNF.NClause := [(48,false),(17,false),(64,true),(70,true),(76,true),(77,false),(83,false),(88,false)]
theorem inputList6159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6159 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6159 (by decide) v hb
mask_input "6159|319307532105995405746110464|76756902090705444274176"
def inputClause6160 : CNF.NClause := [(48,false),(17,true),(64,true),(70,true),(76,true),(77,false),(83,false),(88,false)]
theorem inputList6160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6160 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6160 (by decide) v hb
mask_input "6160|319307532105995405745979392|76756902090705444405248"
def inputClause6161 : CNF.NClause := [(48,false),(17,false),(64,false),(70,false),(76,false),(77,true),(83,false),(88,false)]
theorem inputList6161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6161 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6161 (by decide) v hb
mask_input "6161|319233173280634282543546368|151115727451828646838272"
def inputClause6163 : CNF.NClause := [(48,false),(17,false),(64,true),(70,false),(76,false),(77,true),(83,false),(88,false)]
theorem inputList6163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6163 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6163 (by decide) v hb
mask_input "6163|319233154833890208833994752|151134174195902356389888"
def inputClause6164 : CNF.NClause := [(48,false),(17,true),(64,true),(70,false),(76,false),(77,true),(83,false),(88,false)]
theorem inputList6164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6164 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6164 (by decide) v hb
mask_input "6164|319233154833890208833863680|151134174195902356520960"
def inputClause6165 : CNF.NClause := [(48,false),(17,false),(64,false),(70,true),(76,false),(77,true),(83,false),(88,false)]
theorem inputList6165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6165 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6165 (by decide) v hb
mask_input "6165|319231992689013565132242944|152296319072546058141696"
def inputClause6166 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,false),(77,true),(83,false),(88,false)]
theorem inputList6166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6166 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6166 (by decide) v hb
mask_input "6166|319231992689013565132111872|152296319072546058272768"
def inputClause6167 : CNF.NClause := [(48,false),(17,false),(64,true),(70,true),(76,false),(77,true),(83,false),(88,false)]
theorem inputList6167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6167 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6167 (by decide) v hb
mask_input "6167|319231974242269491422691328|152314765816619767693312"
def inputClause6168 : CNF.NClause := [(48,false),(17,true),(64,true),(70,true),(76,false),(77,true),(83,false),(88,false)]
theorem inputList6168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6168 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6168 (by decide) v hb
mask_input "6168|319231974242269491422560256|152314765816619767824384"
def inputClause6169 : CNF.NClause := [(48,false),(17,false),(64,false),(70,false),(76,true),(77,true),(83,false),(88,false)]
theorem inputList6169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6169 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6169 (by decide) v hb
mask_input "6169|319157615416908368220127232|226673591177742970257408"
def inputClause6171 : CNF.NClause := [(48,false),(17,false),(64,true),(70,false),(76,true),(77,true),(83,false),(88,false)]
theorem inputList6171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6171 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6171 (by decide) v hb
mask_input "6171|319157596970164294510575616|226692037921816679809024"
def inputClause6172 : CNF.NClause := [(48,false),(17,true),(64,true),(70,false),(76,true),(77,true),(83,false),(88,false)]
theorem inputList6172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6172 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6172 (by decide) v hb
mask_input "6172|319157596970164294510444544|226692037921816679940096"
def inputClause6173 : CNF.NClause := [(48,false),(17,false),(64,false),(70,true),(76,true),(77,true),(83,false),(88,false)]
theorem inputList6173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6173 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6173 (by decide) v hb
mask_input "6173|319156434825287650808823808|227854182798460381560832"
def inputClause6174 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,true),(77,true),(83,false),(88,false)]
theorem inputList6174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6174 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6174 (by decide) v hb
mask_input "6174|319156434825287650808692736|227854182798460381691904"
def inputClause6175 : CNF.NClause := [(48,false),(17,false),(64,true),(70,true),(76,true),(77,true),(83,false),(88,false)]
theorem inputList6175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6175 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6175 (by decide) v hb
mask_input "6175|319156416378543577099272192|227872629542534091112448"
def inputClause6176 : CNF.NClause := [(48,false),(17,true),(64,true),(70,true),(76,true),(77,true),(83,false),(88,false)]
theorem inputList6176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6176 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6176 (by decide) v hb
mask_input "6176|319156416378543577099141120|227872629542534091243520"
def inputClause6177 : CNF.NClause := [(48,false),(17,false),(64,false),(70,false),(76,false),(77,false),(83,true),(88,false)]
theorem inputList6177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6177 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6177 (by decide) v hb
mask_input "6177|309712882451169077792735232|9671406556917033397649408"
def inputClause6179 : CNF.NClause := [(48,false),(17,false),(64,true),(70,false),(76,false),(77,false),(83,true),(88,false)]
theorem inputList6179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6179 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6179 (by decide) v hb
mask_input "6179|309712864004425004083183616|9671425003661107107201024"
def inputClause6180 : CNF.NClause := [(48,false),(17,true),(64,true),(70,false),(76,false),(77,false),(83,true),(88,false)]
theorem inputList6180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6180 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6180 (by decide) v hb
mask_input "6180|309712864004425004083052544|9671425003661107107332096"
def inputClause6181 : CNF.NClause := [(48,false),(17,false),(64,false),(70,true),(76,false),(77,false),(83,true),(88,false)]
theorem inputList6181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6181 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6181 (by decide) v hb
mask_input "6181|309711701859548360381431808|9672587148537750808952832"
def inputClause6182 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,false),(77,false),(83,true),(88,false)]
theorem inputList6182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6182 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6182 (by decide) v hb
mask_input "6182|309711701859548360381300736|9672587148537750809083904"
def inputClause6183 : CNF.NClause := [(48,false),(17,false),(64,true),(70,true),(76,false),(77,false),(83,true),(88,false)]
theorem inputList6183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6183 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6183 (by decide) v hb
mask_input "6183|309711683412804286671880192|9672605595281824518504448"
def inputClause6184 : CNF.NClause := [(48,false),(17,true),(64,true),(70,true),(76,false),(77,false),(83,true),(88,false)]
theorem inputList6184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6184 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6184 (by decide) v hb
mask_input "6184|309711683412804286671749120|9672605595281824518635520"
def inputClause6185 : CNF.NClause := [(48,false),(17,false),(64,false),(70,false),(76,true),(77,false),(83,true),(88,false)]
theorem inputList6185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6185 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6185 (by decide) v hb
mask_input "6185|309637324587443163469316096|9746964420642947721068544"
def inputClause6187 : CNF.NClause := [(48,false),(17,false),(64,true),(70,false),(76,true),(77,false),(83,true),(88,false)]
theorem inputList6187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6187 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6187 (by decide) v hb
mask_input "6187|309637306140699089759764480|9746982867387021430620160"
def inputClause6188 : CNF.NClause := [(48,false),(17,true),(64,true),(70,false),(76,true),(77,false),(83,true),(88,false)]
theorem inputList6188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6188 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6188 (by decide) v hb
mask_input "6188|309637306140699089759633408|9746982867387021430751232"
def inputClause6189 : CNF.NClause := [(48,false),(17,false),(64,false),(70,true),(76,true),(77,false),(83,true),(88,false)]
theorem inputList6189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6189 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6189 (by decide) v hb
mask_input "6189|309636143995822446058012672|9748145012263665132371968"
def inputClause6190 : CNF.NClause := [(48,false),(17,true),(64,false),(70,true),(76,true),(77,false),(83,true),(88,false)]
theorem inputList6190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6190 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6190 (by decide) v hb
mask_input "6190|309636143995822446057881600|9748145012263665132503040"
def inputClause6191 : CNF.NClause := [(48,false),(17,false),(64,true),(70,true),(76,true),(77,false),(83,true),(88,false)]
theorem inputList6191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6191 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6191 (by decide) v hb
mask_input "6191|309636125549078372348461056|9748163459007738841923584"
def inputClause6192 : CNF.NClause := [(48,false),(17,true),(64,true),(70,true),(76,true),(77,false),(83,true),(88,false)]
theorem inputList6192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6192 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6192 (by decide) v hb
mask_input "6192|309636125549078372348329984|9748163459007738842054656"
def inputClause6193 : CNF.NClause := [(48,false),(17,false),(64,false),(70,false),(76,false),(77,true),(83,true),(88,false)]
theorem inputList6193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6193 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6193 (by decide) v hb
mask_input "6193|309561766723717249145896960|9822522284368862044487680"
def inputClause6195 : CNF.NClause := [(48,false),(17,false),(64,true),(70,false),(76,false),(77,true),(83,true),(88,false)]
theorem inputList6195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6195 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 17) (spread_mem 17) inputClause6195 (by decide) v hb
mask_input "6195|309561748276973175436345344|9822540731112935754039296"
end Percolation.MaskChain
