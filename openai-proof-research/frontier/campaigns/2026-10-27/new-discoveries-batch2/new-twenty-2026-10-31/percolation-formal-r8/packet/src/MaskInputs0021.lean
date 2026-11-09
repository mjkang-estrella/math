import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause1169 : CNF.NClause := [(80,true),(3,false),(7,false),(11,false),(15,false),(24,true),(29,false)]
theorem inputList1169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1169 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1169 (by decide) v hb
mask_input "1169|536905864|1208925819614629191483392"
def inputClause1170 : CNF.NClause := [(80,true),(3,true),(7,false),(11,false),(15,false),(24,true),(29,false)]
theorem inputList1170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1170 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1170 (by decide) v hb
mask_input "1170|536905856|1208925819614629191483400"
def inputClause1171 : CNF.NClause := [(80,true),(3,false),(7,true),(11,false),(15,false),(24,true),(29,false)]
theorem inputList1171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1171 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1171 (by decide) v hb
mask_input "1171|536905736|1208925819614629191483520"
def inputClause1172 : CNF.NClause := [(80,true),(3,true),(7,true),(11,false),(15,false),(24,true),(29,false)]
theorem inputList1172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1172 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1172 (by decide) v hb
mask_input "1172|536905728|1208925819614629191483528"
def inputClause1173 : CNF.NClause := [(80,true),(3,false),(7,false),(11,true),(15,false),(24,true),(29,false)]
theorem inputList1173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1173 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1173 (by decide) v hb
mask_input "1173|536903816|1208925819614629191485440"
def inputClause1174 : CNF.NClause := [(80,true),(3,true),(7,false),(11,true),(15,false),(24,true),(29,false)]
theorem inputList1174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1174 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1174 (by decide) v hb
mask_input "1174|536903808|1208925819614629191485448"
def inputClause1175 : CNF.NClause := [(80,true),(3,false),(7,true),(11,true),(15,false),(24,true),(29,false)]
theorem inputList1175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1175 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1175 (by decide) v hb
mask_input "1175|536903688|1208925819614629191485568"
def inputClause1176 : CNF.NClause := [(80,true),(3,true),(7,true),(11,true),(15,false),(24,true),(29,false)]
theorem inputList1176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1176 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1176 (by decide) v hb
mask_input "1176|536903680|1208925819614629191485576"
def inputClause1177 : CNF.NClause := [(80,true),(3,false),(7,false),(11,false),(15,true),(24,true),(29,false)]
theorem inputList1177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1177 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1177 (by decide) v hb
mask_input "1177|536873096|1208925819614629191516160"
def inputClause1178 : CNF.NClause := [(80,true),(3,true),(7,false),(11,false),(15,true),(24,true),(29,false)]
theorem inputList1178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1178 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1178 (by decide) v hb
mask_input "1178|536873088|1208925819614629191516168"
def inputClause1179 : CNF.NClause := [(80,true),(3,false),(7,true),(11,false),(15,true),(24,true),(29,false)]
theorem inputList1179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1179 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1179 (by decide) v hb
mask_input "1179|536872968|1208925819614629191516288"
def inputClause1180 : CNF.NClause := [(80,true),(3,true),(7,true),(11,false),(15,true),(24,true),(29,false)]
theorem inputList1180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1180 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1180 (by decide) v hb
mask_input "1180|536872960|1208925819614629191516296"
def inputClause1181 : CNF.NClause := [(80,true),(3,false),(7,false),(11,true),(15,true),(24,true),(29,false)]
theorem inputList1181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1181 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1181 (by decide) v hb
mask_input "1181|536871048|1208925819614629191518208"
def inputClause1182 : CNF.NClause := [(80,true),(3,true),(7,false),(11,true),(15,true),(24,true),(29,false)]
theorem inputList1182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1182 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1182 (by decide) v hb
mask_input "1182|536871040|1208925819614629191518216"
def inputClause1183 : CNF.NClause := [(80,true),(3,false),(7,true),(11,true),(15,true),(24,true),(29,false)]
theorem inputList1183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1183 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1183 (by decide) v hb
mask_input "1183|536870920|1208925819614629191518336"
def inputClause1184 : CNF.NClause := [(80,false),(3,true),(7,true),(11,true),(15,true),(24,true),(29,false)]
theorem inputList1184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1184 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1184 (by decide) v hb
mask_input "1184|1208925819614629711577088|16812168"
def inputClause1185 : CNF.NClause := [(80,true),(3,false),(7,false),(11,false),(15,false),(24,false),(29,true)]
theorem inputList1185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1185 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1185 (by decide) v hb
mask_input "1185|16812168|1208925819614629711577088"
def inputClause1186 : CNF.NClause := [(80,true),(3,true),(7,false),(11,false),(15,false),(24,false),(29,true)]
theorem inputList1186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1186 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1186 (by decide) v hb
mask_input "1186|16812160|1208925819614629711577096"
def inputClause1187 : CNF.NClause := [(80,true),(3,false),(7,true),(11,false),(15,false),(24,false),(29,true)]
theorem inputList1187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1187 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1187 (by decide) v hb
mask_input "1187|16812040|1208925819614629711577216"
def inputClause1188 : CNF.NClause := [(80,true),(3,true),(7,true),(11,false),(15,false),(24,false),(29,true)]
theorem inputList1188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1188 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1188 (by decide) v hb
mask_input "1188|16812032|1208925819614629711577224"
def inputClause1189 : CNF.NClause := [(80,true),(3,false),(7,false),(11,true),(15,false),(24,false),(29,true)]
theorem inputList1189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1189 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1189 (by decide) v hb
mask_input "1189|16810120|1208925819614629711579136"
def inputClause1190 : CNF.NClause := [(80,true),(3,true),(7,false),(11,true),(15,false),(24,false),(29,true)]
theorem inputList1190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1190 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1190 (by decide) v hb
mask_input "1190|16810112|1208925819614629711579144"
def inputClause1191 : CNF.NClause := [(80,true),(3,false),(7,true),(11,true),(15,false),(24,false),(29,true)]
theorem inputList1191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1191 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1191 (by decide) v hb
mask_input "1191|16809992|1208925819614629711579264"
def inputClause1192 : CNF.NClause := [(80,true),(3,true),(7,true),(11,true),(15,false),(24,false),(29,true)]
theorem inputList1192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1192 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1192 (by decide) v hb
mask_input "1192|16809984|1208925819614629711579272"
def inputClause1193 : CNF.NClause := [(80,true),(3,false),(7,false),(11,false),(15,true),(24,false),(29,true)]
theorem inputList1193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1193 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1193 (by decide) v hb
mask_input "1193|16779400|1208925819614629711609856"
def inputClause1194 : CNF.NClause := [(80,true),(3,true),(7,false),(11,false),(15,true),(24,false),(29,true)]
theorem inputList1194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1194 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1194 (by decide) v hb
mask_input "1194|16779392|1208925819614629711609864"
def inputClause1195 : CNF.NClause := [(80,true),(3,false),(7,true),(11,false),(15,true),(24,false),(29,true)]
theorem inputList1195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1195 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1195 (by decide) v hb
mask_input "1195|16779272|1208925819614629711609984"
def inputClause1196 : CNF.NClause := [(80,true),(3,true),(7,true),(11,false),(15,true),(24,false),(29,true)]
theorem inputList1196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1196 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1196 (by decide) v hb
mask_input "1196|16779264|1208925819614629711609992"
def inputClause1197 : CNF.NClause := [(80,true),(3,false),(7,false),(11,true),(15,true),(24,false),(29,true)]
theorem inputList1197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1197 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1197 (by decide) v hb
mask_input "1197|16777352|1208925819614629711611904"
def inputClause1198 : CNF.NClause := [(80,true),(3,true),(7,false),(11,true),(15,true),(24,false),(29,true)]
theorem inputList1198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1198 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1198 (by decide) v hb
mask_input "1198|16777344|1208925819614629711611912"
def inputClause1199 : CNF.NClause := [(80,true),(3,false),(7,true),(11,true),(15,true),(24,false),(29,true)]
theorem inputList1199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1199 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1199 (by decide) v hb
mask_input "1199|16777224|1208925819614629711612032"
def inputClause1201 : CNF.NClause := [(80,true),(3,false),(7,false),(11,false),(15,false),(24,true),(29,true)]
theorem inputList1201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1201 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1201 (by decide) v hb
mask_input "1201|34952|1208925819614629728354304"
def inputClause1202 : CNF.NClause := [(80,true),(3,true),(7,false),(11,false),(15,false),(24,true),(29,true)]
theorem inputList1202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1202 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1202 (by decide) v hb
mask_input "1202|34944|1208925819614629728354312"
def inputClause1203 : CNF.NClause := [(80,true),(3,false),(7,true),(11,false),(15,false),(24,true),(29,true)]
theorem inputList1203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1203 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1203 (by decide) v hb
mask_input "1203|34824|1208925819614629728354432"
def inputClause1204 : CNF.NClause := [(80,true),(3,true),(7,true),(11,false),(15,false),(24,true),(29,true)]
theorem inputList1204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1204 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1204 (by decide) v hb
mask_input "1204|34816|1208925819614629728354440"
def inputClause1205 : CNF.NClause := [(80,true),(3,false),(7,false),(11,true),(15,false),(24,true),(29,true)]
theorem inputList1205 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1205 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1205 (by decide) v hb
mask_input "1205|32904|1208925819614629728356352"
def inputClause1206 : CNF.NClause := [(80,true),(3,true),(7,false),(11,true),(15,false),(24,true),(29,true)]
theorem inputList1206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1206 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1206 (by decide) v hb
mask_input "1206|32896|1208925819614629728356360"
def inputClause1207 : CNF.NClause := [(80,true),(3,false),(7,true),(11,true),(15,false),(24,true),(29,true)]
theorem inputList1207 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1207 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1207 (by decide) v hb
mask_input "1207|32776|1208925819614629728356480"
def inputClause1209 : CNF.NClause := [(80,true),(3,false),(7,false),(11,false),(15,true),(24,true),(29,true)]
theorem inputList1209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1209 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1209 (by decide) v hb
mask_input "1209|2184|1208925819614629728387072"
def inputClause1210 : CNF.NClause := [(80,true),(3,true),(7,false),(11,false),(15,true),(24,true),(29,true)]
theorem inputList1210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause1210 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 18) 18) (activationA_mem 18) inputClause1210 (by decide) v hb
mask_input "1210|2176|1208925819614629728387080"
end Percolation.MaskChain
