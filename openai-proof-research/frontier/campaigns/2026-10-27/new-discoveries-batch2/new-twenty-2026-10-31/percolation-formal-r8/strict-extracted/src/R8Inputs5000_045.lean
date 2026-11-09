import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause6334 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,true),(77,true),(86,true),(91,false)]
theorem inputList6334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6334 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6334 (by decide) v hb
mask_input "6334|2475880115464811647170772992|77532403211564193824374784"
def inputClause6335 : CNF.NClause := [(49,false),(18,false),(65,true),(69,true),(73,true),(77,true),(86,true),(91,false)]
theorem inputList6335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6335 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6335 (by decide) v hb
mask_input "6335|2475880078571323499751931904|77532440105052341243215872"
def inputClause6336 : CNF.NClause := [(49,false),(18,true),(65,true),(69,true),(73,true),(77,true),(86,true),(91,false)]
theorem inputList6336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6336 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6336 (by decide) v hb
mask_input "6336|2475880078571323499751669760|77532440105052341243478016"
def inputClause6337 : CNF.NClause := [(49,false),(18,false),(65,false),(69,false),(73,false),(77,false),(86,false),(91,true)]
theorem inputList6337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6337 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6337 (by decide) v hb
mask_input "6337|77532440105615291196899328|2475880078570760549798248448"
def inputClause6339 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(73,false),(77,false),(86,false),(91,true)]
theorem inputList6339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6339 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6339 (by decide) v hb
mask_input "6339|77532403212127143777796096|2475880115464248697217351680"
def inputClause6340 : CNF.NClause := [(49,false),(18,true),(65,true),(69,false),(73,false),(77,false),(86,false),(91,true)]
theorem inputList6340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6340 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6340 (by decide) v hb
mask_input "6340|77532403212127143777533952|2475880115464248697217613824"
def inputClause6341 : CNF.NClause := [(49,false),(18,false),(65,false),(69,true),(73,false),(77,false),(86,false),(91,true)]
theorem inputList6341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6341 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6341 (by decide) v hb
mask_input "6341|77531849809804932491247616|2475880668866570908503900160"
def inputClause6342 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,false),(77,false),(86,false),(91,true)]
theorem inputList6342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6342 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6342 (by decide) v hb
mask_input "6342|77531849809804932490985472|2475880668866570908504162304"
def inputClause6343 : CNF.NClause := [(49,false),(18,false),(65,true),(69,true),(73,false),(77,false),(86,false),(91,true)]
theorem inputList6343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6343 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6343 (by decide) v hb
mask_input "6343|77531812916316785072144384|2475880705760059055923003392"
def inputClause6344 : CNF.NClause := [(49,false),(18,true),(65,true),(69,true),(73,false),(77,false),(86,false),(91,true)]
theorem inputList6344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6344 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6344 (by decide) v hb
mask_input "6344|77531812916316785071882240|2475880705760059055923265536"
def inputClause6345 : CNF.NClause := [(49,false),(18,false),(65,false),(69,false),(73,true),(77,false),(86,false),(91,true)]
theorem inputList6345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6345 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6345 (by decide) v hb
mask_input "6345|77522995372649551906471936|2475889523303726289088675840"
def inputClause6346 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,true),(77,false),(86,false),(91,true)]
theorem inputList6346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6346 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6346 (by decide) v hb
mask_input "6346|77522995372649551906209792|2475889523303726289088937984"
def inputClause6347 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(73,true),(77,false),(86,false),(91,true)]
theorem inputList6347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6347 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6347 (by decide) v hb
mask_input "6347|77522958479161404487368704|2475889560197214436507779072"
def inputClause6348 : CNF.NClause := [(49,false),(18,true),(65,true),(69,false),(73,true),(77,false),(86,false),(91,true)]
theorem inputList6348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6348 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6348 (by decide) v hb
mask_input "6348|77522958479161404487106560|2475889560197214436508041216"
def inputClause6350 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,true),(77,false),(86,false),(91,true)]
theorem inputList6350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6350 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6350 (by decide) v hb
mask_input "6350|77522405076839193200558080|2475890113599536647794589696"
def inputClause6351 : CNF.NClause := [(49,false),(18,false),(65,true),(69,true),(73,true),(77,false),(86,false),(91,true)]
theorem inputList6351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6351 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6351 (by decide) v hb
mask_input "6351|77522368183351045781716992|2475890150493024795213430784"
def inputClause6352 : CNF.NClause := [(49,false),(18,true),(65,true),(69,true),(73,true),(77,false),(86,false),(91,true)]
theorem inputList6352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6352 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6352 (by decide) v hb
mask_input "6352|77522368183351045781454848|2475890150493024795213692928"
def inputClause6355 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(73,false),(77,true),(86,false),(91,true)]
theorem inputList6355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6355 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6355 (by decide) v hb
mask_input "6355|77381287484675315130957824|2476031231191700525864189952"
def inputClause6356 : CNF.NClause := [(49,false),(18,true),(65,true),(69,false),(73,false),(77,true),(86,false),(91,true)]
theorem inputList6356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6356 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6356 (by decide) v hb
mask_input "6356|77381287484675315130695680|2476031231191700525864452096"
def inputClause6357 : CNF.NClause := [(49,false),(18,false),(65,false),(69,true),(73,false),(77,true),(86,false),(91,true)]
theorem inputList6357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6357 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6357 (by decide) v hb
mask_input "6357|77380734082353103844409344|2476031784594022737150738432"
def inputClause6358 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,false),(77,true),(86,false),(91,true)]
theorem inputList6358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6358 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6358 (by decide) v hb
mask_input "6358|77380734082353103844147200|2476031784594022737151000576"
def inputClause6359 : CNF.NClause := [(49,false),(18,false),(65,true),(69,true),(73,false),(77,true),(86,false),(91,true)]
theorem inputList6359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6359 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6359 (by decide) v hb
mask_input "6359|77380697188864956425306112|2476031821487510884569841664"
def inputClause6360 : CNF.NClause := [(49,false),(18,true),(65,true),(69,true),(73,false),(77,true),(86,false),(91,true)]
theorem inputList6360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6360 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6360 (by decide) v hb
mask_input "6360|77380697188864956425043968|2476031821487510884570103808"
def inputClause6361 : CNF.NClause := [(49,false),(18,false),(65,false),(69,false),(73,true),(77,true),(86,false),(91,true)]
theorem inputList6361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6361 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6361 (by decide) v hb
mask_input "6361|77371879645197723259633664|2476040639031178117735514112"
def inputClause6362 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,true),(77,true),(86,false),(91,true)]
theorem inputList6362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6362 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6362 (by decide) v hb
mask_input "6362|77371879645197723259371520|2476040639031178117735776256"
def inputClause6363 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(73,true),(77,true),(86,false),(91,true)]
theorem inputList6363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6363 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6363 (by decide) v hb
mask_input "6363|77371842751709575840530432|2476040675924666265154617344"
def inputClause6364 : CNF.NClause := [(49,false),(18,true),(65,true),(69,false),(73,true),(77,true),(86,false),(91,true)]
theorem inputList6364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6364 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6364 (by decide) v hb
mask_input "6364|77371842751709575840268288|2476040675924666265154879488"
def inputClause6365 : CNF.NClause := [(49,false),(18,false),(65,false),(69,true),(73,true),(77,true),(86,false),(91,true)]
theorem inputList6365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6365 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6365 (by decide) v hb
mask_input "6365|77371289349387364553981952|2476041229326988476441165824"
def inputClause6366 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,true),(77,true),(86,false),(91,true)]
theorem inputList6366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6366 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6366 (by decide) v hb
mask_input "6366|77371289349387364553719808|2476041229326988476441427968"
def inputClause6367 : CNF.NClause := [(49,false),(18,false),(65,true),(69,true),(73,true),(77,true),(86,false),(91,true)]
theorem inputList6367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6367 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6367 (by decide) v hb
mask_input "6367|77371252455899217134878720|2476041266220476623860269056"
def inputClause6368 : CNF.NClause := [(49,false),(18,true),(65,true),(69,true),(73,true),(77,true),(86,false),(91,true)]
theorem inputList6368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6368 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6368 (by decide) v hb
mask_input "6368|77371252455899217134616576|2476041266220476623860531200"
def inputClause6369 : CNF.NClause := [(49,false),(18,false),(65,false),(69,false),(73,false),(77,false),(86,true),(91,true)]
theorem inputList6369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6369 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6369 (by decide) v hb
mask_input "6369|161187650279024015704064|2553251331026096816979443712"
def inputClause6370 : CNF.NClause := [(49,false),(18,true),(65,false),(69,false),(73,false),(77,false),(86,true),(91,true)]
theorem inputList6370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6370 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6370 (by decide) v hb
mask_input "6370|161187650279024015441920|2553251331026096816979705856"
def inputClause6371 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(73,false),(77,false),(86,true),(91,true)]
theorem inputList6371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6371 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6371 (by decide) v hb
mask_input "6371|161150756790876596600832|2553251367919584964398546944"
def inputClause6372 : CNF.NClause := [(49,false),(18,true),(65,true),(69,false),(73,false),(77,false),(86,true),(91,true)]
theorem inputList6372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6372 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6372 (by decide) v hb
mask_input "6372|161150756790876596338688|2553251367919584964398809088"
def inputClause6373 : CNF.NClause := [(49,false),(18,false),(65,false),(69,true),(73,false),(77,false),(86,true),(91,true)]
theorem inputList6373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6373 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6373 (by decide) v hb
mask_input "6373|160597354468665310052352|2553251921321907175685095424"
def inputClause6374 : CNF.NClause := [(49,false),(18,true),(65,false),(69,true),(73,false),(77,false),(86,true),(91,true)]
theorem inputList6374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6374 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6374 (by decide) v hb
mask_input "6374|160597354468665309790208|2553251921321907175685357568"
def inputClause6375 : CNF.NClause := [(49,false),(18,false),(65,true),(69,true),(73,false),(77,false),(86,true),(91,true)]
theorem inputList6375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6375 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6375 (by decide) v hb
mask_input "6375|160560460980517890949120|2553251958215395323104198656"
def inputClause6376 : CNF.NClause := [(49,false),(18,true),(65,true),(69,true),(73,false),(77,false),(86,true),(91,true)]
theorem inputList6376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6376 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6376 (by decide) v hb
mask_input "6376|160560460980517890686976|2553251958215395323104460800"
def inputClause6377 : CNF.NClause := [(49,false),(18,false),(65,false),(69,false),(73,true),(77,false),(86,true),(91,true)]
theorem inputList6377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause6377 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 18) (spread_mem 18) inputClause6377 (by decide) v hb
mask_input "6377|151742917313284725276672|2553260775759062556269871104"
end Percolation.MaskChain
