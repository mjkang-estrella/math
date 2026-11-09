import NReplay011
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_28337 : CNF.NClause := [(59,false),(81,true),(28,true),(62,false),(73,true),(84,true),(90,true)]
theorem der_28337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28337 :=
  CNF.rup_sound cl_28337 [cl_7678,cl_28334] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7678 v h) (hints_cons _ _ _ (der_28334 v h) (by intro d hd; cases hd)))
def cl_28339 : CNF.NClause := [(59,false),(28,true),(70,true),(73,true),(62,true),(84,true),(90,true)]
theorem der_28339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28339 :=
  CNF.rup_sound cl_28339 [cl_7680,cl_28325] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7680 v h) (hints_cons _ _ _ (der_28325 v h) (by intro d hd; cases hd)))
def cl_28340 : CNF.NClause := [(41,false),(92,false),(10,true),(75,false),(76,false),(74,false),(73,false)]
theorem der_28340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28340 :=
  CNF.rup_sound cl_28340 [cl_5250,cl_5252] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5250 v h) (hints_cons _ _ _ (inp_5252 v h) (by intro d hd; cases hd)))
def cl_28341 : CNF.NClause := [(41,false),(72,true),(73,false),(74,false),(75,false),(76,false),(92,false)]
theorem der_28341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28341 :=
  CNF.rup_sound cl_28341 [cl_5251,cl_5252] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5251 v h) (hints_cons _ _ _ (inp_5252 v h) (by intro d hd; cases hd)))
def cl_28342 : CNF.NClause := [(41,false),(92,false),(72,false),(75,false),(76,false),(73,true),(74,false)]
theorem der_28342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28342 :=
  CNF.rup_sound cl_28342 [cl_5254,cl_5253] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5254 v h) (hints_cons _ _ _ (inp_5253 v h) (by intro d hd; cases hd)))
def cl_28343 : CNF.NClause := [(41,false),(72,true),(10,false),(74,false),(75,false),(76,false),(92,false)]
theorem der_28343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28343 :=
  CNF.rup_sound cl_28343 [cl_5255,cl_28341] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5255 v h) (hints_cons _ _ _ (der_28341 v h) (by intro d hd; cases hd)))
def cl_28344 : CNF.NClause := [(41,false),(72,true),(10,true),(74,false),(75,false),(76,false),(92,false)]
theorem der_28344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28344 :=
  CNF.rup_sound cl_28344 [cl_5256,cl_28341] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5256 v h) (hints_cons _ _ _ (der_28341 v h) (by intro d hd; cases hd)))
def cl_28345 : CNF.NClause := [(41,false),(74,true),(76,false),(73,false),(72,false),(92,false),(75,false)]
theorem der_28345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28345 :=
  CNF.rup_sound cl_28345 [cl_5258,cl_5257] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5258 v h) (hints_cons _ _ _ (inp_5257 v h) (by intro d hd; cases hd)))
def cl_28346 : CNF.NClause := [(41,false),(72,true),(10,false),(73,false),(75,false),(76,false),(92,false)]
theorem der_28346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28346 :=
  CNF.rup_sound cl_28346 [cl_5259,cl_28341] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5259 v h) (hints_cons _ _ _ (der_28341 v h) (by intro d hd; cases hd)))
def cl_28347 : CNF.NClause := [(41,false),(10,true),(75,false),(73,false),(92,false),(76,false),(72,true)]
theorem der_28347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28347 :=
  CNF.rup_sound cl_28347 [cl_5260,cl_28341] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5260 v h) (hints_cons _ _ _ (der_28341 v h) (by intro d hd; cases hd)))
def cl_28348 : CNF.NClause := [(41,false),(10,false),(72,false),(73,true),(75,false),(76,false),(92,false)]
theorem der_28348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28348 :=
  CNF.rup_sound cl_28348 [cl_5261,cl_28342] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5261 v h) (hints_cons _ _ _ (der_28342 v h) (by intro d hd; cases hd)))
def cl_28349 : CNF.NClause := [(41,false),(10,true),(72,false),(73,true),(75,false),(76,false),(92,false)]
theorem der_28349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28349 :=
  CNF.rup_sound cl_28349 [cl_5262,cl_28342] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5262 v h) (hints_cons _ _ _ (der_28342 v h) (by intro d hd; cases hd)))
def cl_28350 : CNF.NClause := [(41,false),(72,true),(10,false),(73,true),(75,false),(76,false),(92,false)]
theorem der_28350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28350 :=
  CNF.rup_sound cl_28350 [cl_5263,cl_28343] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5263 v h) (hints_cons _ _ _ (der_28343 v h) (by intro d hd; cases hd)))
def cl_28351 : CNF.NClause := [(41,false),(74,true),(73,true),(72,true),(75,false),(76,false),(92,false)]
theorem der_28351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28351 :=
  CNF.rup_sound cl_28351 [cl_5264,cl_28350] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5264 v h) (hints_cons _ _ _ (der_28350 v h) (by intro d hd; cases hd)))
def cl_28352 : CNF.NClause := [(41,false),(75,true),(72,false),(76,false),(74,false),(92,false),(73,false)]
theorem der_28352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28352 :=
  CNF.rup_sound cl_28352 [cl_5266,cl_5265] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5266 v h) (hints_cons _ _ _ (inp_5265 v h) (by intro d hd; cases hd)))
def cl_28353 : CNF.NClause := [(41,false),(72,true),(10,false),(73,false),(74,false),(76,false),(92,false)]
theorem der_28353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28353 :=
  CNF.rup_sound cl_28353 [cl_5267,cl_28341] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5267 v h) (hints_cons _ _ _ (der_28341 v h) (by intro d hd; cases hd)))
def cl_28354 : CNF.NClause := [(41,false),(10,true),(73,false),(74,false),(72,true),(76,false),(92,false)]
theorem der_28354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28354 :=
  CNF.rup_sound cl_28354 [cl_5268,cl_28341] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5268 v h) (hints_cons _ _ _ (der_28341 v h) (by intro d hd; cases hd)))
def cl_28355 : CNF.NClause := [(41,false),(10,false),(72,false),(74,false),(73,true),(76,false),(92,false)]
theorem der_28355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28355 :=
  CNF.rup_sound cl_28355 [cl_5269,cl_28342] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5269 v h) (hints_cons _ _ _ (der_28342 v h) (by intro d hd; cases hd)))
def cl_28356 : CNF.NClause := [(41,false),(10,true),(72,false),(74,false),(73,true),(76,false),(92,false)]
theorem der_28356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28356 :=
  CNF.rup_sound cl_28356 [cl_5270,cl_28342] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5270 v h) (hints_cons _ _ _ (der_28342 v h) (by intro d hd; cases hd)))
def cl_28357 : CNF.NClause := [(41,false),(72,true),(10,false),(73,true),(74,false),(76,false),(92,false)]
theorem der_28357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28357 :=
  CNF.rup_sound cl_28357 [cl_5271,cl_28343] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5271 v h) (hints_cons _ _ _ (der_28343 v h) (by intro d hd; cases hd)))
def cl_28358 : CNF.NClause := [(41,false),(10,true),(73,true),(74,false),(72,true),(76,false),(92,false)]
theorem der_28358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28358 :=
  CNF.rup_sound cl_28358 [cl_5272,cl_28344] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5272 v h) (hints_cons _ _ _ (der_28344 v h) (by intro d hd; cases hd)))
def cl_28359 : CNF.NClause := [(41,false),(10,false),(92,false),(72,false),(73,false),(76,false),(74,true)]
theorem der_28359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28359 :=
  CNF.rup_sound cl_28359 [cl_5273,cl_28345] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5273 v h) (hints_cons _ _ _ (der_28345 v h) (by intro d hd; cases hd)))
def cl_28360 : CNF.NClause := [(41,false),(10,true),(73,false),(72,false),(74,true),(76,false),(92,false)]
theorem der_28360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28360 :=
  CNF.rup_sound cl_28360 [cl_5274,cl_28345] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5274 v h) (hints_cons _ _ _ (der_28345 v h) (by intro d hd; cases hd)))
def cl_28361 : CNF.NClause := [(41,false),(10,false),(73,false),(74,true),(75,true),(76,false),(92,false)]
theorem der_28361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28361 :=
  CNF.rup_sound cl_28361 [cl_5275,cl_28359] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5275 v h) (hints_cons _ _ _ (der_28359 v h) (by intro d hd; cases hd)))
def cl_28362 : CNF.NClause := [(41,false),(74,true),(92,false),(73,false),(72,true),(76,false),(75,true)]
theorem der_28362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28362 :=
  CNF.rup_sound cl_28362 [cl_5276,cl_28361] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5276 v h) (hints_cons _ _ _ (der_28361 v h) (by intro d hd; cases hd)))
def cl_28363 : CNF.NClause := [(41,false),(74,true),(10,false),(72,false),(75,true),(76,false),(92,false)]
theorem der_28363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28363 :=
  CNF.rup_sound cl_28363 [cl_5277,cl_28359] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5277 v h) (hints_cons _ _ _ (der_28359 v h) (by intro d hd; cases hd)))
def cl_28364 : CNF.NClause := [(41,false),(74,true),(72,false),(73,true),(75,true),(76,false),(92,false)]
theorem der_28364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28364 :=
  CNF.rup_sound cl_28364 [cl_5278,cl_28363] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5278 v h) (hints_cons _ _ _ (der_28363 v h) (by intro d hd; cases hd)))
def cl_28365 : CNF.NClause := [(41,false),(72,true),(10,false),(73,true),(74,true),(76,false),(92,false)]
theorem der_28365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28365 :=
  CNF.rup_sound cl_28365 [cl_5279,cl_28351] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5279 v h) (hints_cons _ _ _ (der_28351 v h) (by intro d hd; cases hd)))
def cl_28366 : CNF.NClause := [(41,false),(74,true),(10,true),(73,true),(72,true),(76,false),(92,false)]
theorem der_28366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28366 :=
  CNF.rup_sound cl_28366 [cl_5280,cl_28351] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5280 v h) (hints_cons _ _ _ (der_28351 v h) (by intro d hd; cases hd)))
def cl_28367 : CNF.NClause := [(41,false),(92,false),(76,true),(73,false),(72,false),(74,false),(75,false)]
theorem der_28367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28367 :=
  CNF.rup_sound cl_28367 [cl_5282,cl_5281] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5282 v h) (hints_cons _ _ _ (inp_5281 v h) (by intro d hd; cases hd)))
def cl_28368 : CNF.NClause := [(41,false),(72,true),(10,false),(73,false),(74,false),(75,false),(92,false)]
theorem der_28368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28368 :=
  CNF.rup_sound cl_28368 [cl_5283,cl_28341] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5283 v h) (hints_cons _ _ _ (der_28341 v h) (by intro d hd; cases hd)))
def cl_28369 : CNF.NClause := [(41,false),(72,true),(10,true),(75,false),(73,false),(74,false),(92,false)]
theorem der_28369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28369 :=
  CNF.rup_sound cl_28369 [cl_5284,cl_28341] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5284 v h) (hints_cons _ _ _ (der_28341 v h) (by intro d hd; cases hd)))
def cl_28370 : CNF.NClause := [(41,false),(92,false),(10,false),(72,false),(74,false),(75,false),(73,true)]
theorem der_28370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28370 :=
  CNF.rup_sound cl_28370 [cl_5285,cl_28342] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5285 v h) (hints_cons _ _ _ (der_28342 v h) (by intro d hd; cases hd)))
def cl_28371 : CNF.NClause := [(41,false),(92,false),(10,true),(74,false),(75,false),(72,false),(73,true)]
theorem der_28371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28371 :=
  CNF.rup_sound cl_28371 [cl_5286,cl_28342] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5286 v h) (hints_cons _ _ _ (der_28342 v h) (by intro d hd; cases hd)))
def cl_28372 : CNF.NClause := [(41,false),(10,false),(73,true),(74,false),(75,false),(76,true),(92,false)]
theorem der_28372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28372 :=
  CNF.rup_sound cl_28372 [cl_5287,cl_28370] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5287 v h) (hints_cons _ _ _ (der_28370 v h) (by intro d hd; cases hd)))
def cl_28373 : CNF.NClause := [(41,false),(72,true),(73,true),(74,false),(75,false),(76,true),(92,false)]
theorem der_28373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28373 :=
  CNF.rup_sound cl_28373 [cl_5288,cl_28372] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5288 v h) (hints_cons _ _ _ (der_28372 v h) (by intro d hd; cases hd)))
def cl_28374 : CNF.NClause := [(41,false),(74,true),(10,false),(92,false),(72,false),(75,false),(73,false)]
theorem der_28374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28374 :=
  CNF.rup_sound cl_28374 [cl_5289,cl_28345] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5289 v h) (hints_cons _ _ _ (der_28345 v h) (by intro d hd; cases hd)))
def cl_28375 : CNF.NClause := [(41,false),(74,true),(10,true),(72,false),(73,false),(75,false),(92,false)]
theorem der_28375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28375 :=
  CNF.rup_sound cl_28375 [cl_5290,cl_28345] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5290 v h) (hints_cons _ _ _ (der_28345 v h) (by intro d hd; cases hd)))
def cl_28376 : CNF.NClause := [(41,false),(10,false),(73,false),(74,true),(75,false),(76,true),(92,false)]
theorem der_28376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28376 :=
  CNF.rup_sound cl_28376 [cl_5291,cl_28374] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5291 v h) (hints_cons _ _ _ (der_28374 v h) (by intro d hd; cases hd)))
def cl_28377 : CNF.NClause := [(41,false),(74,true),(92,false),(73,false),(72,true),(76,true),(75,false)]
theorem der_28377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28377 :=
  CNF.rup_sound cl_28377 [cl_5292,cl_28376] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5292 v h) (hints_cons _ _ _ (der_28376 v h) (by intro d hd; cases hd)))
def cl_28378 : CNF.NClause := [(41,false),(10,false),(72,false),(73,true),(75,false),(76,true),(92,false)]
theorem der_28378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28378 :=
  CNF.rup_sound cl_28378 [cl_5293,cl_28370] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5293 v h) (hints_cons _ _ _ (der_28370 v h) (by intro d hd; cases hd)))
def cl_28379 : CNF.NClause := [(41,false),(74,true),(72,false),(73,true),(75,false),(76,true),(92,false)]
theorem der_28379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28379 :=
  CNF.rup_sound cl_28379 [cl_5294,cl_28378] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5294 v h) (hints_cons _ _ _ (der_28378 v h) (by intro d hd; cases hd)))
def cl_28380 : CNF.NClause := [(41,false),(72,true),(10,false),(73,true),(74,true),(75,false),(92,false)]
theorem der_28380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28380 :=
  CNF.rup_sound cl_28380 [cl_5295,cl_28351] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5295 v h) (hints_cons _ _ _ (der_28351 v h) (by intro d hd; cases hd)))
def cl_28381 : CNF.NClause := [(41,false),(74,true),(10,true),(73,true),(72,true),(75,false),(92,false)]
theorem der_28381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28381 :=
  CNF.rup_sound cl_28381 [cl_5296,cl_28351] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5296 v h) (hints_cons _ _ _ (der_28351 v h) (by intro d hd; cases hd)))
def cl_28382 : CNF.NClause := [(41,false),(75,true),(10,false),(72,false),(73,false),(74,false),(92,false)]
theorem der_28382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28382 :=
  CNF.rup_sound cl_28382 [cl_5297,cl_28352] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5297 v h) (hints_cons _ _ _ (der_28352 v h) (by intro d hd; cases hd)))
def cl_28383 : CNF.NClause := [(41,false),(75,true),(10,true),(72,false),(73,false),(74,false),(92,false)]
theorem der_28383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28383 :=
  CNF.rup_sound cl_28383 [cl_5298,cl_28352] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5298 v h) (hints_cons _ _ _ (der_28352 v h) (by intro d hd; cases hd)))
def cl_28384 : CNF.NClause := [(41,false),(72,true),(10,false),(73,false),(74,false),(75,true),(92,false)]
theorem der_28384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28384 :=
  CNF.rup_sound cl_28384 [cl_5299,cl_28353] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5299 v h) (hints_cons _ _ _ (der_28353 v h) (by intro d hd; cases hd)))
def cl_28385 : CNF.NClause := [(41,false),(75,true),(92,false),(74,false),(72,true),(76,true),(73,false)]
theorem der_28385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28385 :=
  CNF.rup_sound cl_28385 [cl_5300,cl_28384] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5300 v h) (hints_cons _ _ _ (der_28384 v h) (by intro d hd; cases hd)))
def cl_28386 : CNF.NClause := [(41,false),(10,false),(72,false),(74,false),(73,true),(76,true),(92,false)]
theorem der_28386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28386 :=
  CNF.rup_sound cl_28386 [cl_5301,cl_28370] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5301 v h) (hints_cons _ _ _ (der_28370 v h) (by intro d hd; cases hd)))
def cl_28387 : CNF.NClause := [(41,false),(75,true),(72,false),(74,false),(73,true),(76,true),(92,false)]
theorem der_28387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28387 :=
  CNF.rup_sound cl_28387 [cl_5302,cl_28386] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5302 v h) (hints_cons _ _ _ (der_28386 v h) (by intro d hd; cases hd)))
def cl_28388 : CNF.NClause := [(41,false),(72,true),(10,false),(74,false),(75,true),(76,true),(92,false)]
theorem der_28388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28388 :=
  CNF.rup_sound cl_28388 [cl_5303,cl_28384] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5303 v h) (hints_cons _ _ _ (der_28384 v h) (by intro d hd; cases hd)))
def cl_28389 : CNF.NClause := [(41,false),(75,true),(73,true),(74,false),(72,true),(76,true),(92,false)]
theorem der_28389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28389 :=
  CNF.rup_sound cl_28389 [cl_5304,cl_28388] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5304 v h) (hints_cons _ _ _ (der_28388 v h) (by intro d hd; cases hd)))
def cl_28390 : CNF.NClause := [(41,false),(75,true),(10,false),(72,false),(73,false),(74,true),(92,false)]
theorem der_28390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28390 :=
  CNF.rup_sound cl_28390 [cl_5305,cl_28359] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5305 v h) (hints_cons _ _ _ (der_28359 v h) (by intro d hd; cases hd)))
def cl_28391 : CNF.NClause := [(41,false),(75,true),(72,false),(73,false),(74,true),(76,true),(92,false)]
theorem der_28391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28391 :=
  CNF.rup_sound cl_28391 [cl_5306,cl_28390] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5306 v h) (hints_cons _ _ _ (der_28390 v h) (by intro d hd; cases hd)))
def cl_28392 : CNF.NClause := [(41,false),(72,true),(10,false),(73,false),(75,true),(76,true),(92,false)]
theorem der_28392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28392 :=
  CNF.rup_sound cl_28392 [cl_5307,cl_28384] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5307 v h) (hints_cons _ _ _ (der_28384 v h) (by intro d hd; cases hd)))
def cl_28393 : CNF.NClause := [(41,false),(75,true),(72,true),(73,false),(74,true),(76,true),(92,false)]
theorem der_28393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28393 :=
  CNF.rup_sound cl_28393 [cl_5308,cl_28392] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5308 v h) (hints_cons _ _ _ (der_28392 v h) (by intro d hd; cases hd)))
def cl_28394 : CNF.NClause := [(41,false),(74,true),(10,false),(72,false),(73,true),(75,true),(92,false)]
theorem der_28394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28394 :=
  CNF.rup_sound cl_28394 [cl_5309,cl_28363] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5309 v h) (hints_cons _ _ _ (der_28363 v h) (by intro d hd; cases hd)))
def cl_28395 : CNF.NClause := [(41,false),(74,true),(72,false),(73,true),(75,true),(76,true),(92,false)]
theorem der_28395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28395 :=
  CNF.rup_sound cl_28395 [cl_5310,cl_28394] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5310 v h) (hints_cons _ _ _ (der_28394 v h) (by intro d hd; cases hd)))
def cl_28397 : CNF.NClause := [(41,false),(74,true),(10,true),(73,true),(72,true),(75,true),(92,false)]
theorem der_28397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28397 :=
  CNF.rup_sound cl_28397 [cl_5312,cl_28366] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5312 v h) (hints_cons _ _ _ (der_28366 v h) (by intro d hd; cases hd)))
def cl_28398 : CNF.NClause := [(41,false),(92,true),(76,false),(74,false),(72,false),(73,false),(75,false)]
theorem der_28398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28398 :=
  CNF.rup_sound cl_28398 [cl_5314,cl_5313] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5314 v h) (hints_cons _ _ _ (inp_5313 v h) (by intro d hd; cases hd)))
def cl_28399 : CNF.NClause := [(41,false),(72,true),(10,false),(73,false),(74,false),(75,false),(76,false)]
theorem der_28399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28399 :=
  CNF.rup_sound cl_28399 [cl_5315,cl_28341] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5315 v h) (hints_cons _ _ _ (der_28341 v h) (by intro d hd; cases hd)))
def cl_28400 : CNF.NClause := [(41,false),(72,true),(10,true),(74,false),(73,false),(76,false),(75,false)]
theorem der_28400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28400 :=
  CNF.rup_sound cl_28400 [cl_5316,cl_28341] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5316 v h) (hints_cons _ _ _ (der_28341 v h) (by intro d hd; cases hd)))
def cl_28401 : CNF.NClause := [(41,false),(73,true),(10,false),(72,false),(74,false),(75,false),(76,false)]
theorem der_28401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28401 :=
  CNF.rup_sound cl_28401 [cl_5317,cl_28342] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5317 v h) (hints_cons _ _ _ (der_28342 v h) (by intro d hd; cases hd)))
def cl_28402 : CNF.NClause := [(41,false),(10,true),(75,false),(76,false),(73,true),(74,false),(72,false)]
theorem der_28402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28402 :=
  CNF.rup_sound cl_28402 [cl_5318,cl_28342] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5318 v h) (hints_cons _ _ _ (der_28342 v h) (by intro d hd; cases hd)))
def cl_28403 : CNF.NClause := [(41,false),(72,true),(10,false),(73,true),(74,false),(75,false),(76,false)]
theorem der_28403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28403 :=
  CNF.rup_sound cl_28403 [cl_5319,cl_28343] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5319 v h) (hints_cons _ _ _ (der_28343 v h) (by intro d hd; cases hd)))
def cl_28404 : CNF.NClause := [(41,false),(72,true),(10,true),(73,true),(74,false),(75,false),(76,false)]
theorem der_28404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28404 :=
  CNF.rup_sound cl_28404 [cl_5320,cl_28344] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5320 v h) (hints_cons _ _ _ (der_28344 v h) (by intro d hd; cases hd)))
def cl_28405 : CNF.NClause := [(41,false),(75,false),(10,false),(74,true),(73,false),(72,false),(76,false)]
theorem der_28405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28405 :=
  CNF.rup_sound cl_28405 [cl_5321,cl_28345] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5321 v h) (hints_cons _ _ _ (der_28345 v h) (by intro d hd; cases hd)))
def cl_28406 : CNF.NClause := [(41,false),(74,true),(10,true),(73,false),(75,false),(72,false),(76,false)]
theorem der_28406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28406 :=
  CNF.rup_sound cl_28406 [cl_5322,cl_28345] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5322 v h) (hints_cons _ _ _ (der_28345 v h) (by intro d hd; cases hd)))
def cl_28407 : CNF.NClause := [(41,false),(72,true),(10,false),(73,false),(74,true),(75,false),(76,false)]
theorem der_28407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28407 :=
  CNF.rup_sound cl_28407 [cl_5323,cl_28346] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5323 v h) (hints_cons _ _ _ (der_28346 v h) (by intro d hd; cases hd)))
def cl_28408 : CNF.NClause := [(41,false),(72,true),(10,true),(73,false),(74,true),(75,false),(76,false)]
theorem der_28408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28408 :=
  CNF.rup_sound cl_28408 [cl_5324,cl_28347] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5324 v h) (hints_cons _ _ _ (der_28347 v h) (by intro d hd; cases hd)))
def cl_28409 : CNF.NClause := [(41,false),(74,true),(10,false),(72,false),(73,true),(75,false),(76,false)]
theorem der_28409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28409 :=
  CNF.rup_sound cl_28409 [cl_5325,cl_28348] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5325 v h) (hints_cons _ _ _ (der_28348 v h) (by intro d hd; cases hd)))
def cl_28410 : CNF.NClause := [(41,false),(74,true),(72,false),(73,true),(75,false),(76,false),(92,true)]
theorem der_28410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28410 :=
  CNF.rup_sound cl_28410 [cl_5326,cl_28409] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5326 v h) (hints_cons _ _ _ (der_28409 v h) (by intro d hd; cases hd)))
def cl_28411 : CNF.NClause := [(41,false),(72,true),(10,false),(73,true),(74,true),(75,false),(76,false)]
theorem der_28411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28411 :=
  CNF.rup_sound cl_28411 [cl_5327,cl_28351] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5327 v h) (hints_cons _ _ _ (der_28351 v h) (by intro d hd; cases hd)))
def cl_28412 : CNF.NClause := [(41,false),(74,true),(10,true),(73,true),(72,true),(75,false),(76,false)]
theorem der_28412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28412 :=
  CNF.rup_sound cl_28412 [cl_5328,cl_28351] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5328 v h) (hints_cons _ _ _ (der_28351 v h) (by intro d hd; cases hd)))
def cl_28413 : CNF.NClause := [(41,false),(75,true),(10,false),(72,false),(73,false),(74,false),(76,false)]
theorem der_28413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28413 :=
  CNF.rup_sound cl_28413 [cl_5329,cl_28352] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5329 v h) (hints_cons _ _ _ (der_28352 v h) (by intro d hd; cases hd)))
def cl_28414 : CNF.NClause := [(41,false),(75,true),(10,true),(76,false),(74,false),(73,false),(72,false)]
theorem der_28414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28414 :=
  CNF.rup_sound cl_28414 [cl_5330,cl_28352] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5330 v h) (hints_cons _ _ _ (der_28352 v h) (by intro d hd; cases hd)))
def cl_28415 : CNF.NClause := [(41,false),(72,true),(10,false),(73,false),(74,false),(75,true),(76,false)]
theorem der_28415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28415 :=
  CNF.rup_sound cl_28415 [cl_5331,cl_28384] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5331 v h) (hints_cons _ _ _ (der_28384 v h) (by intro d hd; cases hd)))
def cl_28416 : CNF.NClause := [(41,false),(75,true),(10,true),(72,true),(73,false),(74,false),(76,false)]
theorem der_28416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28416 :=
  CNF.rup_sound cl_28416 [cl_5332,cl_28354] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5332 v h) (hints_cons _ _ _ (der_28354 v h) (by intro d hd; cases hd)))
def cl_28417 : CNF.NClause := [(41,false),(10,false),(72,false),(74,false),(73,true),(76,false),(92,true)]
theorem der_28417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28417 :=
  CNF.rup_sound cl_28417 [cl_5333,cl_28401] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5333 v h) (hints_cons _ _ _ (der_28401 v h) (by intro d hd; cases hd)))
def cl_28418 : CNF.NClause := [(41,false),(75,true),(10,true),(72,false),(74,false),(73,true),(76,false)]
theorem der_28418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28418 :=
  CNF.rup_sound cl_28418 [cl_5334,cl_28356] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5334 v h) (hints_cons _ _ _ (der_28356 v h) (by intro d hd; cases hd)))
def cl_28419 : CNF.NClause := [(41,false),(72,true),(10,false),(73,true),(74,false),(76,false),(92,true)]
theorem der_28419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28419 :=
  CNF.rup_sound cl_28419 [cl_5335,cl_28403] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5335 v h) (hints_cons _ _ _ (der_28403 v h) (by intro d hd; cases hd)))
def cl_28420 : CNF.NClause := [(41,false),(75,true),(10,true),(74,false),(72,true),(76,false),(92,true)]
theorem der_28420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28420 :=
  CNF.rup_sound cl_28420 [cl_5336,cl_28416] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5336 v h) (hints_cons _ _ _ (der_28416 v h) (by intro d hd; cases hd)))
def cl_28421 : CNF.NClause := [(41,false),(75,true),(10,false),(72,false),(73,false),(74,true),(76,false)]
theorem der_28421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28421 :=
  CNF.rup_sound cl_28421 [cl_5337,cl_28359] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5337 v h) (hints_cons _ _ _ (der_28359 v h) (by intro d hd; cases hd)))
def cl_28422 : CNF.NClause := [(41,false),(75,true),(72,false),(73,false),(74,true),(76,false),(92,true)]
theorem der_28422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28422 :=
  CNF.rup_sound cl_28422 [cl_5338,cl_28421] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5338 v h) (hints_cons _ _ _ (der_28421 v h) (by intro d hd; cases hd)))
def cl_28423 : CNF.NClause := [(41,false),(72,true),(10,false),(73,false),(74,true),(75,true),(76,false)]
theorem der_28423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28423 :=
  CNF.rup_sound cl_28423 [cl_5339,cl_28361] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5339 v h) (hints_cons _ _ _ (der_28361 v h) (by intro d hd; cases hd)))
def cl_28424 : CNF.NClause := [(41,false),(75,true),(10,true),(72,true),(73,false),(76,false),(92,true)]
theorem der_28424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28424 :=
  CNF.rup_sound cl_28424 [cl_5340,cl_28416] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5340 v h) (hints_cons _ _ _ (der_28416 v h) (by intro d hd; cases hd)))
def cl_28425 : CNF.NClause := [(41,false),(74,true),(10,false),(72,false),(73,true),(75,true),(76,false)]
theorem der_28425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28425 :=
  CNF.rup_sound cl_28425 [cl_5341,cl_28363] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5341 v h) (hints_cons _ _ _ (der_28363 v h) (by intro d hd; cases hd)))
def cl_28426 : CNF.NClause := [(41,false),(74,true),(72,false),(73,true),(75,true),(76,false),(92,true)]
theorem der_28426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28426 :=
  CNF.rup_sound cl_28426 [cl_5342,cl_28425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5342 v h) (hints_cons _ _ _ (der_28425 v h) (by intro d hd; cases hd)))
def cl_28427 : CNF.NClause := [(41,false),(72,true),(10,false),(74,true),(75,true),(76,false),(92,true)]
theorem der_28427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28427 :=
  CNF.rup_sound cl_28427 [cl_5343,cl_28423] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5343 v h) (hints_cons _ _ _ (der_28423 v h) (by intro d hd; cases hd)))
def cl_28428 : CNF.NClause := [(41,false),(74,true),(10,true),(73,true),(72,true),(75,true),(76,false)]
theorem der_28428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28428 :=
  CNF.rup_sound cl_28428 [cl_5344,cl_28366] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5344 v h) (hints_cons _ _ _ (der_28366 v h) (by intro d hd; cases hd)))
def cl_28429 : CNF.NClause := [(41,false),(73,false),(10,false),(74,false),(72,false),(75,false),(76,true)]
theorem der_28429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28429 :=
  CNF.rup_sound cl_28429 [cl_5345,cl_5281] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5345 v h) (hints_cons _ _ _ (inp_5281 v h) (by intro d hd; cases hd)))
def cl_28430 : CNF.NClause := [(41,false),(10,true),(74,false),(75,false),(72,false),(73,false),(76,true)]
theorem der_28430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28430 :=
  CNF.rup_sound cl_28430 [cl_5346,cl_28367] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5346 v h) (hints_cons _ _ _ (der_28367 v h) (by intro d hd; cases hd)))
def cl_28431 : CNF.NClause := [(41,false),(72,true),(10,false),(73,false),(74,false),(75,false),(76,true)]
theorem der_28431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28431 :=
  CNF.rup_sound cl_28431 [cl_5347,cl_28368] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5347 v h) (hints_cons _ _ _ (der_28368 v h) (by intro d hd; cases hd)))
def cl_28432 : CNF.NClause := [(41,false),(72,true),(10,true),(73,false),(74,false),(76,true),(75,false)]
theorem der_28432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28432 :=
  CNF.rup_sound cl_28432 [cl_5348,cl_28369] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5348 v h) (hints_cons _ _ _ (der_28369 v h) (by intro d hd; cases hd)))
def cl_28434 : CNF.NClause := [(41,false),(10,true),(73,true),(74,false),(76,true),(75,false),(72,false)]
theorem der_28434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28434 :=
  CNF.rup_sound cl_28434 [cl_5350,cl_28371] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5350 v h) (hints_cons _ _ _ (der_28371 v h) (by intro d hd; cases hd)))
def cl_28435 : CNF.NClause := [(41,false),(72,true),(10,false),(73,true),(74,false),(75,false),(76,true)]
theorem der_28435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28435 :=
  CNF.rup_sound cl_28435 [cl_5351,cl_28372] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5351 v h) (hints_cons _ _ _ (der_28372 v h) (by intro d hd; cases hd)))
def cl_28436 : CNF.NClause := [(41,false),(72,true),(10,true),(73,true),(74,false),(75,false),(92,true)]
theorem der_28436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28436 :=
  CNF.rup_sound cl_28436 [cl_5352,cl_28404] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5352 v h) (hints_cons _ _ _ (der_28404 v h) (by intro d hd; cases hd)))
def cl_28437 : CNF.NClause := [(41,false),(10,false),(72,false),(73,false),(75,false),(76,true),(74,true)]
theorem der_28437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28437 :=
  CNF.rup_sound cl_28437 [cl_5353,cl_28374] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5353 v h) (hints_cons _ _ _ (der_28374 v h) (by intro d hd; cases hd)))
def cl_28438 : CNF.NClause := [(41,false),(74,true),(72,false),(75,false),(73,false),(92,true),(76,true)]
theorem der_28438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28438 :=
  CNF.rup_sound cl_28438 [cl_5354,cl_28437] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5354 v h) (hints_cons _ _ _ (der_28437 v h) (by intro d hd; cases hd)))
def cl_28439 : CNF.NClause := [(41,false),(10,false),(73,false),(74,true),(75,false),(76,true),(92,true)]
theorem der_28439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28439 :=
  CNF.rup_sound cl_28439 [cl_5355,cl_28437] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5355 v h) (hints_cons _ _ _ (der_28437 v h) (by intro d hd; cases hd)))
def cl_28440 : CNF.NClause := [(41,false),(74,true),(10,true),(92,true),(73,false),(76,true),(75,false)]
theorem der_28440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28440 :=
  CNF.rup_sound cl_28440 [cl_5356,cl_28438] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5356 v h) (hints_cons _ _ _ (der_28438 v h) (by intro d hd; cases hd)))
def cl_28441 : CNF.NClause := [(41,false),(74,true),(10,false),(72,false),(73,true),(75,false),(76,true)]
theorem der_28441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28441 :=
  CNF.rup_sound cl_28441 [cl_5357,cl_28378] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5357 v h) (hints_cons _ _ _ (der_28378 v h) (by intro d hd; cases hd)))
def cl_28442 : CNF.NClause := [(41,false),(74,true),(10,true),(72,false),(75,false),(76,true),(92,true)]
theorem der_28442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28442 :=
  CNF.rup_sound cl_28442 [cl_5358,cl_28438] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5358 v h) (hints_cons _ _ _ (der_28438 v h) (by intro d hd; cases hd)))
def cl_28443 : CNF.NClause := [(41,false),(10,false),(73,true),(74,true),(75,false),(76,true),(92,true)]
theorem der_28443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28443 :=
  CNF.rup_sound cl_28443 [cl_5359,cl_28441] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5359 v h) (hints_cons _ _ _ (der_28441 v h) (by intro d hd; cases hd)))
def cl_28444 : CNF.NClause := [(41,false),(74,true),(10,true),(73,true),(72,true),(75,false),(76,true)]
theorem der_28444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28444 :=
  CNF.rup_sound cl_28444 [cl_5360,cl_28381] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5360 v h) (hints_cons _ _ _ (der_28381 v h) (by intro d hd; cases hd)))
def cl_28445 : CNF.NClause := [(41,false),(10,false),(72,false),(73,false),(74,false),(76,true),(92,true)]
theorem der_28445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28445 :=
  CNF.rup_sound cl_28445 [cl_5361,cl_28429] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5361 v h) (hints_cons _ _ _ (der_28429 v h) (by intro d hd; cases hd)))
def cl_28446 : CNF.NClause := [(41,false),(75,true),(10,true),(72,false),(73,false),(74,false),(76,true)]
theorem der_28446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28446 :=
  CNF.rup_sound cl_28446 [cl_5362,cl_28383] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5362 v h) (hints_cons _ _ _ (der_28383 v h) (by intro d hd; cases hd)))
def cl_28447 : CNF.NClause := [(41,false),(72,true),(10,false),(73,false),(74,false),(75,true),(76,true)]
theorem der_28447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28447 :=
  CNF.rup_sound cl_28447 [cl_5363,cl_28384] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5363 v h) (hints_cons _ _ _ (der_28384 v h) (by intro d hd; cases hd)))
def cl_28448 : CNF.NClause := [(41,false),(75,true),(10,true),(72,true),(73,false),(74,false),(92,true)]
theorem der_28448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28448 :=
  CNF.rup_sound cl_28448 [cl_5364,cl_28416] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5364 v h) (hints_cons _ _ _ (der_28416 v h) (by intro d hd; cases hd)))
def cl_28449 : CNF.NClause := [(41,false),(75,true),(10,false),(72,false),(74,false),(73,true),(76,true)]
theorem der_28449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28449 :=
  CNF.rup_sound cl_28449 [cl_5365,cl_28386] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5365 v h) (hints_cons _ _ _ (der_28386 v h) (by intro d hd; cases hd)))
def cl_28450 : CNF.NClause := [(41,false),(75,true),(72,false),(74,false),(73,true),(76,true),(92,true)]
theorem der_28450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28450 :=
  CNF.rup_sound cl_28450 [cl_5366,cl_28449] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5366 v h) (hints_cons _ _ _ (der_28449 v h) (by intro d hd; cases hd)))
def cl_28451 : CNF.NClause := [(41,false),(72,true),(10,false),(73,true),(74,false),(75,true),(76,true)]
theorem der_28451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28451 :=
  CNF.rup_sound cl_28451 [cl_5367,cl_28388] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5367 v h) (hints_cons _ _ _ (der_28388 v h) (by intro d hd; cases hd)))
def cl_28452 : CNF.NClause := [(41,false),(75,true),(10,true),(73,true),(74,false),(72,true),(76,true)]
theorem der_28452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28452 :=
  CNF.rup_sound cl_28452 [cl_5368,cl_28389] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5368 v h) (hints_cons _ _ _ (der_28389 v h) (by intro d hd; cases hd)))
def cl_28453 : CNF.NClause := [(41,false),(10,false),(72,false),(73,false),(74,true),(76,true),(92,true)]
theorem der_28453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28453 :=
  CNF.rup_sound cl_28453 [cl_5369,cl_28437] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5369 v h) (hints_cons _ _ _ (der_28437 v h) (by intro d hd; cases hd)))
def cl_28454 : CNF.NClause := [(41,false),(10,true),(72,false),(73,false),(74,true),(76,true),(92,true)]
theorem der_28454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28454 :=
  CNF.rup_sound cl_28454 [cl_5370,cl_28442] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5370 v h) (hints_cons _ _ _ (der_28442 v h) (by intro d hd; cases hd)))
def cl_28455 : CNF.NClause := [(41,false),(72,true),(10,false),(73,false),(74,true),(75,true),(76,true)]
theorem der_28455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28455 :=
  CNF.rup_sound cl_28455 [cl_5371,cl_28392] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5371 v h) (hints_cons _ _ _ (der_28392 v h) (by intro d hd; cases hd)))
def cl_28456 : CNF.NClause := [(41,false),(75,true),(10,true),(72,true),(73,false),(74,true),(76,true)]
theorem der_28456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28456 :=
  CNF.rup_sound cl_28456 [cl_5372,cl_28393] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5372 v h) (hints_cons _ _ _ (der_28393 v h) (by intro d hd; cases hd)))
def cl_28457 : CNF.NClause := [(41,false),(10,false),(72,false),(73,true),(75,true),(76,true),(92,true)]
theorem der_28457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28457 :=
  CNF.rup_sound cl_28457 [cl_5373,cl_28449] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5373 v h) (hints_cons _ _ _ (der_28449 v h) (by intro d hd; cases hd)))
def cl_28458 : CNF.NClause := [(41,false),(74,true),(10,true),(72,false),(75,true),(76,true),(92,true)]
theorem der_28458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28458 :=
  CNF.rup_sound cl_28458 [cl_5374,cl_28454] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5374 v h) (hints_cons _ _ _ (der_28454 v h) (by intro d hd; cases hd)))
def cl_28460 : CNF.NClause := [(41,false),(74,true),(10,true),(72,true),(75,true),(76,true),(92,true)]
theorem der_28460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28460 :=
  CNF.rup_sound cl_28460 [cl_5376,cl_28456] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5376 v h) (hints_cons _ _ _ (der_28456 v h) (by intro d hd; cases hd)))
def cl_28461 : CNF.NClause := [(35,false),(78,false),(4,true),(68,false),(73,false),(83,false),(87,false)]
theorem der_28461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28461 :=
  CNF.rup_sound cl_28461 [cl_4482,cl_4484] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4482 v h) (hints_cons _ _ _ (inp_4484 v h) (by intro d hd; cases hd)))
def cl_28462 : CNF.NClause := [(35,false),(63,true),(68,false),(73,false),(87,false),(83,false),(78,false)]
theorem der_28462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28462 :=
  CNF.rup_sound cl_28462 [cl_4483,cl_28461] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4483 v h) (hints_cons _ _ _ (der_28461 v h) (by intro d hd; cases hd)))
def cl_28463 : CNF.NClause := [(35,false),(78,false),(63,false),(73,false),(68,true),(83,false),(87,false)]
theorem der_28463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28463 :=
  CNF.rup_sound cl_28463 [cl_4486,cl_4485] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4486 v h) (hints_cons _ _ _ (inp_4485 v h) (by intro d hd; cases hd)))
def cl_28464 : CNF.NClause := [(35,false),(4,false),(78,false),(73,false),(63,true),(83,false),(87,false)]
theorem der_28464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28464 :=
  CNF.rup_sound cl_28464 [cl_4487,cl_28462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4487 v h) (hints_cons _ _ _ (der_28462 v h) (by intro d hd; cases hd)))
def cl_28465 : CNF.NClause := [(35,false),(63,true),(4,true),(73,false),(78,false),(83,false),(87,false)]
theorem der_28465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28465 :=
  CNF.rup_sound cl_28465 [cl_4488,cl_28462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4488 v h) (hints_cons _ _ _ (der_28462 v h) (by intro d hd; cases hd)))
def cl_28466 : CNF.NClause := [(35,false),(73,true),(68,false),(63,false),(78,false),(83,false),(87,false)]
theorem der_28466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28466 :=
  CNF.rup_sound cl_28466 [cl_4490,cl_4489] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4490 v h) (hints_cons _ _ _ (inp_4489 v h) (by intro d hd; cases hd)))
def cl_28467 : CNF.NClause := [(35,false),(63,true),(4,false),(68,false),(78,false),(83,false),(87,false)]
theorem der_28467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28467 :=
  CNF.rup_sound cl_28467 [cl_4491,cl_28462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4491 v h) (hints_cons _ _ _ (der_28462 v h) (by intro d hd; cases hd)))
def cl_28468 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(78,false),(83,false),(87,false)]
theorem der_28468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28468 :=
  CNF.rup_sound cl_28468 [cl_4492,cl_28462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4492 v h) (hints_cons _ _ _ (der_28462 v h) (by intro d hd; cases hd)))
def cl_28469 : CNF.NClause := [(35,false),(68,true),(4,false),(63,false),(78,false),(83,false),(87,false)]
theorem der_28469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28469 :=
  CNF.rup_sound cl_28469 [cl_4493,cl_28463] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4493 v h) (hints_cons _ _ _ (der_28463 v h) (by intro d hd; cases hd)))
def cl_28470 : CNF.NClause := [(35,false),(4,true),(68,true),(63,false),(78,false),(83,false),(87,false)]
theorem der_28470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28470 :=
  CNF.rup_sound cl_28470 [cl_4494,cl_28463] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4494 v h) (hints_cons _ _ _ (der_28463 v h) (by intro d hd; cases hd)))
def cl_28471 : CNF.NClause := [(35,false),(68,true),(4,false),(63,true),(78,false),(83,false),(87,false)]
theorem der_28471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28471 :=
  CNF.rup_sound cl_28471 [cl_4495,cl_28464] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4495 v h) (hints_cons _ _ _ (der_28464 v h) (by intro d hd; cases hd)))
def cl_28472 : CNF.NClause := [(35,false),(73,true),(68,true),(63,true),(78,false),(83,false),(87,false)]
theorem der_28472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28472 :=
  CNF.rup_sound cl_28472 [cl_4496,cl_28471] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4496 v h) (hints_cons _ _ _ (der_28471 v h) (by intro d hd; cases hd)))
def cl_28473 : CNF.NClause := [(35,false),(83,false),(68,false),(63,false),(73,false),(78,true),(87,false)]
theorem der_28473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28473 :=
  CNF.rup_sound cl_28473 [cl_4498,cl_4497] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4498 v h) (hints_cons _ _ _ (inp_4497 v h) (by intro d hd; cases hd)))
def cl_28474 : CNF.NClause := [(35,false),(63,true),(4,false),(83,false),(68,false),(73,false),(87,false)]
theorem der_28474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28474 :=
  CNF.rup_sound cl_28474 [cl_4499,cl_28462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4499 v h) (hints_cons _ _ _ (der_28462 v h) (by intro d hd; cases hd)))
def cl_28475 : CNF.NClause := [(35,false),(83,false),(4,true),(63,true),(68,false),(73,false),(87,false)]
theorem der_28475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28475 :=
  CNF.rup_sound cl_28475 [cl_4500,cl_28462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4500 v h) (hints_cons _ _ _ (der_28462 v h) (by intro d hd; cases hd)))
def cl_28476 : CNF.NClause := [(35,false),(68,true),(4,false),(83,false),(63,false),(73,false),(87,false)]
theorem der_28476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28476 :=
  CNF.rup_sound cl_28476 [cl_4501,cl_28463] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4501 v h) (hints_cons _ _ _ (der_28463 v h) (by intro d hd; cases hd)))
def cl_28477 : CNF.NClause := [(35,false),(83,false),(4,true),(68,true),(63,false),(73,false),(87,false)]
theorem der_28477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28477 :=
  CNF.rup_sound cl_28477 [cl_4502,cl_28463] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4502 v h) (hints_cons _ _ _ (der_28463 v h) (by intro d hd; cases hd)))
def cl_28478 : CNF.NClause := [(35,false),(68,true),(4,false),(83,false),(63,true),(73,false),(87,false)]
theorem der_28478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28478 :=
  CNF.rup_sound cl_28478 [cl_4503,cl_28464] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4503 v h) (hints_cons _ _ _ (der_28464 v h) (by intro d hd; cases hd)))
def cl_28479 : CNF.NClause := [(35,false),(78,true),(68,true),(73,false),(63,true),(83,false),(87,false)]
theorem der_28479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28479 :=
  CNF.rup_sound cl_28479 [cl_4504,cl_28478] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4504 v h) (hints_cons _ _ _ (der_28478 v h) (by intro d hd; cases hd)))
def cl_28480 : CNF.NClause := [(35,false),(4,false),(68,false),(63,false),(73,true),(83,false),(87,false)]
theorem der_28480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28480 :=
  CNF.rup_sound cl_28480 [cl_4505,cl_28466] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4505 v h) (hints_cons _ _ _ (der_28466 v h) (by intro d hd; cases hd)))
def cl_28481 : CNF.NClause := [(35,false),(4,true),(68,false),(63,false),(73,true),(83,false),(87,false)]
theorem der_28481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28481 :=
  CNF.rup_sound cl_28481 [cl_4506,cl_28466] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4506 v h) (hints_cons _ _ _ (der_28466 v h) (by intro d hd; cases hd)))
def cl_28482 : CNF.NClause := [(35,false),(4,false),(68,false),(63,true),(73,true),(83,false),(87,false)]
theorem der_28482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28482 :=
  CNF.rup_sound cl_28482 [cl_4507,cl_28467] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4507 v h) (hints_cons _ _ _ (der_28467 v h) (by intro d hd; cases hd)))
def cl_28483 : CNF.NClause := [(35,false),(78,true),(63,true),(68,false),(73,true),(83,false),(87,false)]
theorem der_28483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28483 :=
  CNF.rup_sound cl_28483 [cl_4508,cl_28482] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4508 v h) (hints_cons _ _ _ (der_28482 v h) (by intro d hd; cases hd)))
def cl_28484 : CNF.NClause := [(35,false),(4,false),(68,true),(63,false),(73,true),(83,false),(87,false)]
theorem der_28484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28484 :=
  CNF.rup_sound cl_28484 [cl_4509,cl_28469] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4509 v h) (hints_cons _ _ _ (der_28469 v h) (by intro d hd; cases hd)))
def cl_28485 : CNF.NClause := [(35,false),(78,true),(68,true),(63,false),(73,true),(83,false),(87,false)]
theorem der_28485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28485 :=
  CNF.rup_sound cl_28485 [cl_4510,cl_28484] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4510 v h) (hints_cons _ _ _ (der_28484 v h) (by intro d hd; cases hd)))
def cl_28486 : CNF.NClause := [(35,false),(4,false),(68,true),(63,true),(73,true),(83,false),(87,false)]
theorem der_28486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28486 :=
  CNF.rup_sound cl_28486 [cl_4511,cl_28472] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4511 v h) (hints_cons _ _ _ (der_28472 v h) (by intro d hd; cases hd)))
def cl_28487 : CNF.NClause := [(35,false),(4,true),(68,true),(63,true),(73,true),(83,false),(87,false)]
theorem der_28487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28487 :=
  CNF.rup_sound cl_28487 [cl_4512,cl_28472] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4512 v h) (hints_cons _ _ _ (der_28472 v h) (by intro d hd; cases hd)))
def cl_28488 : CNF.NClause := [(35,false),(83,true),(68,false),(63,false),(78,false),(73,false),(87,false)]
theorem der_28488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28488 :=
  CNF.rup_sound cl_28488 [cl_4514,cl_4513] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4514 v h) (hints_cons _ _ _ (inp_4513 v h) (by intro d hd; cases hd)))
def cl_28489 : CNF.NClause := [(35,false),(4,false),(68,false),(63,true),(78,false),(73,false),(87,false)]
theorem der_28489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28489 :=
  CNF.rup_sound cl_28489 [cl_4515,cl_28462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4515 v h) (hints_cons _ _ _ (der_28462 v h) (by intro d hd; cases hd)))
def cl_28490 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,false),(78,false),(87,false)]
theorem der_28490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28490 :=
  CNF.rup_sound cl_28490 [cl_4516,cl_28462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4516 v h) (hints_cons _ _ _ (der_28462 v h) (by intro d hd; cases hd)))
def cl_28491 : CNF.NClause := [(35,false),(4,false),(68,true),(63,false),(78,false),(73,false),(87,false)]
theorem der_28491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28491 :=
  CNF.rup_sound cl_28491 [cl_4517,cl_28463] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4517 v h) (hints_cons _ _ _ (der_28463 v h) (by intro d hd; cases hd)))
def cl_28492 : CNF.NClause := [(35,false),(4,true),(68,true),(63,false),(78,false),(73,false),(87,false)]
theorem der_28492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28492 :=
  CNF.rup_sound cl_28492 [cl_4518,cl_28463] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4518 v h) (hints_cons _ _ _ (der_28463 v h) (by intro d hd; cases hd)))
def cl_28493 : CNF.NClause := [(35,false),(4,false),(68,true),(63,true),(78,false),(73,false),(87,false)]
theorem der_28493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28493 :=
  CNF.rup_sound cl_28493 [cl_4519,cl_28478] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4519 v h) (hints_cons _ _ _ (der_28478 v h) (by intro d hd; cases hd)))
def cl_28494 : CNF.NClause := [(35,false),(4,true),(68,true),(73,false),(78,false),(63,true),(87,false)]
theorem der_28494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28494 :=
  CNF.rup_sound cl_28494 [cl_4520,cl_28465] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4520 v h) (hints_cons _ _ _ (der_28465 v h) (by intro d hd; cases hd)))
def cl_28495 : CNF.NClause := [(35,false),(4,false),(68,false),(63,false),(78,false),(73,true),(87,false)]
theorem der_28495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28495 :=
  CNF.rup_sound cl_28495 [cl_4521,cl_28466] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4521 v h) (hints_cons _ _ _ (der_28466 v h) (by intro d hd; cases hd)))
def cl_28496 : CNF.NClause := [(35,false),(4,true),(68,false),(63,false),(78,false),(73,true),(87,false)]
theorem der_28496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28496 :=
  CNF.rup_sound cl_28496 [cl_4522,cl_28466] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4522 v h) (hints_cons _ _ _ (der_28466 v h) (by intro d hd; cases hd)))
def cl_28497 : CNF.NClause := [(35,false),(83,true),(4,false),(68,false),(78,false),(73,true),(87,false)]
theorem der_28497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28497 :=
  CNF.rup_sound cl_28497 [cl_4523,cl_28495] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4523 v h) (hints_cons _ _ _ (der_28495 v h) (by intro d hd; cases hd)))
def cl_28498 : CNF.NClause := [(35,false),(83,true),(63,true),(68,false),(78,false),(73,true),(87,false)]
theorem der_28498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28498 :=
  CNF.rup_sound cl_28498 [cl_4524,cl_28497] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4524 v h) (hints_cons _ _ _ (der_28497 v h) (by intro d hd; cases hd)))
def cl_28499 : CNF.NClause := [(35,false),(83,true),(4,false),(63,false),(78,false),(73,true),(87,false)]
theorem der_28499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28499 :=
  CNF.rup_sound cl_28499 [cl_4525,cl_28495] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4525 v h) (hints_cons _ _ _ (der_28495 v h) (by intro d hd; cases hd)))
def cl_28500 : CNF.NClause := [(35,false),(83,true),(68,true),(63,false),(78,false),(73,true),(87,false)]
theorem der_28500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28500 :=
  CNF.rup_sound cl_28500 [cl_4526,cl_28499] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4526 v h) (hints_cons _ _ _ (der_28499 v h) (by intro d hd; cases hd)))
def cl_28501 : CNF.NClause := [(35,false),(4,false),(68,true),(63,true),(78,false),(73,true),(87,false)]
theorem der_28501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28501 :=
  CNF.rup_sound cl_28501 [cl_4527,cl_28472] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4527 v h) (hints_cons _ _ _ (der_28472 v h) (by intro d hd; cases hd)))
def cl_28502 : CNF.NClause := [(35,false),(4,true),(68,true),(63,true),(78,false),(73,true),(87,false)]
theorem der_28502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28502 :=
  CNF.rup_sound cl_28502 [cl_4528,cl_28472] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4528 v h) (hints_cons _ _ _ (der_28472 v h) (by intro d hd; cases hd)))
def cl_28503 : CNF.NClause := [(35,false),(4,false),(68,false),(73,false),(63,false),(78,true),(87,false)]
theorem der_28503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28503 :=
  CNF.rup_sound cl_28503 [cl_4529,cl_28473] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4529 v h) (hints_cons _ _ _ (der_28473 v h) (by intro d hd; cases hd)))
def cl_28504 : CNF.NClause := [(35,false),(4,true),(68,false),(63,false),(73,false),(78,true),(87,false)]
theorem der_28504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28504 :=
  CNF.rup_sound cl_28504 [cl_4530,cl_28473] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4530 v h) (hints_cons _ _ _ (der_28473 v h) (by intro d hd; cases hd)))
def cl_28505 : CNF.NClause := [(35,false),(4,false),(68,false),(63,true),(73,false),(78,true),(87,false)]
theorem der_28505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28505 :=
  CNF.rup_sound cl_28505 [cl_4531,cl_28474] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4531 v h) (hints_cons _ _ _ (der_28474 v h) (by intro d hd; cases hd)))
def cl_28506 : CNF.NClause := [(35,false),(83,true),(63,true),(68,false),(73,false),(78,true),(87,false)]
theorem der_28506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28506 :=
  CNF.rup_sound cl_28506 [cl_4532,cl_28505] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4532 v h) (hints_cons _ _ _ (der_28505 v h) (by intro d hd; cases hd)))
def cl_28507 : CNF.NClause := [(35,false),(4,false),(68,true),(63,false),(73,false),(78,true),(87,false)]
theorem der_28507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28507 :=
  CNF.rup_sound cl_28507 [cl_4533,cl_28476] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4533 v h) (hints_cons _ _ _ (der_28476 v h) (by intro d hd; cases hd)))
def cl_28508 : CNF.NClause := [(35,false),(83,true),(68,true),(63,false),(73,false),(78,true),(87,false)]
theorem der_28508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28508 :=
  CNF.rup_sound cl_28508 [cl_4534,cl_28507] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4534 v h) (hints_cons _ _ _ (der_28507 v h) (by intro d hd; cases hd)))
def cl_28509 : CNF.NClause := [(35,false),(4,false),(68,true),(63,true),(73,false),(78,true),(87,false)]
theorem der_28509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28509 :=
  CNF.rup_sound cl_28509 [cl_4535,cl_28478] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4535 v h) (hints_cons _ _ _ (der_28478 v h) (by intro d hd; cases hd)))
def cl_28510 : CNF.NClause := [(35,false),(78,true),(4,true),(68,true),(73,false),(63,true),(87,false)]
theorem der_28510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28510 :=
  CNF.rup_sound cl_28510 [cl_4536,cl_28479] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4536 v h) (hints_cons _ _ _ (der_28479 v h) (by intro d hd; cases hd)))
def cl_28511 : CNF.NClause := [(35,false),(4,false),(68,false),(63,false),(73,true),(83,true),(87,false)]
theorem der_28511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28511 :=
  CNF.rup_sound cl_28511 [cl_4537,cl_28495] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4537 v h) (hints_cons _ _ _ (der_28495 v h) (by intro d hd; cases hd)))
def cl_28512 : CNF.NClause := [(35,false),(78,true),(4,true),(68,false),(63,false),(73,true),(87,false)]
theorem der_28512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28512 :=
  CNF.rup_sound cl_28512 [cl_4538,cl_28481] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4538 v h) (hints_cons _ _ _ (der_28481 v h) (by intro d hd; cases hd)))
def cl_28513 : CNF.NClause := [(35,false),(78,true),(4,false),(68,false),(63,true),(73,true),(87,false)]
theorem der_28513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28513 :=
  CNF.rup_sound cl_28513 [cl_4539,cl_28483] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4539 v h) (hints_cons _ _ _ (der_28483 v h) (by intro d hd; cases hd)))
def cl_28514 : CNF.NClause := [(35,false),(78,true),(4,true),(63,true),(68,false),(73,true),(87,false)]
theorem der_28514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28514 :=
  CNF.rup_sound cl_28514 [cl_4540,cl_28483] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4540 v h) (hints_cons _ _ _ (der_28483 v h) (by intro d hd; cases hd)))
def cl_28515 : CNF.NClause := [(35,false),(78,true),(4,false),(68,true),(63,false),(73,true),(87,false)]
theorem der_28515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28515 :=
  CNF.rup_sound cl_28515 [cl_4541,cl_28485] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4541 v h) (hints_cons _ _ _ (der_28485 v h) (by intro d hd; cases hd)))
def cl_28516 : CNF.NClause := [(35,false),(78,true),(4,true),(68,true),(63,false),(73,true),(87,false)]
theorem der_28516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28516 :=
  CNF.rup_sound cl_28516 [cl_4542,cl_28485] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4542 v h) (hints_cons _ _ _ (der_28485 v h) (by intro d hd; cases hd)))
def cl_28517 : CNF.NClause := [(35,false),(78,true),(4,false),(63,true),(73,true),(83,true),(87,false)]
theorem der_28517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28517 :=
  CNF.rup_sound cl_28517 [cl_4543,cl_28513] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4543 v h) (hints_cons _ _ _ (der_28513 v h) (by intro d hd; cases hd)))
def cl_28518 : CNF.NClause := [(35,false),(78,true),(68,true),(63,true),(73,true),(83,true),(87,false)]
theorem der_28518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28518 :=
  CNF.rup_sound cl_28518 [cl_4544,cl_28517] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4544 v h) (hints_cons _ _ _ (der_28517 v h) (by intro d hd; cases hd)))
def cl_28519 : CNF.NClause := [(35,false),(68,false),(4,true),(83,false),(73,false),(63,false),(78,false)]
theorem der_28519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28519 :=
  CNF.rup_sound cl_28519 [cl_4546,cl_28461] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4546 v h) (hints_cons _ _ _ (der_28461 v h) (by intro d hd; cases hd)))
def cl_28520 : CNF.NClause := [(35,false),(4,false),(68,false),(73,false),(63,true),(83,false),(78,false)]
theorem der_28520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28520 :=
  CNF.rup_sound cl_28520 [cl_4547,cl_28462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4547 v h) (hints_cons _ _ _ (der_28462 v h) (by intro d hd; cases hd)))
def cl_28521 : CNF.NClause := [(35,false),(4,false),(68,true),(73,false),(63,false),(83,false),(78,false)]
theorem der_28521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28521 :=
  CNF.rup_sound cl_28521 [cl_4549,cl_28463] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4549 v h) (hints_cons _ _ _ (der_28463 v h) (by intro d hd; cases hd)))
def cl_28522 : CNF.NClause := [(35,false),(68,true),(4,true),(63,false),(73,false),(78,false),(83,false)]
theorem der_28522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28522 :=
  CNF.rup_sound cl_28522 [cl_4550,cl_28463] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4550 v h) (hints_cons _ _ _ (der_28463 v h) (by intro d hd; cases hd)))
def cl_28523 : CNF.NClause := [(35,false),(4,false),(68,true),(73,false),(63,true),(83,false),(78,false)]
theorem der_28523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28523 :=
  CNF.rup_sound cl_28523 [cl_4551,cl_28478] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4551 v h) (hints_cons _ _ _ (der_28478 v h) (by intro d hd; cases hd)))
def cl_28524 : CNF.NClause := [(35,false),(68,true),(4,true),(73,false),(63,true),(83,false),(78,false)]
theorem der_28524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28524 :=
  CNF.rup_sound cl_28524 [cl_4552,cl_28465] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4552 v h) (hints_cons _ _ _ (der_28465 v h) (by intro d hd; cases hd)))
def cl_28525 : CNF.NClause := [(35,false),(68,false),(4,false),(63,false),(73,true),(78,false),(83,false)]
theorem der_28525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28525 :=
  CNF.rup_sound cl_28525 [cl_4553,cl_28466] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4553 v h) (hints_cons _ _ _ (der_28466 v h) (by intro d hd; cases hd)))
def cl_28526 : CNF.NClause := [(35,false),(68,false),(4,true),(83,false),(63,false),(78,false),(73,true)]
theorem der_28526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28526 :=
  CNF.rup_sound cl_28526 [cl_4554,cl_28466] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4554 v h) (hints_cons _ _ _ (der_28466 v h) (by intro d hd; cases hd)))
def cl_28527 : CNF.NClause := [(35,false),(4,false),(73,true),(68,false),(78,false),(83,false),(87,true)]
theorem der_28527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28527 :=
  CNF.rup_sound cl_28527 [cl_4555,cl_28525] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4555 v h) (hints_cons _ _ _ (der_28525 v h) (by intro d hd; cases hd)))
def cl_28528 : CNF.NClause := [(35,false),(4,true),(83,false),(68,false),(73,true),(78,false),(87,true)]
theorem der_28528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28528 :=
  CNF.rup_sound cl_28528 [cl_4556,cl_28526] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4556 v h) (hints_cons _ _ _ (der_28526 v h) (by intro d hd; cases hd)))
def cl_28529 : CNF.NClause := [(35,false),(68,true),(4,false),(78,false),(63,false),(73,true),(83,false)]
theorem der_28529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28529 :=
  CNF.rup_sound cl_28529 [cl_4557,cl_28469] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4557 v h) (hints_cons _ _ _ (der_28469 v h) (by intro d hd; cases hd)))
def cl_28530 : CNF.NClause := [(35,false),(4,true),(78,false),(63,false),(73,true),(83,false),(87,true)]
theorem der_28530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28530 :=
  CNF.rup_sound cl_28530 [cl_4558,cl_28526] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4558 v h) (hints_cons _ _ _ (der_28526 v h) (by intro d hd; cases hd)))
def cl_28531 : CNF.NClause := [(35,false),(68,true),(4,false),(73,true),(63,true),(78,false),(83,false)]
theorem der_28531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28531 :=
  CNF.rup_sound cl_28531 [cl_4559,cl_28472] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4559 v h) (hints_cons _ _ _ (der_28472 v h) (by intro d hd; cases hd)))
def cl_28532 : CNF.NClause := [(35,false),(68,true),(4,true),(73,true),(63,true),(78,false),(83,false)]
theorem der_28532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28532 :=
  CNF.rup_sound cl_28532 [cl_4560,cl_28472] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4560 v h) (hints_cons _ _ _ (der_28472 v h) (by intro d hd; cases hd)))
def cl_28533 : CNF.NClause := [(35,false),(78,true),(4,false),(63,false),(83,false),(73,false),(68,false)]
theorem der_28533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28533 :=
  CNF.rup_sound cl_28533 [cl_4561,cl_28473] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4561 v h) (hints_cons _ _ _ (der_28473 v h) (by intro d hd; cases hd)))
def cl_28534 : CNF.NClause := [(35,false),(78,true),(4,true),(68,false),(63,false),(73,false),(83,false)]
theorem der_28534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28534 :=
  CNF.rup_sound cl_28534 [cl_4562,cl_28473] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4562 v h) (hints_cons _ _ _ (der_28473 v h) (by intro d hd; cases hd)))
def cl_28535 : CNF.NClause := [(35,false),(63,true),(4,false),(83,false),(68,false),(73,false),(78,true)]
theorem der_28535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28535 :=
  CNF.rup_sound cl_28535 [cl_4563,cl_28505] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4563 v h) (hints_cons _ _ _ (der_28505 v h) (by intro d hd; cases hd)))
def cl_28536 : CNF.NClause := [(35,false),(78,true),(4,true),(83,false),(73,false),(68,false),(87,true)]
theorem der_28536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28536 :=
  CNF.rup_sound cl_28536 [cl_4564,cl_28534] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4564 v h) (hints_cons _ _ _ (der_28534 v h) (by intro d hd; cases hd)))
def cl_28537 : CNF.NClause := [(35,false),(68,true),(4,false),(83,false),(63,false),(73,false),(78,true)]
theorem der_28537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28537 :=
  CNF.rup_sound cl_28537 [cl_4565,cl_28476] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4565 v h) (hints_cons _ _ _ (der_28476 v h) (by intro d hd; cases hd)))
def cl_28538 : CNF.NClause := [(35,false),(78,true),(4,true),(63,false),(73,false),(83,false),(87,true)]
theorem der_28538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28538 :=
  CNF.rup_sound cl_28538 [cl_4566,cl_28534] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4566 v h) (hints_cons _ _ _ (der_28534 v h) (by intro d hd; cases hd)))
def cl_28539 : CNF.NClause := [(35,false),(68,true),(4,false),(83,false),(63,true),(73,false),(78,true)]
theorem der_28539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28539 :=
  CNF.rup_sound cl_28539 [cl_4567,cl_28478] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4567 v h) (hints_cons _ _ _ (der_28478 v h) (by intro d hd; cases hd)))
def cl_28540 : CNF.NClause := [(35,false),(78,true),(4,true),(68,true),(73,false),(63,true),(83,false)]
theorem der_28540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28540 :=
  CNF.rup_sound cl_28540 [cl_4568,cl_28479] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4568 v h) (hints_cons _ _ _ (der_28479 v h) (by intro d hd; cases hd)))
def cl_28541 : CNF.NClause := [(35,false),(78,true),(4,false),(63,false),(68,false),(83,false),(87,true)]
theorem der_28541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28541 :=
  CNF.rup_sound cl_28541 [cl_4569,cl_28533] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4569 v h) (hints_cons _ _ _ (der_28533 v h) (by intro d hd; cases hd)))
def cl_28542 : CNF.NClause := [(35,false),(4,true),(68,false),(63,false),(73,true),(83,false),(87,true)]
theorem der_28542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28542 :=
  CNF.rup_sound cl_28542 [cl_4570,cl_28526] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4570 v h) (hints_cons _ _ _ (der_28526 v h) (by intro d hd; cases hd)))
def cl_28543 : CNF.NClause := [(35,false),(78,true),(4,false),(68,false),(63,true),(73,true),(83,false)]
theorem der_28543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28543 :=
  CNF.rup_sound cl_28543 [cl_4571,cl_28483] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4571 v h) (hints_cons _ _ _ (der_28483 v h) (by intro d hd; cases hd)))
def cl_28544 : CNF.NClause := [(35,false),(78,true),(4,true),(63,true),(68,false),(73,true),(83,false)]
theorem der_28544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28544 :=
  CNF.rup_sound cl_28544 [cl_4572,cl_28483] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4572 v h) (hints_cons _ _ _ (der_28483 v h) (by intro d hd; cases hd)))
def cl_28545 : CNF.NClause := [(35,false),(78,true),(4,false),(68,true),(63,false),(73,true),(83,false)]
theorem der_28545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28545 :=
  CNF.rup_sound cl_28545 [cl_4573,cl_28485] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4573 v h) (hints_cons _ _ _ (der_28485 v h) (by intro d hd; cases hd)))
def cl_28546 : CNF.NClause := [(35,false),(78,true),(4,true),(68,true),(63,false),(73,true),(83,false)]
theorem der_28546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28546 :=
  CNF.rup_sound cl_28546 [cl_4574,cl_28485] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4574 v h) (hints_cons _ _ _ (der_28485 v h) (by intro d hd; cases hd)))
def cl_28547 : CNF.NClause := [(35,false),(78,true),(4,false),(63,true),(73,true),(83,false),(87,true)]
theorem der_28547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28547 :=
  CNF.rup_sound cl_28547 [cl_4575,cl_28543] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4575 v h) (hints_cons _ _ _ (der_28543 v h) (by intro d hd; cases hd)))
def cl_28548 : CNF.NClause := [(35,false),(78,true),(4,true),(68,true),(63,true),(83,false),(87,true)]
theorem der_28548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28548 :=
  CNF.rup_sound cl_28548 [cl_4576,cl_28540] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4576 v h) (hints_cons _ _ _ (der_28540 v h) (by intro d hd; cases hd)))
def cl_28549 : CNF.NClause := [(35,false),(83,true),(4,false),(63,false),(73,false),(78,false),(68,false)]
theorem der_28549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28549 :=
  CNF.rup_sound cl_28549 [cl_4577,cl_4513] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4577 v h) (hints_cons _ _ _ (inp_4513 v h) (by intro d hd; cases hd)))
def cl_28550 : CNF.NClause := [(35,false),(83,true),(4,true),(68,false),(63,false),(78,false),(73,false)]
theorem der_28550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28550 :=
  CNF.rup_sound cl_28550 [cl_4578,cl_28488] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4578 v h) (hints_cons _ _ _ (der_28488 v h) (by intro d hd; cases hd)))
def cl_28551 : CNF.NClause := [(35,false),(4,false),(68,false),(63,true),(78,false),(73,false),(87,true)]
theorem der_28551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28551 :=
  CNF.rup_sound cl_28551 [cl_4579,cl_28520] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4579 v h) (hints_cons _ _ _ (der_28520 v h) (by intro d hd; cases hd)))
def cl_28552 : CNF.NClause := [(35,false),(4,true),(63,true),(68,false),(73,false),(78,false),(87,true)]
theorem der_28552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28552 :=
  CNF.rup_sound cl_28552 [cl_4580,cl_26324] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4580 v h) (hints_cons _ _ _ (der_26324 v h) (by intro d hd; cases hd)))
def cl_28553 : CNF.NClause := [(35,false),(83,true),(4,false),(63,false),(78,false),(73,false),(87,true)]
theorem der_28553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28553 :=
  CNF.rup_sound cl_28553 [cl_4581,cl_28549] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4581 v h) (hints_cons _ _ _ (der_28549 v h) (by intro d hd; cases hd)))
def cl_28554 : CNF.NClause := [(35,false),(83,true),(4,true),(63,false),(78,false),(73,false),(87,true)]
theorem der_28554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28554 :=
  CNF.rup_sound cl_28554 [cl_4582,cl_28550] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4582 v h) (hints_cons _ _ _ (der_28550 v h) (by intro d hd; cases hd)))
def cl_28555 : CNF.NClause := [(35,false),(4,false),(68,true),(63,true),(78,false),(73,false),(87,true)]
theorem der_28555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28555 :=
  CNF.rup_sound cl_28555 [cl_4583,cl_28523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4583 v h) (hints_cons _ _ _ (der_28523 v h) (by intro d hd; cases hd)))
def cl_28556 : CNF.NClause := [(35,false),(83,true),(4,true),(68,true),(73,false),(78,false),(87,true)]
theorem der_28556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28556 :=
  CNF.rup_sound cl_28556 [cl_4584,cl_28554] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4584 v h) (hints_cons _ _ _ (der_28554 v h) (by intro d hd; cases hd)))
def cl_28557 : CNF.NClause := [(35,false),(83,true),(4,false),(63,false),(68,false),(73,true),(78,false)]
theorem der_28557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28557 :=
  CNF.rup_sound cl_28557 [cl_4585,cl_28495] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4585 v h) (hints_cons _ _ _ (der_28495 v h) (by intro d hd; cases hd)))
def cl_28558 : CNF.NClause := [(35,false),(4,true),(68,false),(63,false),(73,true),(78,false),(87,true)]
theorem der_28558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28558 :=
  CNF.rup_sound cl_28558 [cl_4586,cl_28526] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4586 v h) (hints_cons _ _ _ (der_28526 v h) (by intro d hd; cases hd)))
def cl_28559 : CNF.NClause := [(35,false),(83,true),(4,false),(68,false),(63,true),(78,false),(73,true)]
theorem der_28559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28559 :=
  CNF.rup_sound cl_28559 [cl_4587,cl_28497] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4587 v h) (hints_cons _ _ _ (der_28497 v h) (by intro d hd; cases hd)))
def cl_28560 : CNF.NClause := [(35,false),(83,true),(63,true),(68,false),(73,true),(78,false),(87,true)]
theorem der_28560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28560 :=
  CNF.rup_sound cl_28560 [cl_4588,cl_28559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4588 v h) (hints_cons _ _ _ (der_28559 v h) (by intro d hd; cases hd)))
def cl_28561 : CNF.NClause := [(35,false),(83,true),(4,false),(68,true),(63,false),(73,true),(78,false)]
theorem der_28561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28561 :=
  CNF.rup_sound cl_28561 [cl_4589,cl_28499] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4589 v h) (hints_cons _ _ _ (der_28499 v h) (by intro d hd; cases hd)))
def cl_28562 : CNF.NClause := [(35,false),(83,true),(4,true),(68,true),(63,false),(78,false),(87,true)]
theorem der_28562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28562 :=
  CNF.rup_sound cl_28562 [cl_4590,cl_28556] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4590 v h) (hints_cons _ _ _ (der_28556 v h) (by intro d hd; cases hd)))
def cl_28563 : CNF.NClause := [(35,false),(83,true),(4,false),(63,true),(78,false),(73,true),(87,true)]
theorem der_28563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28563 :=
  CNF.rup_sound cl_28563 [cl_4591,cl_28559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4591 v h) (hints_cons _ _ _ (der_28559 v h) (by intro d hd; cases hd)))
def cl_28564 : CNF.NClause := [(35,false),(83,true),(4,true),(68,true),(63,true),(78,false),(87,true)]
theorem der_28564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28564 :=
  CNF.rup_sound cl_28564 [cl_4592,cl_28556] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4592 v h) (hints_cons _ _ _ (der_28556 v h) (by intro d hd; cases hd)))
def cl_28565 : CNF.NClause := [(35,false),(83,true),(4,false),(63,false),(73,false),(68,false),(87,true)]
theorem der_28565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28565 :=
  CNF.rup_sound cl_28565 [cl_4593,cl_28549] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4593 v h) (hints_cons _ _ _ (der_28549 v h) (by intro d hd; cases hd)))
def cl_28566 : CNF.NClause := [(35,false),(4,true),(68,false),(63,false),(73,false),(78,true),(87,true)]
theorem der_28566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28566 :=
  CNF.rup_sound cl_28566 [cl_4594,cl_28534] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4594 v h) (hints_cons _ _ _ (der_28534 v h) (by intro d hd; cases hd)))
def cl_28567 : CNF.NClause := [(35,false),(83,true),(4,false),(68,false),(63,true),(73,false),(78,true)]
theorem der_28567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28567 :=
  CNF.rup_sound cl_28567 [cl_4595,cl_28505] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4595 v h) (hints_cons _ _ _ (der_28505 v h) (by intro d hd; cases hd)))
def cl_28568 : CNF.NClause := [(35,false),(83,true),(4,true),(63,true),(68,false),(73,false),(78,true)]
theorem der_28568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28568 :=
  CNF.rup_sound cl_28568 [cl_4596,cl_28506] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4596 v h) (hints_cons _ _ _ (der_28506 v h) (by intro d hd; cases hd)))
def cl_28569 : CNF.NClause := [(35,false),(83,true),(4,false),(68,true),(63,false),(73,false),(87,true)]
theorem der_28569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28569 :=
  CNF.rup_sound cl_28569 [cl_4597,cl_28553] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4597 v h) (hints_cons _ _ _ (der_28553 v h) (by intro d hd; cases hd)))
def cl_28570 : CNF.NClause := [(35,false),(83,true),(4,true),(68,true),(63,false),(73,false),(87,true)]
theorem der_28570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28570 :=
  CNF.rup_sound cl_28570 [cl_4598,cl_28556] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4598 v h) (hints_cons _ _ _ (der_28556 v h) (by intro d hd; cases hd)))
def cl_28571 : CNF.NClause := [(35,false),(4,false),(68,true),(63,true),(73,false),(78,true),(87,true)]
theorem der_28571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28571 :=
  CNF.rup_sound cl_28571 [cl_4599,cl_28539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4599 v h) (hints_cons _ _ _ (der_28539 v h) (by intro d hd; cases hd)))
def cl_28572 : CNF.NClause := [(35,false),(78,true),(4,true),(68,true),(73,false),(63,true),(87,true)]
theorem der_28572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28572 :=
  CNF.rup_sound cl_28572 [cl_4600,cl_28540] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4600 v h) (hints_cons _ _ _ (der_28540 v h) (by intro d hd; cases hd)))
def cl_28573 : CNF.NClause := [(35,false),(78,true),(4,false),(63,false),(68,false),(73,true),(87,true)]
theorem der_28573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28573 :=
  CNF.rup_sound cl_28573 [cl_4601,cl_28541] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4601 v h) (hints_cons _ _ _ (der_28541 v h) (by intro d hd; cases hd)))
def cl_28574 : CNF.NClause := [(35,false),(78,true),(4,true),(68,false),(63,false),(73,true),(83,true)]
theorem der_28574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28574 :=
  CNF.rup_sound cl_28574 [cl_4602,cl_28512] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4602 v h) (hints_cons _ _ _ (der_28512 v h) (by intro d hd; cases hd)))
def cl_28575 : CNF.NClause := [(35,false),(78,true),(4,false),(68,false),(63,true),(73,true),(83,true)]
theorem der_28575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28575 :=
  CNF.rup_sound cl_28575 [cl_4603,cl_28513] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4603 v h) (hints_cons _ _ _ (der_28513 v h) (by intro d hd; cases hd)))
def cl_28576 : CNF.NClause := [(35,false),(78,true),(4,true),(63,true),(68,false),(83,true),(87,true)]
theorem der_28576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28576 :=
  CNF.rup_sound cl_28576 [cl_4604,cl_28568] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4604 v h) (hints_cons _ _ _ (der_28568 v h) (by intro d hd; cases hd)))
def cl_28577 : CNF.NClause := [(35,false),(78,true),(4,false),(68,true),(63,false),(73,true),(83,true)]
theorem der_28577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28577 :=
  CNF.rup_sound cl_28577 [cl_4605,cl_28515] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4605 v h) (hints_cons _ _ _ (der_28515 v h) (by intro d hd; cases hd)))
def cl_28578 : CNF.NClause := [(35,false),(78,true),(4,true),(68,true),(63,false),(73,true),(83,true)]
theorem der_28578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28578 :=
  CNF.rup_sound cl_28578 [cl_4606,cl_28516] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4606 v h) (hints_cons _ _ _ (der_28516 v h) (by intro d hd; cases hd)))
def cl_28579 : CNF.NClause := [(35,false),(4,false),(68,true),(63,true),(73,true),(83,true),(87,true)]
theorem der_28579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28579 :=
  CNF.rup_sound cl_28579 [cl_4607,cl_28563] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4607 v h) (hints_cons _ _ _ (der_28563 v h) (by intro d hd; cases hd)))
def cl_28580 : CNF.NClause := [(35,false),(78,true),(4,true),(68,true),(73,true),(83,true),(87,true)]
theorem der_28580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28580 :=
  CNF.rup_sound cl_28580 [cl_4608,cl_28578] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4608 v h) (hints_cons _ _ _ (der_28578 v h) (by intro d hd; cases hd)))
def cl_28581 : CNF.NClause := [(57,false),(71,false),(26,true),(79,false),(91,false),(75,false),(83,false)]
theorem der_28581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28581 :=
  CNF.rup_sound cl_28581 [cl_7298,cl_7300] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7298 v h) (hints_cons _ _ _ (inp_7300 v h) (by intro d hd; cases hd)))
def cl_28582 : CNF.NClause := [(57,false),(62,true),(83,false),(75,false),(91,false),(79,false),(71,false)]
theorem der_28582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28582 :=
  CNF.rup_sound cl_28582 [cl_7299,cl_26730] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7299 v h) (hints_cons _ _ _ (der_26730 v h) (by intro d hd; cases hd)))
def cl_28583 : CNF.NClause := [(57,false),(71,true),(79,false),(62,false),(83,false),(75,false),(91,false)]
theorem der_28583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28583 :=
  CNF.rup_sound cl_28583 [cl_7302,cl_7301] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7302 v h) (hints_cons _ _ _ (inp_7301 v h) (by intro d hd; cases hd)))
def cl_28584 : CNF.NClause := [(57,false),(26,false),(62,true),(91,false),(83,false),(75,false),(79,false)]
theorem der_28584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28584 :=
  CNF.rup_sound cl_28584 [cl_7303,cl_28582] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7303 v h) (hints_cons _ _ _ (der_28582 v h) (by intro d hd; cases hd)))
def cl_28585 : CNF.NClause := [(57,false),(26,true),(62,true),(83,false),(75,false),(91,false),(79,false)]
theorem der_28585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28585 :=
  CNF.rup_sound cl_28585 [cl_7304,cl_28582] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7304 v h) (hints_cons _ _ _ (der_28582 v h) (by intro d hd; cases hd)))
def cl_28586 : CNF.NClause := [(57,false),(75,true),(79,false),(71,false),(91,false),(62,false),(83,false)]
theorem der_28586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28586 :=
  CNF.rup_sound cl_28586 [cl_7306,cl_7305] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7306 v h) (hints_cons _ _ _ (inp_7305 v h) (by intro d hd; cases hd)))
def cl_28587 : CNF.NClause := [(57,false),(26,false),(83,false),(71,false),(91,false),(62,true),(79,false)]
theorem der_28587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28587 :=
  CNF.rup_sound cl_28587 [cl_7307,cl_28582] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7307 v h) (hints_cons _ _ _ (der_28582 v h) (by intro d hd; cases hd)))
def cl_28588 : CNF.NClause := [(57,false),(26,false),(71,true),(62,false),(79,false),(83,false),(91,false)]
theorem der_28588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28588 :=
  CNF.rup_sound cl_28588 [cl_7309,cl_28583] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7309 v h) (hints_cons _ _ _ (der_28583 v h) (by intro d hd; cases hd)))
def cl_28589 : CNF.NClause := [(57,false),(26,true),(71,true),(62,false),(79,false),(83,false),(91,false)]
theorem der_28589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28589 :=
  CNF.rup_sound cl_28589 [cl_7310,cl_28583] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7310 v h) (hints_cons _ _ _ (der_28583 v h) (by intro d hd; cases hd)))
def cl_28590 : CNF.NClause := [(57,false),(26,false),(62,true),(71,true),(79,false),(83,false),(91,false)]
theorem der_28590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28590 :=
  CNF.rup_sound cl_28590 [cl_7311,cl_28584] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7311 v h) (hints_cons _ _ _ (der_28584 v h) (by intro d hd; cases hd)))
def cl_28591 : CNF.NClause := [(57,false),(75,true),(62,true),(71,true),(79,false),(83,false),(91,false)]
theorem der_28591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28591 :=
  CNF.rup_sound cl_28591 [cl_7312,cl_28590] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7312 v h) (hints_cons _ _ _ (der_28590 v h) (by intro d hd; cases hd)))
def cl_28592 : CNF.NClause := [(57,false),(79,true),(83,false),(75,false),(71,false),(91,false),(62,false)]
theorem der_28592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28592 :=
  CNF.rup_sound cl_28592 [cl_7314,cl_7313] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7314 v h) (hints_cons _ _ _ (inp_7313 v h) (by intro d hd; cases hd)))
def cl_28593 : CNF.NClause := [(57,false),(26,false),(71,false),(75,false),(62,true),(83,false),(91,false)]
theorem der_28593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28593 :=
  CNF.rup_sound cl_28593 [cl_7315,cl_28582] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7315 v h) (hints_cons _ _ _ (der_28582 v h) (by intro d hd; cases hd)))
def cl_28594 : CNF.NClause := [(57,false),(26,false),(62,false),(71,true),(75,false),(83,false),(91,false)]
theorem der_28594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28594 :=
  CNF.rup_sound cl_28594 [cl_7317,cl_28583] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7317 v h) (hints_cons _ _ _ (der_28583 v h) (by intro d hd; cases hd)))
def cl_28595 : CNF.NClause := [(57,false),(26,true),(62,false),(71,true),(75,false),(83,false),(91,false)]
theorem der_28595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28595 :=
  CNF.rup_sound cl_28595 [cl_7318,cl_28583] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7318 v h) (hints_cons _ _ _ (der_28583 v h) (by intro d hd; cases hd)))
def cl_28596 : CNF.NClause := [(57,false),(79,true),(26,false),(71,true),(75,false),(83,false),(91,false)]
theorem der_28596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28596 :=
  CNF.rup_sound cl_28596 [cl_7319,cl_28594] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7319 v h) (hints_cons _ _ _ (der_28594 v h) (by intro d hd; cases hd)))
def cl_28597 : CNF.NClause := [(57,false),(79,true),(62,true),(75,false),(71,true),(83,false),(91,false)]
theorem der_28597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28597 :=
  CNF.rup_sound cl_28597 [cl_7320,cl_28596] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7320 v h) (hints_cons _ _ _ (der_28596 v h) (by intro d hd; cases hd)))
def cl_28598 : CNF.NClause := [(57,false),(26,false),(71,false),(62,false),(75,true),(83,false),(91,false)]
theorem der_28598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28598 :=
  CNF.rup_sound cl_28598 [cl_7321,cl_28586] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7321 v h) (hints_cons _ _ _ (der_28586 v h) (by intro d hd; cases hd)))
def cl_28599 : CNF.NClause := [(57,false),(26,true),(71,false),(62,false),(75,true),(83,false),(91,false)]
theorem der_28599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28599 :=
  CNF.rup_sound cl_28599 [cl_7322,cl_28586] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7322 v h) (hints_cons _ _ _ (der_28586 v h) (by intro d hd; cases hd)))
def cl_28600 : CNF.NClause := [(57,false),(26,false),(71,false),(62,true),(75,true),(83,false),(91,false)]
theorem der_28600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28600 :=
  CNF.rup_sound cl_28600 [cl_7323,cl_28587] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7323 v h) (hints_cons _ _ _ (der_28587 v h) (by intro d hd; cases hd)))
def cl_28601 : CNF.NClause := [(57,false),(79,true),(26,false),(71,true),(62,false),(83,false),(91,false)]
theorem der_28601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28601 :=
  CNF.rup_sound cl_28601 [cl_7325,cl_28594] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7325 v h) (hints_cons _ _ _ (der_28594 v h) (by intro d hd; cases hd)))
def cl_28602 : CNF.NClause := [(57,false),(79,true),(71,true),(62,false),(75,true),(83,false),(91,false)]
theorem der_28602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28602 :=
  CNF.rup_sound cl_28602 [cl_7326,cl_28601] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7326 v h) (hints_cons _ _ _ (der_28601 v h) (by intro d hd; cases hd)))
def cl_28604 : CNF.NClause := [(57,false),(75,true),(26,true),(62,true),(71,true),(83,false),(91,false)]
theorem der_28604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28604 :=
  CNF.rup_sound cl_28604 [cl_7328,cl_28591] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7328 v h) (hints_cons _ _ _ (der_28591 v h) (by intro d hd; cases hd)))
def cl_28605 : CNF.NClause := [(57,false),(83,true),(71,false),(75,false),(79,false),(62,false),(91,false)]
theorem der_28605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28605 :=
  CNF.rup_sound cl_28605 [cl_7330,cl_7329] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7330 v h) (hints_cons _ _ _ (inp_7329 v h) (by intro d hd; cases hd)))
def cl_28606 : CNF.NClause := [(57,false),(26,false),(71,false),(75,false),(79,false),(62,true),(91,false)]
theorem der_28606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28606 :=
  CNF.rup_sound cl_28606 [cl_7331,cl_28582] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7331 v h) (hints_cons _ _ _ (der_28582 v h) (by intro d hd; cases hd)))
def cl_28607 : CNF.NClause := [(57,false),(26,false),(71,true),(75,false),(79,false),(62,false),(91,false)]
theorem der_28607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28607 :=
  CNF.rup_sound cl_28607 [cl_7333,cl_28583] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7333 v h) (hints_cons _ _ _ (der_28583 v h) (by intro d hd; cases hd)))
def cl_28608 : CNF.NClause := [(57,false),(26,true),(71,true),(75,false),(79,false),(62,false),(91,false)]
theorem der_28608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28608 :=
  CNF.rup_sound cl_28608 [cl_7334,cl_28583] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7334 v h) (hints_cons _ _ _ (der_28583 v h) (by intro d hd; cases hd)))
def cl_28609 : CNF.NClause := [(57,false),(26,false),(62,true),(71,true),(79,false),(75,false),(91,false)]
theorem der_28609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28609 :=
  CNF.rup_sound cl_28609 [cl_7335,cl_28584] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7335 v h) (hints_cons _ _ _ (der_28584 v h) (by intro d hd; cases hd)))
def cl_28610 : CNF.NClause := [(57,false),(83,true),(62,true),(75,false),(71,true),(79,false),(91,false)]
theorem der_28610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28610 :=
  CNF.rup_sound cl_28610 [cl_7336,cl_28609] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7336 v h) (hints_cons _ _ _ (der_28609 v h) (by intro d hd; cases hd)))
def cl_28612 : CNF.NClause := [(57,false),(26,true),(71,false),(62,false),(79,false),(75,true),(91,false)]
theorem der_28612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28612 :=
  CNF.rup_sound cl_28612 [cl_7338,cl_28586] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7338 v h) (hints_cons _ _ _ (der_28586 v h) (by intro d hd; cases hd)))
def cl_28613 : CNF.NClause := [(57,false),(26,false),(71,false),(62,true),(75,true),(79,false),(91,false)]
theorem der_28613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28613 :=
  CNF.rup_sound cl_28613 [cl_7339,cl_28600] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7339 v h) (hints_cons _ _ _ (der_28600 v h) (by intro d hd; cases hd)))
def cl_28614 : CNF.NClause := [(57,false),(26,false),(71,true),(62,false),(79,false),(75,true),(91,false)]
theorem der_28614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28614 :=
  CNF.rup_sound cl_28614 [cl_7341,cl_28588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7341 v h) (hints_cons _ _ _ (der_28588 v h) (by intro d hd; cases hd)))
def cl_28615 : CNF.NClause := [(57,false),(83,true),(71,true),(62,false),(79,false),(75,true),(91,false)]
theorem der_28615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28615 :=
  CNF.rup_sound cl_28615 [cl_7342,cl_28614] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7342 v h) (hints_cons _ _ _ (der_28614 v h) (by intro d hd; cases hd)))
def cl_28616 : CNF.NClause := [(57,false),(75,true),(26,false),(62,true),(71,true),(79,false),(91,false)]
theorem der_28616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28616 :=
  CNF.rup_sound cl_28616 [cl_7343,cl_28591] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7343 v h) (hints_cons _ _ _ (der_28591 v h) (by intro d hd; cases hd)))
def cl_28617 : CNF.NClause := [(57,false),(75,true),(26,true),(62,true),(71,true),(79,false),(91,false)]
theorem der_28617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28617 :=
  CNF.rup_sound cl_28617 [cl_7344,cl_28591] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7344 v h) (hints_cons _ _ _ (der_28591 v h) (by intro d hd; cases hd)))
def cl_28618 : CNF.NClause := [(57,false),(26,false),(71,false),(75,false),(79,true),(62,false),(91,false)]
theorem der_28618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28618 :=
  CNF.rup_sound cl_28618 [cl_7345,cl_28592] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7345 v h) (hints_cons _ _ _ (der_28592 v h) (by intro d hd; cases hd)))
def cl_28619 : CNF.NClause := [(57,false),(26,true),(71,false),(75,false),(79,true),(62,false),(91,false)]
theorem der_28619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28619 :=
  CNF.rup_sound cl_28619 [cl_7346,cl_28592] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7346 v h) (hints_cons _ _ _ (der_28592 v h) (by intro d hd; cases hd)))
def cl_28620 : CNF.NClause := [(57,false),(79,true),(26,false),(71,false),(75,false),(62,true),(91,false)]
theorem der_28620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28620 :=
  CNF.rup_sound cl_28620 [cl_7347,cl_28593] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7347 v h) (hints_cons _ _ _ (der_28593 v h) (by intro d hd; cases hd)))
def cl_28621 : CNF.NClause := [(57,false),(26,false),(71,true),(75,false),(79,true),(62,false),(91,false)]
theorem der_28621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28621 :=
  CNF.rup_sound cl_28621 [cl_7349,cl_28594] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7349 v h) (hints_cons _ _ _ (der_28594 v h) (by intro d hd; cases hd)))
def cl_28622 : CNF.NClause := [(57,false),(83,true),(71,true),(75,false),(79,true),(62,false),(91,false)]
theorem der_28622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28622 :=
  CNF.rup_sound cl_28622 [cl_7350,cl_28621] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7350 v h) (hints_cons _ _ _ (der_28621 v h) (by intro d hd; cases hd)))
def cl_28623 : CNF.NClause := [(57,false),(79,true),(26,false),(62,true),(71,true),(75,false),(91,false)]
theorem der_28623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28623 :=
  CNF.rup_sound cl_28623 [cl_7351,cl_28597] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7351 v h) (hints_cons _ _ _ (der_28597 v h) (by intro d hd; cases hd)))
def cl_28624 : CNF.NClause := [(57,false),(79,true),(26,true),(62,true),(75,false),(71,true),(91,false)]
theorem der_28624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28624 :=
  CNF.rup_sound cl_28624 [cl_7352,cl_28597] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7352 v h) (hints_cons _ _ _ (der_28597 v h) (by intro d hd; cases hd)))
def cl_28625 : CNF.NClause := [(57,false),(79,true),(26,false),(71,false),(62,false),(75,true),(91,false)]
theorem der_28625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28625 :=
  CNF.rup_sound cl_28625 [cl_7353,cl_28598] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7353 v h) (hints_cons _ _ _ (der_28598 v h) (by intro d hd; cases hd)))
def cl_28626 : CNF.NClause := [(57,false),(79,true),(26,true),(71,false),(62,false),(75,true),(91,false)]
theorem der_28626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28626 :=
  CNF.rup_sound cl_28626 [cl_7354,cl_28599] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7354 v h) (hints_cons _ _ _ (der_28599 v h) (by intro d hd; cases hd)))
def cl_28627 : CNF.NClause := [(57,false),(79,true),(26,false),(71,false),(62,true),(75,true),(91,false)]
theorem der_28627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28627 :=
  CNF.rup_sound cl_28627 [cl_7355,cl_28600] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7355 v h) (hints_cons _ _ _ (der_28600 v h) (by intro d hd; cases hd)))
def cl_28628 : CNF.NClause := [(57,false),(79,true),(26,false),(71,true),(62,false),(75,true),(91,false)]
theorem der_28628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28628 :=
  CNF.rup_sound cl_28628 [cl_7357,cl_28602] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7357 v h) (hints_cons _ _ _ (der_28602 v h) (by intro d hd; cases hd)))
def cl_28629 : CNF.NClause := [(57,false),(79,true),(26,true),(71,true),(62,false),(75,true),(91,false)]
theorem der_28629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28629 :=
  CNF.rup_sound cl_28629 [cl_7358,cl_28602] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7358 v h) (hints_cons _ _ _ (der_28602 v h) (by intro d hd; cases hd)))
def cl_28630 : CNF.NClause := [(57,false),(75,true),(26,false),(71,true),(79,true),(83,true),(91,false)]
theorem der_28630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28630 :=
  CNF.rup_sound cl_28630 [cl_7359,cl_28628] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7359 v h) (hints_cons _ _ _ (der_28628 v h) (by intro d hd; cases hd)))
def cl_28631 : CNF.NClause := [(57,false),(75,true),(62,true),(71,true),(79,true),(83,true),(91,false)]
theorem der_28631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28631 :=
  CNF.rup_sound cl_28631 [cl_7360,cl_28630] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7360 v h) (hints_cons _ _ _ (der_28630 v h) (by intro d hd; cases hd)))
def cl_28632 : CNF.NClause := [(57,false),(71,false),(26,true),(75,false),(79,false),(83,false),(91,true)]
theorem der_28632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28632 :=
  CNF.rup_sound cl_28632 [cl_7362,cl_26737] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7362 v h) (hints_cons _ _ _ (der_26737 v h) (by intro d hd; cases hd)))
def cl_28633 : CNF.NClause := [(57,false),(62,true),(26,false),(79,false),(75,false),(71,false),(83,false)]
theorem der_28633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28633 :=
  CNF.rup_sound cl_28633 [cl_7363,cl_28582] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7363 v h) (hints_cons _ _ _ (der_28582 v h) (by intro d hd; cases hd)))
def cl_28634 : CNF.NClause := [(57,false),(71,true),(26,false),(79,false),(75,false),(83,false),(62,false)]
theorem der_28634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28634 :=
  CNF.rup_sound cl_28634 [cl_7365,cl_28583] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7365 v h) (hints_cons _ _ _ (der_28583 v h) (by intro d hd; cases hd)))
def cl_28635 : CNF.NClause := [(57,false),(71,true),(26,true),(62,false),(79,false),(75,false),(83,false)]
theorem der_28635 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28635 :=
  CNF.rup_sound cl_28635 [cl_7366,cl_28583] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7366 v h) (hints_cons _ _ _ (der_28583 v h) (by intro d hd; cases hd)))
def cl_28636 : CNF.NClause := [(57,false),(26,false),(62,true),(79,false),(71,true),(83,false),(75,false)]
theorem der_28636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28636 :=
  CNF.rup_sound cl_28636 [cl_7367,cl_28609] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7367 v h) (hints_cons _ _ _ (der_28609 v h) (by intro d hd; cases hd)))
def cl_28637 : CNF.NClause := [(57,false),(26,true),(91,true),(75,false),(62,true),(79,false),(83,false)]
theorem der_28637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28637 :=
  CNF.rup_sound cl_28637 [cl_7368,cl_26737] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7368 v h) (hints_cons _ _ _ (der_26737 v h) (by intro d hd; cases hd)))
def cl_28638 : CNF.NClause := [(57,false),(62,false),(26,false),(71,false),(79,false),(83,false),(75,true)]
theorem der_28638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28638 :=
  CNF.rup_sound cl_28638 [cl_7369,cl_28586] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7369 v h) (hints_cons _ _ _ (der_28586 v h) (by intro d hd; cases hd)))
def cl_28639 : CNF.NClause := [(57,false),(75,true),(26,true),(71,false),(62,false),(79,false),(83,false)]
theorem der_28639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28639 :=
  CNF.rup_sound cl_28639 [cl_7370,cl_28586] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7370 v h) (hints_cons _ _ _ (der_28586 v h) (by intro d hd; cases hd)))
def cl_28640 : CNF.NClause := [(57,false),(75,true),(26,false),(62,true),(79,false),(83,false),(71,false)]
theorem der_28640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28640 :=
  CNF.rup_sound cl_28640 [cl_7371,cl_28600] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7371 v h) (hints_cons _ _ _ (der_28600 v h) (by intro d hd; cases hd)))
def cl_28641 : CNF.NClause := [(57,false),(75,true),(26,false),(71,true),(62,false),(79,false),(83,false)]
theorem der_28641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28641 :=
  CNF.rup_sound cl_28641 [cl_7373,cl_28614] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7373 v h) (hints_cons _ _ _ (der_28614 v h) (by intro d hd; cases hd)))
def cl_28642 : CNF.NClause := [(57,false),(75,true),(71,true),(62,false),(79,false),(83,false),(91,true)]
theorem der_28642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28642 :=
  CNF.rup_sound cl_28642 [cl_7374,cl_28641] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7374 v h) (hints_cons _ _ _ (der_28641 v h) (by intro d hd; cases hd)))
def cl_28643 : CNF.NClause := [(57,false),(75,true),(26,false),(62,true),(71,true),(79,false),(83,false)]
theorem der_28643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28643 :=
  CNF.rup_sound cl_28643 [cl_7375,cl_28591] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7375 v h) (hints_cons _ _ _ (der_28591 v h) (by intro d hd; cases hd)))
def cl_28644 : CNF.NClause := [(57,false),(75,true),(26,true),(62,true),(71,true),(79,false),(83,false)]
theorem der_28644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28644 :=
  CNF.rup_sound cl_28644 [cl_7376,cl_28591] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7376 v h) (hints_cons _ _ _ (der_28591 v h) (by intro d hd; cases hd)))
def cl_28645 : CNF.NClause := [(57,false),(79,true),(26,false),(71,false),(75,false),(83,false),(62,false)]
theorem der_28645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28645 :=
  CNF.rup_sound cl_28645 [cl_7377,cl_28592] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7377 v h) (hints_cons _ _ _ (der_28592 v h) (by intro d hd; cases hd)))
def cl_28646 : CNF.NClause := [(57,false),(79,true),(26,true),(75,false),(71,false),(83,false),(62,false)]
theorem der_28646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28646 :=
  CNF.rup_sound cl_28646 [cl_7378,cl_28592] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7378 v h) (hints_cons _ _ _ (der_28592 v h) (by intro d hd; cases hd)))
def cl_28647 : CNF.NClause := [(57,false),(26,false),(71,false),(75,false),(62,true),(83,false),(91,true)]
theorem der_28647 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28647 :=
  CNF.rup_sound cl_28647 [cl_7379,cl_28633] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7379 v h) (hints_cons _ _ _ (der_28633 v h) (by intro d hd; cases hd)))
def cl_28648 : CNF.NClause := [(57,false),(79,true),(26,false),(71,true),(75,false),(83,false),(62,false)]
theorem der_28648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28648 :=
  CNF.rup_sound cl_28648 [cl_7381,cl_28594] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7381 v h) (hints_cons _ _ _ (der_28594 v h) (by intro d hd; cases hd)))
def cl_28649 : CNF.NClause := [(57,false),(79,true),(71,true),(91,true),(75,false),(83,false),(62,false)]
theorem der_28649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28649 :=
  CNF.rup_sound cl_28649 [cl_7382,cl_28648] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7382 v h) (hints_cons _ _ _ (der_28648 v h) (by intro d hd; cases hd)))
def cl_28650 : CNF.NClause := [(57,false),(79,true),(26,false),(62,true),(71,true),(75,false),(83,false)]
theorem der_28650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28650 :=
  CNF.rup_sound cl_28650 [cl_7383,cl_28597] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7383 v h) (hints_cons _ _ _ (der_28597 v h) (by intro d hd; cases hd)))
def cl_28651 : CNF.NClause := [(57,false),(79,true),(26,true),(62,true),(75,false),(71,true),(83,false)]
theorem der_28651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28651 :=
  CNF.rup_sound cl_28651 [cl_7384,cl_28597] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7384 v h) (hints_cons _ _ _ (der_28597 v h) (by intro d hd; cases hd)))
def cl_28652 : CNF.NClause := [(57,false),(79,true),(26,false),(71,false),(62,false),(75,true),(83,false)]
theorem der_28652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28652 :=
  CNF.rup_sound cl_28652 [cl_7385,cl_28598] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7385 v h) (hints_cons _ _ _ (der_28598 v h) (by intro d hd; cases hd)))
def cl_28653 : CNF.NClause := [(57,false),(79,true),(26,true),(71,false),(62,false),(75,true),(83,false)]
theorem der_28653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28653 :=
  CNF.rup_sound cl_28653 [cl_7386,cl_28599] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7386 v h) (hints_cons _ _ _ (der_28599 v h) (by intro d hd; cases hd)))
def cl_28654 : CNF.NClause := [(57,false),(79,true),(26,false),(71,false),(62,true),(75,true),(83,false)]
theorem der_28654 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28654 :=
  CNF.rup_sound cl_28654 [cl_7387,cl_28600] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7387 v h) (hints_cons _ _ _ (der_28600 v h) (by intro d hd; cases hd)))
def cl_28655 : CNF.NClause := [(57,false),(79,true),(26,false),(71,true),(62,false),(75,true),(83,false)]
theorem der_28655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28655 :=
  CNF.rup_sound cl_28655 [cl_7389,cl_28602] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7389 v h) (hints_cons _ _ _ (der_28602 v h) (by intro d hd; cases hd)))
def cl_28656 : CNF.NClause := [(57,false),(79,true),(26,true),(71,true),(62,false),(75,true),(83,false)]
theorem der_28656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28656 :=
  CNF.rup_sound cl_28656 [cl_7390,cl_28602] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7390 v h) (hints_cons _ _ _ (der_28602 v h) (by intro d hd; cases hd)))
def cl_28658 : CNF.NClause := [(57,false),(75,true),(26,true),(62,true),(71,true),(79,true),(83,false)]
theorem der_28658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28658 :=
  CNF.rup_sound cl_28658 [cl_7392,cl_28604] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7392 v h) (hints_cons _ _ _ (der_28604 v h) (by intro d hd; cases hd)))
def cl_28659 : CNF.NClause := [(57,false),(83,true),(26,false),(71,false),(75,false),(79,false),(62,false)]
theorem der_28659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28659 :=
  CNF.rup_sound cl_28659 [cl_7393,cl_7329] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7393 v h) (hints_cons _ _ _ (inp_7329 v h) (by intro d hd; cases hd)))
def cl_28660 : CNF.NClause := [(57,false),(83,true),(26,true),(71,false),(62,false),(79,false),(75,false)]
theorem der_28660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28660 :=
  CNF.rup_sound cl_28660 [cl_7394,cl_28605] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7394 v h) (hints_cons _ _ _ (der_28605 v h) (by intro d hd; cases hd)))
def cl_28661 : CNF.NClause := [(57,false),(26,false),(71,false),(75,false),(79,false),(62,true),(91,true)]
theorem der_28661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28661 :=
  CNF.rup_sound cl_28661 [cl_7395,cl_28633] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7395 v h) (hints_cons _ _ _ (der_28633 v h) (by intro d hd; cases hd)))
def cl_28662 : CNF.NClause := [(57,false),(83,true),(26,false),(71,true),(75,false),(79,false),(62,false)]
theorem der_28662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28662 :=
  CNF.rup_sound cl_28662 [cl_7397,cl_28607] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7397 v h) (hints_cons _ _ _ (der_28607 v h) (by intro d hd; cases hd)))
def cl_28663 : CNF.NClause := [(57,false),(83,true),(26,true),(71,true),(75,false),(79,false),(62,false)]
theorem der_28663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28663 :=
  CNF.rup_sound cl_28663 [cl_7398,cl_28608] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7398 v h) (hints_cons _ _ _ (der_28608 v h) (by intro d hd; cases hd)))
def cl_28664 : CNF.NClause := [(57,false),(83,true),(26,false),(62,true),(71,true),(79,false),(75,false)]
theorem der_28664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28664 :=
  CNF.rup_sound cl_28664 [cl_7399,cl_28609] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7399 v h) (hints_cons _ _ _ (der_28609 v h) (by intro d hd; cases hd)))
def cl_28665 : CNF.NClause := [(57,false),(83,true),(26,true),(62,true),(75,false),(71,true),(79,false)]
theorem der_28665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28665 :=
  CNF.rup_sound cl_28665 [cl_7400,cl_28610] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7400 v h) (hints_cons _ _ _ (der_28610 v h) (by intro d hd; cases hd)))
def cl_28667 : CNF.NClause := [(57,false),(83,true),(26,true),(71,false),(62,false),(79,false),(75,true)]
theorem der_28667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28667 :=
  CNF.rup_sound cl_28667 [cl_7402,cl_28612] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7402 v h) (hints_cons _ _ _ (der_28612 v h) (by intro d hd; cases hd)))
def cl_28668 : CNF.NClause := [(57,false),(26,false),(71,false),(62,true),(75,true),(79,false),(91,true)]
theorem der_28668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28668 :=
  CNF.rup_sound cl_28668 [cl_7403,cl_28640] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7403 v h) (hints_cons _ _ _ (der_28640 v h) (by intro d hd; cases hd)))
def cl_28670 : CNF.NClause := [(57,false),(83,true),(26,true),(71,true),(62,false),(79,false),(91,true)]
theorem der_28670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28670 :=
  CNF.rup_sound cl_28670 [cl_7406,cl_28663] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7406 v h) (hints_cons _ _ _ (der_28663 v h) (by intro d hd; cases hd)))
def cl_28672 : CNF.NClause := [(57,false),(75,true),(26,true),(62,true),(71,true),(79,false),(83,true)]
theorem der_28672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28672 :=
  CNF.rup_sound cl_28672 [cl_7408,cl_28617] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7408 v h) (hints_cons _ _ _ (der_28617 v h) (by intro d hd; cases hd)))
def cl_28673 : CNF.NClause := [(57,false),(83,true),(26,false),(71,false),(75,false),(79,true),(62,false)]
theorem der_28673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28673 :=
  CNF.rup_sound cl_28673 [cl_7409,cl_28618] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7409 v h) (hints_cons _ _ _ (der_28618 v h) (by intro d hd; cases hd)))
def cl_28674 : CNF.NClause := [(57,false),(83,true),(26,true),(71,false),(62,false),(79,true),(75,false)]
theorem der_28674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28674 :=
  CNF.rup_sound cl_28674 [cl_7410,cl_28619] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7410 v h) (hints_cons _ _ _ (der_28619 v h) (by intro d hd; cases hd)))
def cl_28675 : CNF.NClause := [(57,false),(79,true),(26,false),(71,false),(75,false),(62,true),(91,true)]
theorem der_28675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28675 :=
  CNF.rup_sound cl_28675 [cl_7411,cl_28647] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7411 v h) (hints_cons _ _ _ (der_28647 v h) (by intro d hd; cases hd)))
def cl_28676 : CNF.NClause := [(57,false),(83,true),(26,false),(71,true),(75,false),(79,true),(62,false)]
theorem der_28676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28676 :=
  CNF.rup_sound cl_28676 [cl_7413,cl_28621] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7413 v h) (hints_cons _ _ _ (der_28621 v h) (by intro d hd; cases hd)))
def cl_28677 : CNF.NClause := [(57,false),(83,true),(26,true),(71,true),(75,false),(62,false),(91,true)]
theorem der_28677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28677 :=
  CNF.rup_sound cl_28677 [cl_7414,cl_28663] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7414 v h) (hints_cons _ _ _ (der_28663 v h) (by intro d hd; cases hd)))
def cl_28680 : CNF.NClause := [(57,false),(79,true),(26,false),(71,false),(62,false),(75,true),(83,true)]
theorem der_28680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28680 :=
  CNF.rup_sound cl_28680 [cl_7417,cl_28625] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7417 v h) (hints_cons _ _ _ (der_28625 v h) (by intro d hd; cases hd)))
def cl_28681 : CNF.NClause := [(57,false),(79,true),(26,true),(71,false),(62,false),(83,true),(91,true)]
theorem der_28681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28681 :=
  CNF.rup_sound cl_28681 [cl_7418,cl_28674] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7418 v h) (hints_cons _ _ _ (der_28674 v h) (by intro d hd; cases hd)))
def cl_28682 : CNF.NClause := [(57,false),(79,true),(26,false),(71,false),(62,true),(75,true),(91,true)]
theorem der_28682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28682 :=
  CNF.rup_sound cl_28682 [cl_7419,cl_28654] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7419 v h) (hints_cons _ _ _ (der_28654 v h) (by intro d hd; cases hd)))
def cl_28684 : CNF.NClause := [(57,false),(26,true),(71,true),(62,false),(75,true),(83,true),(91,true)]
theorem der_28684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28684 :=
  CNF.rup_sound cl_28684 [cl_7422,cl_28670] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7422 v h) (hints_cons _ _ _ (der_28670 v h) (by intro d hd; cases hd)))
def cl_28686 : CNF.NClause := [(57,false),(75,true),(26,true),(62,true),(71,true),(83,true),(91,true)]
theorem der_28686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28686 :=
  CNF.rup_sound cl_28686 [cl_7424,cl_28672] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7424 v h) (hints_cons _ _ _ (der_28672 v h) (by intro d hd; cases hd)))
def cl_28687 : CNF.NClause := [(51,false),(67,true),(70,false),(71,false),(69,false),(92,false),(68,false)]
theorem der_28687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28687 :=
  CNF.rup_sound cl_28687 [cl_6532,cl_6531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6532 v h) (hints_cons _ _ _ (inp_6531 v h) (by intro d hd; cases hd)))
def cl_28688 : CNF.NClause := [(51,false),(68,true),(67,false),(71,false),(70,false),(92,false),(69,false)]
theorem der_28688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28688 :=
  CNF.rup_sound cl_28688 [cl_6534,cl_6533] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6534 v h) (hints_cons _ _ _ (inp_6533 v h) (by intro d hd; cases hd)))
def cl_28689 : CNF.NClause := [(51,false),(20,false),(67,true),(69,false),(70,false),(71,false),(92,false)]
theorem der_28689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28689 :=
  CNF.rup_sound cl_28689 [cl_6535,cl_28687] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6535 v h) (hints_cons _ _ _ (der_28687 v h) (by intro d hd; cases hd)))
def cl_28690 : CNF.NClause := [(51,false),(20,true),(67,true),(69,false),(70,false),(71,false),(92,false)]
theorem der_28690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28690 :=
  CNF.rup_sound cl_28690 [cl_6536,cl_28687] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6536 v h) (hints_cons _ _ _ (der_28687 v h) (by intro d hd; cases hd)))
def cl_28691 : CNF.NClause := [(51,false),(69,true),(67,false),(68,false),(70,false),(71,false),(92,false)]
theorem der_28691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28691 :=
  CNF.rup_sound cl_28691 [cl_6538,cl_6537] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6538 v h) (hints_cons _ _ _ (inp_6537 v h) (by intro d hd; cases hd)))
def cl_28692 : CNF.NClause := [(51,false),(20,false),(68,false),(67,true),(70,false),(71,false),(92,false)]
theorem der_28692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28692 :=
  CNF.rup_sound cl_28692 [cl_6539,cl_28687] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6539 v h) (hints_cons _ _ _ (der_28687 v h) (by intro d hd; cases hd)))
def cl_28693 : CNF.NClause := [(51,false),(20,true),(68,false),(67,true),(70,false),(71,false),(92,false)]
theorem der_28693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28693 :=
  CNF.rup_sound cl_28693 [cl_6540,cl_28687] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6540 v h) (hints_cons _ _ _ (der_28687 v h) (by intro d hd; cases hd)))
def cl_28694 : CNF.NClause := [(51,false),(20,false),(68,true),(67,false),(70,false),(71,false),(92,false)]
theorem der_28694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28694 :=
  CNF.rup_sound cl_28694 [cl_6541,cl_28688] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6541 v h) (hints_cons _ _ _ (der_28688 v h) (by intro d hd; cases hd)))
def cl_28695 : CNF.NClause := [(51,false),(20,true),(68,true),(67,false),(70,false),(71,false),(92,false)]
theorem der_28695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28695 :=
  CNF.rup_sound cl_28695 [cl_6542,cl_28688] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6542 v h) (hints_cons _ _ _ (der_28688 v h) (by intro d hd; cases hd)))
def cl_28696 : CNF.NClause := [(51,false),(68,true),(20,false),(69,true),(70,false),(71,false),(92,false)]
theorem der_28696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28696 :=
  CNF.rup_sound cl_28696 [cl_6543,cl_28694] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6543 v h) (hints_cons _ _ _ (der_28694 v h) (by intro d hd; cases hd)))
def cl_28697 : CNF.NClause := [(51,false),(68,true),(67,true),(69,true),(70,false),(71,false),(92,false)]
theorem der_28697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28697 :=
  CNF.rup_sound cl_28697 [cl_6544,cl_28696] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6544 v h) (hints_cons _ _ _ (der_28696 v h) (by intro d hd; cases hd)))
def cl_28698 : CNF.NClause := [(51,false),(68,false),(92,false),(67,false),(69,false),(71,false),(70,true)]
theorem der_28698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28698 :=
  CNF.rup_sound cl_28698 [cl_6546,cl_6545] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6546 v h) (hints_cons _ _ _ (inp_6545 v h) (by intro d hd; cases hd)))
def cl_28699 : CNF.NClause := [(51,false),(20,false),(68,false),(69,false),(67,true),(71,false),(92,false)]
theorem der_28699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28699 :=
  CNF.rup_sound cl_28699 [cl_6547,cl_28687] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6547 v h) (hints_cons _ _ _ (der_28687 v h) (by intro d hd; cases hd)))
def cl_28700 : CNF.NClause := [(51,false),(20,true),(68,false),(69,false),(67,true),(71,false),(92,false)]
theorem der_28700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28700 :=
  CNF.rup_sound cl_28700 [cl_6548,cl_28687] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6548 v h) (hints_cons _ _ _ (der_28687 v h) (by intro d hd; cases hd)))
def cl_28701 : CNF.NClause := [(51,false),(68,true),(20,false),(71,false),(69,false),(67,false),(92,false)]
theorem der_28701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28701 :=
  CNF.rup_sound cl_28701 [cl_6549,cl_28688] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6549 v h) (hints_cons _ _ _ (der_28688 v h) (by intro d hd; cases hd)))
def cl_28702 : CNF.NClause := [(51,false),(68,true),(20,true),(92,false),(67,false),(69,false),(71,false)]
theorem der_28702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28702 :=
  CNF.rup_sound cl_28702 [cl_6550,cl_28688] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6550 v h) (hints_cons _ _ _ (der_28688 v h) (by intro d hd; cases hd)))
def cl_28703 : CNF.NClause := [(51,false),(68,true),(20,false),(69,false),(70,true),(71,false),(92,false)]
theorem der_28703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28703 :=
  CNF.rup_sound cl_28703 [cl_6551,cl_28701] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6551 v h) (hints_cons _ _ _ (der_28701 v h) (by intro d hd; cases hd)))
def cl_28704 : CNF.NClause := [(51,false),(68,true),(67,true),(69,false),(70,true),(71,false),(92,false)]
theorem der_28704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28704 :=
  CNF.rup_sound cl_28704 [cl_6552,cl_28703] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6552 v h) (hints_cons _ _ _ (der_28703 v h) (by intro d hd; cases hd)))
def cl_28705 : CNF.NClause := [(51,false),(69,true),(20,false),(68,false),(67,false),(71,false),(92,false)]
theorem der_28705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28705 :=
  CNF.rup_sound cl_28705 [cl_6553,cl_28691] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6553 v h) (hints_cons _ _ _ (der_28691 v h) (by intro d hd; cases hd)))
def cl_28706 : CNF.NClause := [(51,false),(69,true),(20,true),(67,false),(68,false),(71,false),(92,false)]
theorem der_28706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28706 :=
  CNF.rup_sound cl_28706 [cl_6554,cl_28691] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6554 v h) (hints_cons _ _ _ (der_28691 v h) (by intro d hd; cases hd)))
def cl_28707 : CNF.NClause := [(51,false),(69,true),(20,false),(68,false),(67,true),(71,false),(92,false)]
theorem der_28707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28707 :=
  CNF.rup_sound cl_28707 [cl_6555,cl_28692] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6555 v h) (hints_cons _ _ _ (der_28692 v h) (by intro d hd; cases hd)))
def cl_28708 : CNF.NClause := [(51,false),(69,true),(68,false),(67,true),(70,true),(71,false),(92,false)]
theorem der_28708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28708 :=
  CNF.rup_sound cl_28708 [cl_6556,cl_28707] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6556 v h) (hints_cons _ _ _ (der_28707 v h) (by intro d hd; cases hd)))
def cl_28709 : CNF.NClause := [(51,false),(69,true),(20,false),(68,true),(67,false),(71,false),(92,false)]
theorem der_28709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28709 :=
  CNF.rup_sound cl_28709 [cl_6557,cl_28694] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6557 v h) (hints_cons _ _ _ (der_28694 v h) (by intro d hd; cases hd)))
def cl_28710 : CNF.NClause := [(51,false),(69,true),(68,true),(67,false),(70,true),(71,false),(92,false)]
theorem der_28710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28710 :=
  CNF.rup_sound cl_28710 [cl_6558,cl_28709] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6558 v h) (hints_cons _ _ _ (der_28709 v h) (by intro d hd; cases hd)))
def cl_28711 : CNF.NClause := [(51,false),(68,true),(20,false),(67,true),(69,true),(71,false),(92,false)]
theorem der_28711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28711 :=
  CNF.rup_sound cl_28711 [cl_6559,cl_28697] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6559 v h) (hints_cons _ _ _ (der_28697 v h) (by intro d hd; cases hd)))
def cl_28712 : CNF.NClause := [(51,false),(68,true),(20,true),(67,true),(69,true),(71,false),(92,false)]
theorem der_28712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28712 :=
  CNF.rup_sound cl_28712 [cl_6560,cl_28697] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6560 v h) (hints_cons _ _ _ (der_28697 v h) (by intro d hd; cases hd)))
def cl_28713 : CNF.NClause := [(51,false),(68,false),(70,false),(71,true),(67,false),(92,false),(69,false)]
theorem der_28713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28713 :=
  CNF.rup_sound cl_28713 [cl_6562,cl_6561] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6562 v h) (hints_cons _ _ _ (inp_6561 v h) (by intro d hd; cases hd)))
def cl_28714 : CNF.NClause := [(51,false),(67,true),(20,false),(92,false),(69,false),(68,false),(70,false)]
theorem der_28714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28714 :=
  CNF.rup_sound cl_28714 [cl_6563,cl_28687] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6563 v h) (hints_cons _ _ _ (der_28687 v h) (by intro d hd; cases hd)))
def cl_28715 : CNF.NClause := [(51,false),(20,true),(67,true),(92,false),(69,false),(70,false),(68,false)]
theorem der_28715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28715 :=
  CNF.rup_sound cl_28715 [cl_6564,cl_28687] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6564 v h) (hints_cons _ _ _ (der_28687 v h) (by intro d hd; cases hd)))
def cl_28716 : CNF.NClause := [(51,false),(68,true),(20,false),(67,false),(69,false),(70,false),(92,false)]
theorem der_28716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28716 :=
  CNF.rup_sound cl_28716 [cl_6565,cl_28688] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6565 v h) (hints_cons _ _ _ (der_28688 v h) (by intro d hd; cases hd)))
def cl_28717 : CNF.NClause := [(51,false),(68,true),(20,true),(69,false),(70,false),(67,false),(92,false)]
theorem der_28717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28717 :=
  CNF.rup_sound cl_28717 [cl_6566,cl_28688] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6566 v h) (hints_cons _ _ _ (der_28688 v h) (by intro d hd; cases hd)))
def cl_28718 : CNF.NClause := [(51,false),(68,true),(20,false),(69,false),(70,false),(71,true),(92,false)]
theorem der_28718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28718 :=
  CNF.rup_sound cl_28718 [cl_6567,cl_28716] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6567 v h) (hints_cons _ _ _ (der_28716 v h) (by intro d hd; cases hd)))
def cl_28719 : CNF.NClause := [(51,false),(68,true),(67,true),(69,false),(70,false),(71,true),(92,false)]
theorem der_28719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28719 :=
  CNF.rup_sound cl_28719 [cl_6568,cl_28718] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6568 v h) (hints_cons _ _ _ (der_28718 v h) (by intro d hd; cases hd)))
def cl_28720 : CNF.NClause := [(51,false),(69,true),(20,false),(68,false),(67,false),(70,false),(92,false)]
theorem der_28720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28720 :=
  CNF.rup_sound cl_28720 [cl_6569,cl_28691] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6569 v h) (hints_cons _ _ _ (der_28691 v h) (by intro d hd; cases hd)))
def cl_28721 : CNF.NClause := [(51,false),(69,true),(20,true),(67,false),(68,false),(70,false),(92,false)]
theorem der_28721 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28721 :=
  CNF.rup_sound cl_28721 [cl_6570,cl_28691] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6570 v h) (hints_cons _ _ _ (der_28691 v h) (by intro d hd; cases hd)))
def cl_28722 : CNF.NClause := [(51,false),(69,true),(20,false),(68,false),(67,true),(70,false),(92,false)]
theorem der_28722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28722 :=
  CNF.rup_sound cl_28722 [cl_6571,cl_28707] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6571 v h) (hints_cons _ _ _ (der_28707 v h) (by intro d hd; cases hd)))
def cl_28723 : CNF.NClause := [(51,false),(69,true),(68,false),(67,true),(70,false),(71,true),(92,false)]
theorem der_28723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28723 :=
  CNF.rup_sound cl_28723 [cl_6572,cl_28722] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6572 v h) (hints_cons _ _ _ (der_28722 v h) (by intro d hd; cases hd)))
def cl_28724 : CNF.NClause := [(51,false),(69,true),(20,false),(68,true),(67,false),(70,false),(92,false)]
theorem der_28724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28724 :=
  CNF.rup_sound cl_28724 [cl_6573,cl_28694] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6573 v h) (hints_cons _ _ _ (der_28694 v h) (by intro d hd; cases hd)))
def cl_28725 : CNF.NClause := [(51,false),(69,true),(68,true),(67,false),(70,false),(71,true),(92,false)]
theorem der_28725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28725 :=
  CNF.rup_sound cl_28725 [cl_6574,cl_28724] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6574 v h) (hints_cons _ _ _ (der_28724 v h) (by intro d hd; cases hd)))
def cl_28726 : CNF.NClause := [(51,false),(68,true),(20,false),(67,true),(69,true),(70,false),(92,false)]
theorem der_28726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28726 :=
  CNF.rup_sound cl_28726 [cl_6575,cl_28697] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6575 v h) (hints_cons _ _ _ (der_28697 v h) (by intro d hd; cases hd)))
def cl_28727 : CNF.NClause := [(51,false),(68,true),(20,true),(67,true),(69,true),(70,false),(92,false)]
theorem der_28727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28727 :=
  CNF.rup_sound cl_28727 [cl_6576,cl_28697] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6576 v h) (hints_cons _ _ _ (der_28697 v h) (by intro d hd; cases hd)))
def cl_28728 : CNF.NClause := [(51,false),(20,false),(68,false),(69,false),(67,false),(70,true),(92,false)]
theorem der_28728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28728 :=
  CNF.rup_sound cl_28728 [cl_6577,cl_28698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6577 v h) (hints_cons _ _ _ (der_28698 v h) (by intro d hd; cases hd)))
def cl_28729 : CNF.NClause := [(51,false),(68,false),(20,true),(92,false),(67,false),(69,false),(70,true)]
theorem der_28729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28729 :=
  CNF.rup_sound cl_28729 [cl_6578,cl_28698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6578 v h) (hints_cons _ _ _ (der_28698 v h) (by intro d hd; cases hd)))
def cl_28730 : CNF.NClause := [(51,false),(70,true),(20,false),(68,false),(69,false),(67,true),(92,false)]
theorem der_28730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28730 :=
  CNF.rup_sound cl_28730 [cl_6579,cl_28699] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6579 v h) (hints_cons _ _ _ (der_28699 v h) (by intro d hd; cases hd)))
def cl_28731 : CNF.NClause := [(51,false),(70,true),(20,true),(68,false),(69,false),(67,true),(92,false)]
theorem der_28731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28731 :=
  CNF.rup_sound cl_28731 [cl_6580,cl_28700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6580 v h) (hints_cons _ _ _ (der_28700 v h) (by intro d hd; cases hd)))
def cl_28732 : CNF.NClause := [(51,false),(20,false),(68,true),(69,false),(67,false),(70,true),(92,false)]
theorem der_28732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28732 :=
  CNF.rup_sound cl_28732 [cl_6581,cl_28701] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6581 v h) (hints_cons _ _ _ (der_28701 v h) (by intro d hd; cases hd)))
def cl_28733 : CNF.NClause := [(51,false),(68,true),(71,true),(69,false),(67,false),(70,true),(92,false)]
theorem der_28733 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28733 :=
  CNF.rup_sound cl_28733 [cl_6582,cl_28732] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6582 v h) (hints_cons _ _ _ (der_28732 v h) (by intro d hd; cases hd)))
def cl_28734 : CNF.NClause := [(51,false),(68,true),(20,false),(67,true),(69,false),(70,true),(92,false)]
theorem der_28734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28734 :=
  CNF.rup_sound cl_28734 [cl_6583,cl_28704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6583 v h) (hints_cons _ _ _ (der_28704 v h) (by intro d hd; cases hd)))
def cl_28735 : CNF.NClause := [(51,false),(68,true),(20,true),(67,true),(69,false),(70,true),(92,false)]
theorem der_28735 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28735 :=
  CNF.rup_sound cl_28735 [cl_6584,cl_28704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6584 v h) (hints_cons _ _ _ (der_28704 v h) (by intro d hd; cases hd)))
def cl_28736 : CNF.NClause := [(51,false),(69,true),(20,false),(68,false),(67,false),(70,true),(92,false)]
theorem der_28736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28736 :=
  CNF.rup_sound cl_28736 [cl_6585,cl_28705] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6585 v h) (hints_cons _ _ _ (der_28705 v h) (by intro d hd; cases hd)))
def cl_28737 : CNF.NClause := [(51,false),(69,true),(20,true),(67,false),(68,false),(70,true),(92,false)]
theorem der_28737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28737 :=
  CNF.rup_sound cl_28737 [cl_6586,cl_28706] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6586 v h) (hints_cons _ _ _ (der_28706 v h) (by intro d hd; cases hd)))
def cl_28738 : CNF.NClause := [(51,false),(69,true),(20,false),(68,false),(67,true),(70,true),(92,false)]
theorem der_28738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28738 :=
  CNF.rup_sound cl_28738 [cl_6587,cl_28707] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6587 v h) (hints_cons _ _ _ (der_28707 v h) (by intro d hd; cases hd)))
def cl_28739 : CNF.NClause := [(51,false),(69,true),(20,true),(68,false),(67,true),(70,true),(92,false)]
theorem der_28739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28739 :=
  CNF.rup_sound cl_28739 [cl_6588,cl_28708] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6588 v h) (hints_cons _ _ _ (der_28708 v h) (by intro d hd; cases hd)))
def cl_28740 : CNF.NClause := [(51,false),(69,true),(20,false),(68,true),(67,false),(70,true),(92,false)]
theorem der_28740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28740 :=
  CNF.rup_sound cl_28740 [cl_6589,cl_28710] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6589 v h) (hints_cons _ _ _ (der_28710 v h) (by intro d hd; cases hd)))
def cl_28741 : CNF.NClause := [(51,false),(69,true),(20,true),(68,true),(67,false),(70,true),(92,false)]
theorem der_28741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28741 :=
  CNF.rup_sound cl_28741 [cl_6590,cl_28710] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6590 v h) (hints_cons _ _ _ (der_28710 v h) (by intro d hd; cases hd)))
def cl_28742 : CNF.NClause := [(51,false),(68,true),(20,false),(69,true),(70,true),(71,true),(92,false)]
theorem der_28742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28742 :=
  CNF.rup_sound cl_28742 [cl_6591,cl_28740] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6591 v h) (hints_cons _ _ _ (der_28740 v h) (by intro d hd; cases hd)))
def cl_28743 : CNF.NClause := [(51,false),(68,true),(67,true),(69,true),(70,true),(71,true),(92,false)]
theorem der_28743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28743 :=
  CNF.rup_sound cl_28743 [cl_6592,cl_28742] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6592 v h) (hints_cons _ _ _ (der_28742 v h) (by intro d hd; cases hd)))
def cl_28744 : CNF.NClause := [(51,false),(68,false),(20,true),(71,false),(67,false),(69,false),(70,false)]
theorem der_28744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28744 :=
  CNF.rup_sound cl_28744 [cl_6594,cl_6530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6594 v h) (hints_cons _ _ _ (inp_6530 v h) (by intro d hd; cases hd)))
def cl_28745 : CNF.NClause := [(51,false),(67,true),(20,false),(70,false),(69,false),(68,false),(71,false)]
theorem der_28745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28745 :=
  CNF.rup_sound cl_28745 [cl_6595,cl_28687] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6595 v h) (hints_cons _ _ _ (der_28687 v h) (by intro d hd; cases hd)))
def cl_28746 : CNF.NClause := [(51,false),(67,true),(20,true),(69,false),(70,false),(68,false),(71,false)]
theorem der_28746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28746 :=
  CNF.rup_sound cl_28746 [cl_6596,cl_28687] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6596 v h) (hints_cons _ _ _ (der_28687 v h) (by intro d hd; cases hd)))
def cl_28747 : CNF.NClause := [(51,false),(20,false),(68,true),(69,false),(70,false),(71,false),(67,false)]
theorem der_28747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28747 :=
  CNF.rup_sound cl_28747 [cl_6597,cl_28688] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6597 v h) (hints_cons _ _ _ (der_28688 v h) (by intro d hd; cases hd)))
def cl_28748 : CNF.NClause := [(51,false),(68,true),(20,true),(69,false),(67,false),(71,false),(70,false)]
theorem der_28748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28748 :=
  CNF.rup_sound cl_28748 [cl_6598,cl_28688] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6598 v h) (hints_cons _ _ _ (der_28688 v h) (by intro d hd; cases hd)))
def cl_28749 : CNF.NClause := [(51,false),(20,false),(67,true),(69,false),(70,false),(71,false),(92,true)]
theorem der_28749 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28749 :=
  CNF.rup_sound cl_28749 [cl_6599,cl_28745] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6599 v h) (hints_cons _ _ _ (der_28745 v h) (by intro d hd; cases hd)))
def cl_28750 : CNF.NClause := [(51,false),(68,true),(20,true),(67,true),(69,false),(70,false),(71,false)]
theorem der_28750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28750 :=
  CNF.rup_sound cl_28750 [cl_6600,cl_28690] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6600 v h) (hints_cons _ _ _ (der_28690 v h) (by intro d hd; cases hd)))
def cl_28751 : CNF.NClause := [(51,false),(69,true),(20,false),(67,false),(68,false),(70,false),(71,false)]
theorem der_28751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28751 :=
  CNF.rup_sound cl_28751 [cl_6601,cl_28691] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6601 v h) (hints_cons _ _ _ (der_28691 v h) (by intro d hd; cases hd)))
def cl_28752 : CNF.NClause := [(51,false),(69,true),(20,true),(67,false),(68,false),(70,false),(71,false)]
theorem der_28752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28752 :=
  CNF.rup_sound cl_28752 [cl_6602,cl_28691] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6602 v h) (hints_cons _ _ _ (der_28691 v h) (by intro d hd; cases hd)))
def cl_28753 : CNF.NClause := [(51,false),(69,true),(20,false),(68,false),(67,true),(70,false),(71,false)]
theorem der_28753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28753 :=
  CNF.rup_sound cl_28753 [cl_6603,cl_28707] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6603 v h) (hints_cons _ _ _ (der_28707 v h) (by intro d hd; cases hd)))
def cl_28754 : CNF.NClause := [(51,false),(69,true),(20,true),(68,false),(70,false),(71,false),(92,true)]
theorem der_28754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28754 :=
  CNF.rup_sound cl_28754 [cl_6604,cl_28752] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6604 v h) (hints_cons _ _ _ (der_28752 v h) (by intro d hd; cases hd)))
def cl_28755 : CNF.NClause := [(51,false),(69,true),(20,false),(68,true),(67,false),(70,false),(71,false)]
theorem der_28755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28755 :=
  CNF.rup_sound cl_28755 [cl_6605,cl_28694] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6605 v h) (hints_cons _ _ _ (der_28694 v h) (by intro d hd; cases hd)))
def cl_28756 : CNF.NClause := [(51,false),(69,true),(20,true),(67,false),(70,false),(71,false),(92,true)]
theorem der_28756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28756 :=
  CNF.rup_sound cl_28756 [cl_6606,cl_28752] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6606 v h) (hints_cons _ _ _ (der_28752 v h) (by intro d hd; cases hd)))
def cl_28757 : CNF.NClause := [(51,false),(68,true),(20,false),(67,true),(69,true),(70,false),(71,false)]
theorem der_28757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28757 :=
  CNF.rup_sound cl_28757 [cl_6607,cl_28697] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6607 v h) (hints_cons _ _ _ (der_28697 v h) (by intro d hd; cases hd)))
def cl_28758 : CNF.NClause := [(51,false),(68,true),(20,true),(67,true),(69,true),(70,false),(71,false)]
theorem der_28758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28758 :=
  CNF.rup_sound cl_28758 [cl_6608,cl_28697] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6608 v h) (hints_cons _ _ _ (der_28697 v h) (by intro d hd; cases hd)))
def cl_28759 : CNF.NClause := [(51,false),(68,false),(20,false),(67,false),(69,false),(70,true),(71,false)]
theorem der_28759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28759 :=
  CNF.rup_sound cl_28759 [cl_6609,cl_28698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6609 v h) (hints_cons _ _ _ (der_28698 v h) (by intro d hd; cases hd)))
def cl_28760 : CNF.NClause := [(51,false),(68,false),(20,true),(67,false),(69,false),(70,true),(71,false)]
theorem der_28760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28760 :=
  CNF.rup_sound cl_28760 [cl_6610,cl_28698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6610 v h) (hints_cons _ _ _ (der_28698 v h) (by intro d hd; cases hd)))
def cl_28761 : CNF.NClause := [(51,false),(20,false),(68,false),(69,false),(67,true),(71,false),(92,true)]
theorem der_28761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28761 :=
  CNF.rup_sound cl_28761 [cl_6611,cl_28745] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6611 v h) (hints_cons _ _ _ (der_28745 v h) (by intro d hd; cases hd)))
def cl_28762 : CNF.NClause := [(51,false),(70,true),(20,true),(69,false),(68,false),(71,false),(92,true)]
theorem der_28762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28762 :=
  CNF.rup_sound cl_28762 [cl_6612,cl_28760] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6612 v h) (hints_cons _ _ _ (der_28760 v h) (by intro d hd; cases hd)))
def cl_28763 : CNF.NClause := [(51,false),(20,false),(68,true),(69,false),(67,false),(70,true),(71,false)]
theorem der_28763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28763 :=
  CNF.rup_sound cl_28763 [cl_6613,cl_28701] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6613 v h) (hints_cons _ _ _ (der_28701 v h) (by intro d hd; cases hd)))
def cl_28764 : CNF.NClause := [(51,false),(20,true),(92,true),(69,false),(67,false),(70,true),(71,false)]
theorem der_28764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28764 :=
  CNF.rup_sound cl_28764 [cl_6614,cl_28760] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6614 v h) (hints_cons _ _ _ (der_28760 v h) (by intro d hd; cases hd)))
def cl_28765 : CNF.NClause := [(51,false),(68,true),(20,false),(67,true),(69,false),(70,true),(71,false)]
theorem der_28765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28765 :=
  CNF.rup_sound cl_28765 [cl_6615,cl_28704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6615 v h) (hints_cons _ _ _ (der_28704 v h) (by intro d hd; cases hd)))
def cl_28766 : CNF.NClause := [(51,false),(68,true),(20,true),(67,true),(69,false),(70,true),(71,false)]
theorem der_28766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28766 :=
  CNF.rup_sound cl_28766 [cl_6616,cl_28704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6616 v h) (hints_cons _ _ _ (der_28704 v h) (by intro d hd; cases hd)))
def cl_28767 : CNF.NClause := [(51,false),(20,false),(67,false),(68,false),(70,true),(71,false),(92,true)]
theorem der_28767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28767 :=
  CNF.rup_sound cl_28767 [cl_6617,cl_28759] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6617 v h) (hints_cons _ _ _ (der_28759 v h) (by intro d hd; cases hd)))
def cl_28768 : CNF.NClause := [(51,false),(69,true),(20,true),(67,false),(68,false),(71,false),(92,true)]
theorem der_28768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28768 :=
  CNF.rup_sound cl_28768 [cl_6618,cl_28752] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6618 v h) (hints_cons _ _ _ (der_28752 v h) (by intro d hd; cases hd)))
def cl_28769 : CNF.NClause := [(51,false),(69,true),(20,false),(68,false),(67,true),(70,true),(71,false)]
theorem der_28769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28769 :=
  CNF.rup_sound cl_28769 [cl_6619,cl_28707] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6619 v h) (hints_cons _ _ _ (der_28707 v h) (by intro d hd; cases hd)))
def cl_28770 : CNF.NClause := [(51,false),(69,true),(20,true),(67,true),(68,false),(70,true),(71,false)]
theorem der_28770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28770 :=
  CNF.rup_sound cl_28770 [cl_6620,cl_28708] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6620 v h) (hints_cons _ _ _ (der_28708 v h) (by intro d hd; cases hd)))
def cl_28771 : CNF.NClause := [(51,false),(69,true),(20,false),(68,true),(67,false),(70,true),(71,false)]
theorem der_28771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28771 :=
  CNF.rup_sound cl_28771 [cl_6621,cl_28710] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6621 v h) (hints_cons _ _ _ (der_28710 v h) (by intro d hd; cases hd)))
def cl_28772 : CNF.NClause := [(51,false),(69,true),(20,true),(68,true),(67,false),(70,true),(71,false)]
theorem der_28772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28772 :=
  CNF.rup_sound cl_28772 [cl_6622,cl_28710] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6622 v h) (hints_cons _ _ _ (der_28710 v h) (by intro d hd; cases hd)))
def cl_28773 : CNF.NClause := [(51,false),(68,true),(20,false),(67,true),(69,true),(70,true),(71,false)]
theorem der_28773 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28773 :=
  CNF.rup_sound cl_28773 [cl_6623,cl_28711] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6623 v h) (hints_cons _ _ _ (der_28711 v h) (by intro d hd; cases hd)))
def cl_28774 : CNF.NClause := [(51,false),(68,true),(20,true),(67,true),(70,true),(71,false),(92,true)]
theorem der_28774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28774 :=
  CNF.rup_sound cl_28774 [cl_6624,cl_28766] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6624 v h) (hints_cons _ _ _ (der_28766 v h) (by intro d hd; cases hd)))
def cl_28775 : CNF.NClause := [(51,false),(68,false),(20,false),(69,false),(67,false),(70,false),(71,true)]
theorem der_28775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28775 :=
  CNF.rup_sound cl_28775 [cl_6625,cl_28713] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6625 v h) (hints_cons _ _ _ (der_28713 v h) (by intro d hd; cases hd)))
def cl_28776 : CNF.NClause := [(51,false),(68,false),(20,true),(70,false),(69,false),(71,true),(67,false)]
theorem der_28776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28776 :=
  CNF.rup_sound cl_28776 [cl_6626,cl_28713] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6626 v h) (hints_cons _ _ _ (der_28713 v h) (by intro d hd; cases hd)))
def cl_28777 : CNF.NClause := [(51,false),(92,true),(20,false),(68,false),(69,false),(67,true),(70,false)]
theorem der_28777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28777 :=
  CNF.rup_sound cl_28777 [cl_6627,cl_28745] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6627 v h) (hints_cons _ _ _ (der_28745 v h) (by intro d hd; cases hd)))
def cl_28778 : CNF.NClause := [(51,false),(67,true),(20,true),(68,false),(69,false),(70,false),(71,true)]
theorem der_28778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28778 :=
  CNF.rup_sound cl_28778 [cl_6628,cl_28715] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6628 v h) (hints_cons _ _ _ (der_28715 v h) (by intro d hd; cases hd)))
def cl_28780 : CNF.NClause := [(51,false),(20,true),(92,true),(67,false),(70,false),(71,true),(69,false)]
theorem der_28780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28780 :=
  CNF.rup_sound cl_28780 [cl_6630,cl_28776] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6630 v h) (hints_cons _ _ _ (der_28776 v h) (by intro d hd; cases hd)))
def cl_28781 : CNF.NClause := [(51,false),(68,true),(20,false),(67,true),(69,false),(70,false),(71,true)]
theorem der_28781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28781 :=
  CNF.rup_sound cl_28781 [cl_6631,cl_28719] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6631 v h) (hints_cons _ _ _ (der_28719 v h) (by intro d hd; cases hd)))
def cl_28782 : CNF.NClause := [(51,false),(68,true),(20,true),(67,true),(69,false),(70,false),(71,true)]
theorem der_28782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28782 :=
  CNF.rup_sound cl_28782 [cl_6632,cl_28719] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6632 v h) (hints_cons _ _ _ (der_28719 v h) (by intro d hd; cases hd)))
def cl_28783 : CNF.NClause := [(51,false),(69,true),(20,false),(67,false),(68,false),(70,false),(71,true)]
theorem der_28783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28783 :=
  CNF.rup_sound cl_28783 [cl_6633,cl_28720] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6633 v h) (hints_cons _ _ _ (der_28720 v h) (by intro d hd; cases hd)))
def cl_28784 : CNF.NClause := [(51,false),(69,true),(20,true),(67,false),(68,false),(70,false),(92,true)]
theorem der_28784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28784 :=
  CNF.rup_sound cl_28784 [cl_6634,cl_28752] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6634 v h) (hints_cons _ _ _ (der_28752 v h) (by intro d hd; cases hd)))
def cl_28785 : CNF.NClause := [(51,false),(69,true),(20,false),(68,false),(67,true),(70,false),(71,true)]
theorem der_28785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28785 :=
  CNF.rup_sound cl_28785 [cl_6635,cl_28722] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6635 v h) (hints_cons _ _ _ (der_28722 v h) (by intro d hd; cases hd)))
def cl_28786 : CNF.NClause := [(51,false),(69,true),(20,true),(67,true),(68,false),(70,false),(71,true)]
theorem der_28786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28786 :=
  CNF.rup_sound cl_28786 [cl_6636,cl_28723] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6636 v h) (hints_cons _ _ _ (der_28723 v h) (by intro d hd; cases hd)))
def cl_28787 : CNF.NClause := [(51,false),(69,true),(20,false),(67,false),(70,false),(71,true),(92,true)]
theorem der_28787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28787 :=
  CNF.rup_sound cl_28787 [cl_6637,cl_28783] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6637 v h) (hints_cons _ _ _ (der_28783 v h) (by intro d hd; cases hd)))
def cl_28788 : CNF.NClause := [(51,false),(69,true),(20,true),(67,false),(70,false),(71,true),(92,true)]
theorem der_28788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28788 :=
  CNF.rup_sound cl_28788 [cl_6638,cl_28784] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6638 v h) (hints_cons _ _ _ (der_28784 v h) (by intro d hd; cases hd)))
def cl_28790 : CNF.NClause := [(51,false),(68,true),(20,true),(67,true),(70,false),(71,true),(92,true)]
theorem der_28790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28790 :=
  CNF.rup_sound cl_28790 [cl_6640,cl_28782] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6640 v h) (hints_cons _ _ _ (der_28782 v h) (by intro d hd; cases hd)))
def cl_28791 : CNF.NClause := [(51,false),(20,false),(67,false),(69,false),(68,false),(70,true),(71,true)]
theorem der_28791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28791 :=
  CNF.rup_sound cl_28791 [cl_6641,cl_28728] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6641 v h) (hints_cons _ _ _ (der_28728 v h) (by intro d hd; cases hd)))
def cl_28792 : CNF.NClause := [(51,false),(68,false),(20,true),(70,true),(67,false),(69,false),(92,true)]
theorem der_28792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28792 :=
  CNF.rup_sound cl_28792 [cl_6642,cl_28760] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6642 v h) (hints_cons _ _ _ (der_28760 v h) (by intro d hd; cases hd)))
def cl_28793 : CNF.NClause := [(51,false),(70,true),(20,false),(68,false),(69,false),(67,true),(92,true)]
theorem der_28793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28793 :=
  CNF.rup_sound cl_28793 [cl_6643,cl_28761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6643 v h) (hints_cons _ _ _ (der_28761 v h) (by intro d hd; cases hd)))
def cl_28794 : CNF.NClause := [(51,false),(71,true),(20,true),(67,true),(69,false),(68,false),(70,true)]
theorem der_28794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28794 :=
  CNF.rup_sound cl_28794 [cl_6644,cl_28731] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6644 v h) (hints_cons _ _ _ (der_28731 v h) (by intro d hd; cases hd)))
def cl_28796 : CNF.NClause := [(51,false),(20,true),(92,true),(69,false),(67,false),(70,true),(71,true)]
theorem der_28796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28796 :=
  CNF.rup_sound cl_28796 [cl_6646,cl_28792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6646 v h) (hints_cons _ _ _ (der_28792 v h) (by intro d hd; cases hd)))
def cl_28798 : CNF.NClause := [(51,false),(68,true),(20,true),(67,true),(69,false),(70,true),(92,true)]
theorem der_28798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28798 :=
  CNF.rup_sound cl_28798 [cl_6648,cl_28766] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6648 v h) (hints_cons _ _ _ (der_28766 v h) (by intro d hd; cases hd)))
def cl_28799 : CNF.NClause := [(51,false),(20,false),(67,false),(68,false),(70,true),(71,true),(92,true)]
theorem der_28799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28799 :=
  CNF.rup_sound cl_28799 [cl_6649,cl_28791] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6649 v h) (hints_cons _ _ _ (der_28791 v h) (by intro d hd; cases hd)))
def cl_28800 : CNF.NClause := [(51,false),(69,true),(20,true),(67,false),(68,false),(70,true),(92,true)]
theorem der_28800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28800 :=
  CNF.rup_sound cl_28800 [cl_6650,cl_28768] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6650 v h) (hints_cons _ _ _ (der_28768 v h) (by intro d hd; cases hd)))
def cl_28801 : CNF.NClause := [(51,false),(69,true),(20,false),(68,false),(67,true),(70,true),(92,true)]
theorem der_28801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28801 :=
  CNF.rup_sound cl_28801 [cl_6651,cl_28769] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6651 v h) (hints_cons _ _ _ (der_28769 v h) (by intro d hd; cases hd)))
def cl_28802 : CNF.NClause := [(51,false),(20,true),(67,true),(68,false),(70,true),(71,true),(92,true)]
theorem der_28802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28802 :=
  CNF.rup_sound cl_28802 [cl_6652,cl_28794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6652 v h) (hints_cons _ _ _ (der_28794 v h) (by intro d hd; cases hd)))
def cl_28803 : CNF.NClause := [(51,false),(69,true),(20,false),(68,true),(67,false),(70,true),(71,true)]
theorem der_28803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28803 :=
  CNF.rup_sound cl_28803 [cl_6653,cl_28740] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6653 v h) (hints_cons _ _ _ (der_28740 v h) (by intro d hd; cases hd)))
def cl_28804 : CNF.NClause := [(51,false),(69,true),(20,true),(67,false),(70,true),(71,true),(92,true)]
theorem der_28804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28804 :=
  CNF.rup_sound cl_28804 [cl_6654,cl_28800] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6654 v h) (hints_cons _ _ _ (der_28800 v h) (by intro d hd; cases hd)))
def cl_28805 : CNF.NClause := [(51,false),(20,false),(67,true),(69,true),(70,true),(71,true),(92,true)]
theorem der_28805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28805 :=
  CNF.rup_sound cl_28805 [cl_6655,cl_28801] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6655 v h) (hints_cons _ _ _ (der_28801 v h) (by intro d hd; cases hd)))
def cl_28806 : CNF.NClause := [(51,false),(68,true),(67,true),(69,true),(70,true),(71,true),(92,true)]
theorem der_28806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28806 :=
  CNF.rup_sound cl_28806 [cl_6656,cl_28805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6656 v h) (hints_cons _ _ _ (der_28805 v h) (by intro d hd; cases hd)))
def cl_28807 : CNF.NClause := [(50,false),(90,false),(19,true),(85,false),(71,false),(74,false),(77,false)]
theorem der_28807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28807 :=
  CNF.rup_sound cl_28807 [cl_6404,cl_26749] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6404 v h) (hints_cons _ _ _ (der_26749 v h) (by intro d hd; cases hd)))
def cl_28808 : CNF.NClause := [(50,false),(71,true),(85,false),(77,false),(74,false),(63,false),(90,false)]
theorem der_28808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28808 :=
  CNF.rup_sound cl_28808 [cl_6406,cl_6405] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6406 v h) (hints_cons _ _ _ (inp_6405 v h) (by intro d hd; cases hd)))
def cl_28809 : CNF.NClause := [(50,false),(19,false),(85,false),(74,false),(77,false),(71,true),(90,false)]
theorem der_28809 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28809 :=
  CNF.rup_sound cl_28809 [cl_6407,cl_28808] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6407 v h) (hints_cons _ _ _ (der_28808 v h) (by intro d hd; cases hd)))
def cl_28810 : CNF.NClause := [(50,false),(19,true),(71,true),(74,false),(77,false),(85,false),(90,false)]
theorem der_28810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28810 :=
  CNF.rup_sound cl_28810 [cl_6408,cl_28808] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6408 v h) (hints_cons _ _ _ (der_28808 v h) (by intro d hd; cases hd)))
def cl_28811 : CNF.NClause := [(50,false),(74,true),(71,false),(63,false),(77,false),(85,false),(90,false)]
theorem der_28811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28811 :=
  CNF.rup_sound cl_28811 [cl_6409,cl_26749] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6409 v h) (hints_cons _ _ _ (der_26749 v h) (by intro d hd; cases hd)))
def cl_28812 : CNF.NClause := [(50,false),(74,true),(19,false),(85,false),(71,false),(77,false),(90,false)]
theorem der_28812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28812 :=
  CNF.rup_sound cl_28812 [cl_6411,cl_28811] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6411 v h) (hints_cons _ _ _ (der_28811 v h) (by intro d hd; cases hd)))
def cl_28813 : CNF.NClause := [(50,false),(74,true),(19,true),(71,false),(77,false),(85,false),(90,false)]
theorem der_28813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28813 :=
  CNF.rup_sound cl_28813 [cl_6412,cl_28811] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6412 v h) (hints_cons _ _ _ (der_28811 v h) (by intro d hd; cases hd)))
def cl_28814 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(77,false),(85,false),(90,false)]
theorem der_28814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28814 :=
  CNF.rup_sound cl_28814 [cl_6413,cl_28808] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6413 v h) (hints_cons _ _ _ (der_28808 v h) (by intro d hd; cases hd)))
def cl_28815 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(77,false),(85,false),(90,false)]
theorem der_28815 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28815 :=
  CNF.rup_sound cl_28815 [cl_6414,cl_28808] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6414 v h) (hints_cons _ _ _ (der_28808 v h) (by intro d hd; cases hd)))
def cl_28816 : CNF.NClause := [(50,false),(19,false),(63,true),(71,true),(77,false),(85,false),(90,false)]
theorem der_28816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28816 :=
  CNF.rup_sound cl_28816 [cl_6415,cl_28809] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6415 v h) (hints_cons _ _ _ (der_28809 v h) (by intro d hd; cases hd)))
def cl_28817 : CNF.NClause := [(50,false),(74,true),(63,true),(71,true),(77,false),(85,false),(90,false)]
theorem der_28817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28817 :=
  CNF.rup_sound cl_28817 [cl_6416,cl_28816] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6416 v h) (hints_cons _ _ _ (der_28816 v h) (by intro d hd; cases hd)))
def cl_28818 : CNF.NClause := [(50,false),(63,true),(19,false),(74,false),(71,false),(85,false),(90,false)]
theorem der_28818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28818 :=
  CNF.rup_sound cl_28818 [cl_6419,cl_6403] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6419 v h) (hints_cons _ _ _ (inp_6403 v h) (by intro d hd; cases hd)))
def cl_28819 : CNF.NClause := [(50,false),(19,true),(85,false),(77,true),(74,false),(71,false),(90,false)]
theorem der_28819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28819 :=
  CNF.rup_sound cl_28819 [cl_6420,cl_26750] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6420 v h) (hints_cons _ _ _ (der_26750 v h) (by intro d hd; cases hd)))
def cl_28820 : CNF.NClause := [(50,false),(19,false),(63,false),(85,false),(74,false),(71,true),(90,false)]
theorem der_28820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28820 :=
  CNF.rup_sound cl_28820 [cl_6421,cl_28808] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6421 v h) (hints_cons _ _ _ (der_28808 v h) (by intro d hd; cases hd)))
def cl_28821 : CNF.NClause := [(50,false),(19,true),(63,false),(74,false),(71,true),(85,false),(90,false)]
theorem der_28821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28821 :=
  CNF.rup_sound cl_28821 [cl_6422,cl_28808] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6422 v h) (hints_cons _ _ _ (der_28808 v h) (by intro d hd; cases hd)))
def cl_28822 : CNF.NClause := [(50,false),(77,true),(19,false),(74,false),(71,true),(85,false),(90,false)]
theorem der_28822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28822 :=
  CNF.rup_sound cl_28822 [cl_6423,cl_28820] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6423 v h) (hints_cons _ _ _ (der_28820 v h) (by intro d hd; cases hd)))
def cl_28823 : CNF.NClause := [(50,false),(77,true),(63,true),(74,false),(71,true),(85,false),(90,false)]
theorem der_28823 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28823 :=
  CNF.rup_sound cl_28823 [cl_6424,cl_28822] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6424 v h) (hints_cons _ _ _ (der_28822 v h) (by intro d hd; cases hd)))
def cl_28824 : CNF.NClause := [(50,false),(74,true),(19,false),(85,false),(63,false),(71,false),(90,false)]
theorem der_28824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28824 :=
  CNF.rup_sound cl_28824 [cl_6425,cl_28811] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6425 v h) (hints_cons _ _ _ (der_28811 v h) (by intro d hd; cases hd)))
def cl_28825 : CNF.NClause := [(50,false),(74,true),(19,false),(71,false),(63,true),(85,false),(90,false)]
theorem der_28825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28825 :=
  CNF.rup_sound cl_28825 [cl_6427,cl_28812] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6427 v h) (hints_cons _ _ _ (der_28812 v h) (by intro d hd; cases hd)))
def cl_28826 : CNF.NClause := [(50,false),(77,true),(63,true),(71,false),(74,true),(85,false),(90,false)]
theorem der_28826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28826 :=
  CNF.rup_sound cl_28826 [cl_6428,cl_28825] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6428 v h) (hints_cons _ _ _ (der_28825 v h) (by intro d hd; cases hd)))
def cl_28827 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(85,false),(77,true),(90,false)]
theorem der_28827 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28827 :=
  CNF.rup_sound cl_28827 [cl_6429,cl_28820] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6429 v h) (hints_cons _ _ _ (der_28820 v h) (by intro d hd; cases hd)))
def cl_28828 : CNF.NClause := [(50,false),(74,true),(63,false),(71,true),(77,true),(85,false),(90,false)]
theorem der_28828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28828 :=
  CNF.rup_sound cl_28828 [cl_6430,cl_28827] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6430 v h) (hints_cons _ _ _ (der_28827 v h) (by intro d hd; cases hd)))
def cl_28829 : CNF.NClause := [(50,false),(74,true),(19,false),(63,true),(71,true),(85,false),(90,false)]
theorem der_28829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28829 :=
  CNF.rup_sound cl_28829 [cl_6431,cl_28817] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6431 v h) (hints_cons _ _ _ (der_28817 v h) (by intro d hd; cases hd)))
def cl_28830 : CNF.NClause := [(50,false),(74,true),(19,true),(63,true),(71,true),(85,false),(90,false)]
theorem der_28830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28830 :=
  CNF.rup_sound cl_28830 [cl_6432,cl_28817] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6432 v h) (hints_cons _ _ _ (der_28817 v h) (by intro d hd; cases hd)))
def cl_28831 : CNF.NClause := [(50,false),(85,true),(74,false),(71,false),(77,false),(63,false),(90,false)]
theorem der_28831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28831 :=
  CNF.rup_sound cl_28831 [cl_6434,cl_6433] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6434 v h) (hints_cons _ _ _ (inp_6433 v h) (by intro d hd; cases hd)))
def cl_28832 : CNF.NClause := [(50,false),(19,false),(71,false),(74,false),(77,false),(85,true),(90,false)]
theorem der_28832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28832 :=
  CNF.rup_sound cl_28832 [cl_6435,cl_28831] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6435 v h) (hints_cons _ _ _ (der_28831 v h) (by intro d hd; cases hd)))
def cl_28833 : CNF.NClause := [(50,false),(19,true),(90,false),(85,true),(71,false),(77,false),(74,false)]
theorem der_28833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28833 :=
  CNF.rup_sound cl_28833 [cl_6436,cl_28831] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6436 v h) (hints_cons _ _ _ (der_28831 v h) (by intro d hd; cases hd)))
def cl_28834 : CNF.NClause := [(50,false),(71,true),(19,false),(63,false),(74,false),(90,false),(77,false)]
theorem der_28834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28834 :=
  CNF.rup_sound cl_28834 [cl_6437,cl_28808] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6437 v h) (hints_cons _ _ _ (der_28808 v h) (by intro d hd; cases hd)))
def cl_28835 : CNF.NClause := [(50,false),(71,true),(19,true),(63,false),(77,false),(90,false),(74,false)]
theorem der_28835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28835 :=
  CNF.rup_sound cl_28835 [cl_6438,cl_28808] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6438 v h) (hints_cons _ _ _ (der_28808 v h) (by intro d hd; cases hd)))
def cl_28836 : CNF.NClause := [(50,false),(90,false),(19,false),(74,false),(77,false),(71,true),(85,true)]
theorem der_28836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28836 :=
  CNF.rup_sound cl_28836 [cl_6439,cl_28834] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6439 v h) (hints_cons _ _ _ (der_28834 v h) (by intro d hd; cases hd)))
def cl_28837 : CNF.NClause := [(50,false),(63,true),(90,false),(74,false),(77,false),(71,true),(85,true)]
theorem der_28837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28837 :=
  CNF.rup_sound cl_28837 [cl_6440,cl_28836] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6440 v h) (hints_cons _ _ _ (der_28836 v h) (by intro d hd; cases hd)))
def cl_28838 : CNF.NClause := [(50,false),(19,false),(71,false),(63,false),(77,false),(90,false),(74,true)]
theorem der_28838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28838 :=
  CNF.rup_sound cl_28838 [cl_6441,cl_28811] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6441 v h) (hints_cons _ _ _ (der_28811 v h) (by intro d hd; cases hd)))
def cl_28839 : CNF.NClause := [(50,false),(74,true),(19,false),(90,false),(71,false),(63,true),(77,false)]
theorem der_28839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28839 :=
  CNF.rup_sound cl_28839 [cl_6443,cl_28825] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6443 v h) (hints_cons _ _ _ (der_28825 v h) (by intro d hd; cases hd)))
def cl_28840 : CNF.NClause := [(50,false),(74,true),(71,false),(90,false),(63,true),(77,false),(85,true)]
theorem der_28840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28840 :=
  CNF.rup_sound cl_28840 [cl_6444,cl_28839] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6444 v h) (hints_cons _ _ _ (der_28839 v h) (by intro d hd; cases hd)))
def cl_28841 : CNF.NClause := [(50,false),(19,false),(63,false),(90,false),(71,true),(77,false),(85,true)]
theorem der_28841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28841 :=
  CNF.rup_sound cl_28841 [cl_6445,cl_28834] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6445 v h) (hints_cons _ _ _ (der_28834 v h) (by intro d hd; cases hd)))
def cl_28842 : CNF.NClause := [(50,false),(74,true),(63,false),(71,true),(77,false),(85,true),(90,false)]
theorem der_28842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28842 :=
  CNF.rup_sound cl_28842 [cl_6446,cl_28841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6446 v h) (hints_cons _ _ _ (der_28841 v h) (by intro d hd; cases hd)))
def cl_28843 : CNF.NClause := [(50,false),(74,true),(19,false),(63,true),(71,true),(77,false),(90,false)]
theorem der_28843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28843 :=
  CNF.rup_sound cl_28843 [cl_6447,cl_28817] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6447 v h) (hints_cons _ _ _ (der_28817 v h) (by intro d hd; cases hd)))
def cl_28844 : CNF.NClause := [(50,false),(74,true),(19,true),(63,true),(71,true),(77,false),(90,false)]
theorem der_28844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28844 :=
  CNF.rup_sound cl_28844 [cl_6448,cl_28817] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6448 v h) (hints_cons _ _ _ (der_28817 v h) (by intro d hd; cases hd)))
def cl_28845 : CNF.NClause := [(50,false),(85,true),(19,false),(71,false),(74,false),(90,false),(63,false)]
theorem der_28845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28845 :=
  CNF.rup_sound cl_28845 [cl_6449,cl_28831] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6449 v h) (hints_cons _ _ _ (der_28831 v h) (by intro d hd; cases hd)))
def cl_28846 : CNF.NClause := [(50,false),(85,true),(19,true),(63,false),(74,false),(71,false),(90,false)]
theorem der_28846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28846 :=
  CNF.rup_sound cl_28846 [cl_6450,cl_28831] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6450 v h) (hints_cons _ _ _ (der_28831 v h) (by intro d hd; cases hd)))
def cl_28847 : CNF.NClause := [(50,false),(63,true),(19,false),(71,false),(74,false),(77,true),(90,false)]
theorem der_28847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28847 :=
  CNF.rup_sound cl_28847 [cl_6451,cl_28818] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6451 v h) (hints_cons _ _ _ (der_28818 v h) (by intro d hd; cases hd)))
def cl_28848 : CNF.NClause := [(50,false),(19,true),(90,false),(74,false),(63,true),(71,false),(77,true)]
theorem der_28848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28848 :=
  CNF.rup_sound cl_28848 [cl_6452,cl_28819] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6452 v h) (hints_cons _ _ _ (der_28819 v h) (by intro d hd; cases hd)))
def cl_28849 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(77,true),(74,false),(90,false)]
theorem der_28849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28849 :=
  CNF.rup_sound cl_28849 [cl_6453,cl_28820] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6453 v h) (hints_cons _ _ _ (der_28820 v h) (by intro d hd; cases hd)))
def cl_28850 : CNF.NClause := [(50,false),(77,true),(63,false),(74,false),(71,true),(85,true),(90,false)]
theorem der_28850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28850 :=
  CNF.rup_sound cl_28850 [cl_6454,cl_28849] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6454 v h) (hints_cons _ _ _ (der_28849 v h) (by intro d hd; cases hd)))
def cl_28851 : CNF.NClause := [(50,false),(77,true),(19,false),(63,true),(74,false),(71,true),(90,false)]
theorem der_28851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28851 :=
  CNF.rup_sound cl_28851 [cl_6455,cl_28823] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6455 v h) (hints_cons _ _ _ (der_28823 v h) (by intro d hd; cases hd)))
def cl_28852 : CNF.NClause := [(50,false),(77,true),(19,true),(63,true),(74,false),(71,true),(90,false)]
theorem der_28852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28852 :=
  CNF.rup_sound cl_28852 [cl_6456,cl_28823] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6456 v h) (hints_cons _ _ _ (der_28823 v h) (by intro d hd; cases hd)))
def cl_28853 : CNF.NClause := [(50,false),(19,false),(71,false),(63,false),(74,true),(77,true),(90,false)]
theorem der_28853 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28853 :=
  CNF.rup_sound cl_28853 [cl_6457,cl_28824] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6457 v h) (hints_cons _ _ _ (der_28824 v h) (by intro d hd; cases hd)))
def cl_28854 : CNF.NClause := [(50,false),(19,false),(71,false),(74,true),(63,true),(77,true),(90,false)]
theorem der_28854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28854 :=
  CNF.rup_sound cl_28854 [cl_6459,cl_28825] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6459 v h) (hints_cons _ _ _ (der_28825 v h) (by intro d hd; cases hd)))
def chunk012 : List CNF.NClause := [cl_28337,cl_28339,cl_28340,cl_28341,cl_28342,cl_28343,cl_28344,cl_28345,cl_28346,cl_28347,cl_28348,cl_28349,cl_28350,cl_28351,cl_28352,cl_28353,cl_28354,cl_28355,cl_28356,cl_28357,cl_28358,cl_28359,cl_28360,cl_28361,cl_28362,cl_28363,cl_28364,cl_28365,cl_28366,cl_28367,cl_28368,cl_28369,cl_28370,cl_28371,cl_28372,cl_28373,cl_28374,cl_28375,cl_28376,cl_28377,cl_28378,cl_28379,cl_28380,cl_28381,cl_28382,cl_28383,cl_28384,cl_28385,cl_28386,cl_28387,cl_28388,cl_28389,cl_28390,cl_28391,cl_28392,cl_28393,cl_28394,cl_28395,cl_28397,cl_28398,cl_28399,cl_28400,cl_28401,cl_28402,cl_28403,cl_28404,cl_28405,cl_28406,cl_28407,cl_28408,cl_28409,cl_28410,cl_28411,cl_28412,cl_28413,cl_28414,cl_28415,cl_28416,cl_28417,cl_28418,cl_28419,cl_28420,cl_28421,cl_28422,cl_28423,cl_28424,cl_28425,cl_28426,cl_28427,cl_28428,cl_28429,cl_28430,cl_28431,cl_28432,cl_28434,cl_28435,cl_28436,cl_28437,cl_28438,cl_28439,cl_28440,cl_28441,cl_28442,cl_28443,cl_28444,cl_28445,cl_28446,cl_28447,cl_28448,cl_28449,cl_28450,cl_28451,cl_28452,cl_28453,cl_28454,cl_28455,cl_28456,cl_28457,cl_28458,cl_28460,cl_28461,cl_28462,cl_28463,cl_28464,cl_28465,cl_28466,cl_28467,cl_28468,cl_28469,cl_28470,cl_28471,cl_28472,cl_28473,cl_28474,cl_28475,cl_28476,cl_28477,cl_28478,cl_28479,cl_28480,cl_28481,cl_28482,cl_28483,cl_28484,cl_28485,cl_28486,cl_28487,cl_28488,cl_28489,cl_28490,cl_28491,cl_28492,cl_28493,cl_28494,cl_28495,cl_28496,cl_28497,cl_28498,cl_28499,cl_28500,cl_28501,cl_28502,cl_28503,cl_28504,cl_28505,cl_28506,cl_28507,cl_28508,cl_28509,cl_28510,cl_28511,cl_28512,cl_28513,cl_28514,cl_28515,cl_28516,cl_28517,cl_28518,cl_28519,cl_28520,cl_28521,cl_28522,cl_28523,cl_28524,cl_28525,cl_28526,cl_28527,cl_28528,cl_28529,cl_28530,cl_28531,cl_28532,cl_28533,cl_28534,cl_28535,cl_28536,cl_28537,cl_28538,cl_28539,cl_28540,cl_28541,cl_28542,cl_28543,cl_28544,cl_28545,cl_28546,cl_28547,cl_28548,cl_28549,cl_28550,cl_28551,cl_28552,cl_28553,cl_28554,cl_28555,cl_28556,cl_28557,cl_28558,cl_28559,cl_28560,cl_28561,cl_28562,cl_28563,cl_28564,cl_28565,cl_28566,cl_28567,cl_28568,cl_28569,cl_28570,cl_28571,cl_28572,cl_28573,cl_28574,cl_28575,cl_28576,cl_28577,cl_28578,cl_28579,cl_28580,cl_28581,cl_28582,cl_28583,cl_28584,cl_28585,cl_28586,cl_28587,cl_28588,cl_28589,cl_28590,cl_28591,cl_28592,cl_28593,cl_28594,cl_28595,cl_28596,cl_28597,cl_28598,cl_28599,cl_28600,cl_28601,cl_28602,cl_28604,cl_28605,cl_28606,cl_28607,cl_28608,cl_28609,cl_28610,cl_28612,cl_28613,cl_28614,cl_28615,cl_28616,cl_28617,cl_28618,cl_28619,cl_28620,cl_28621,cl_28622,cl_28623,cl_28624,cl_28625,cl_28626,cl_28627,cl_28628,cl_28629,cl_28630,cl_28631,cl_28632,cl_28633,cl_28634,cl_28635,cl_28636,cl_28637,cl_28638,cl_28639,cl_28640,cl_28641,cl_28642,cl_28643,cl_28644,cl_28645,cl_28646,cl_28647,cl_28648,cl_28649,cl_28650,cl_28651,cl_28652,cl_28653,cl_28654,cl_28655,cl_28656,cl_28658,cl_28659,cl_28660,cl_28661,cl_28662,cl_28663,cl_28664,cl_28665,cl_28667,cl_28668,cl_28670,cl_28672,cl_28673,cl_28674,cl_28675,cl_28676,cl_28677,cl_28680,cl_28681,cl_28682,cl_28684,cl_28686,cl_28687,cl_28688,cl_28689,cl_28690,cl_28691,cl_28692,cl_28693,cl_28694,cl_28695,cl_28696,cl_28697,cl_28698,cl_28699,cl_28700,cl_28701,cl_28702,cl_28703,cl_28704,cl_28705,cl_28706,cl_28707,cl_28708,cl_28709,cl_28710,cl_28711,cl_28712,cl_28713,cl_28714,cl_28715,cl_28716,cl_28717,cl_28718,cl_28719,cl_28720,cl_28721,cl_28722,cl_28723,cl_28724,cl_28725,cl_28726,cl_28727,cl_28728,cl_28729,cl_28730,cl_28731,cl_28732,cl_28733,cl_28734,cl_28735,cl_28736,cl_28737,cl_28738,cl_28739,cl_28740,cl_28741,cl_28742,cl_28743,cl_28744,cl_28745,cl_28746,cl_28747,cl_28748,cl_28749,cl_28750,cl_28751,cl_28752,cl_28753,cl_28754,cl_28755,cl_28756,cl_28757,cl_28758,cl_28759,cl_28760,cl_28761,cl_28762,cl_28763,cl_28764,cl_28765,cl_28766,cl_28767,cl_28768,cl_28769,cl_28770,cl_28771,cl_28772,cl_28773,cl_28774,cl_28775,cl_28776,cl_28777,cl_28778,cl_28780,cl_28781,cl_28782,cl_28783,cl_28784,cl_28785,cl_28786,cl_28787,cl_28788,cl_28790,cl_28791,cl_28792,cl_28793,cl_28794,cl_28796,cl_28798,cl_28799,cl_28800,cl_28801,cl_28802,cl_28803,cl_28804,cl_28805,cl_28806,cl_28807,cl_28808,cl_28809,cl_28810,cl_28811,cl_28812,cl_28813,cl_28814,cl_28815,cl_28816,cl_28817,cl_28818,cl_28819,cl_28820,cl_28821,cl_28822,cl_28823,cl_28824,cl_28825,cl_28826,cl_28827,cl_28828,cl_28829,cl_28830,cl_28831,cl_28832,cl_28833,cl_28834,cl_28835,cl_28836,cl_28837,cl_28838,cl_28839,cl_28840,cl_28841,cl_28842,cl_28843,cl_28844,cl_28845,cl_28846,cl_28847,cl_28848,cl_28849,cl_28850,cl_28851,cl_28852,cl_28853,cl_28854]
theorem chunk_sound012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk012, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_28337 v h) (hints_cons _ _ _ (der_28339 v h) (hints_cons _ _ _ (der_28340 v h) (hints_cons _ _ _ (der_28341 v h) (hints_cons _ _ _ (der_28342 v h) (hints_cons _ _ _ (der_28343 v h) (hints_cons _ _ _ (der_28344 v h) (hints_cons _ _ _ (der_28345 v h) (hints_cons _ _ _ (der_28346 v h) (hints_cons _ _ _ (der_28347 v h) (hints_cons _ _ _ (der_28348 v h) (hints_cons _ _ _ (der_28349 v h) (hints_cons _ _ _ (der_28350 v h) (hints_cons _ _ _ (der_28351 v h) (hints_cons _ _ _ (der_28352 v h) (hints_cons _ _ _ (der_28353 v h) (hints_cons _ _ _ (der_28354 v h) (hints_cons _ _ _ (der_28355 v h) (hints_cons _ _ _ (der_28356 v h) (hints_cons _ _ _ (der_28357 v h) (hints_cons _ _ _ (der_28358 v h) (hints_cons _ _ _ (der_28359 v h) (hints_cons _ _ _ (der_28360 v h) (hints_cons _ _ _ (der_28361 v h) (hints_cons _ _ _ (der_28362 v h) (hints_cons _ _ _ (der_28363 v h) (hints_cons _ _ _ (der_28364 v h) (hints_cons _ _ _ (der_28365 v h) (hints_cons _ _ _ (der_28366 v h) (hints_cons _ _ _ (der_28367 v h) (hints_cons _ _ _ (der_28368 v h) (hints_cons _ _ _ (der_28369 v h) (hints_cons _ _ _ (der_28370 v h) (hints_cons _ _ _ (der_28371 v h) (hints_cons _ _ _ (der_28372 v h) (hints_cons _ _ _ (der_28373 v h) (hints_cons _ _ _ (der_28374 v h) (hints_cons _ _ _ (der_28375 v h) (hints_cons _ _ _ (der_28376 v h) (hints_cons _ _ _ (der_28377 v h) (hints_cons _ _ _ (der_28378 v h) (hints_cons _ _ _ (der_28379 v h) (hints_cons _ _ _ (der_28380 v h) (hints_cons _ _ _ (der_28381 v h) (hints_cons _ _ _ (der_28382 v h) (hints_cons _ _ _ (der_28383 v h) (hints_cons _ _ _ (der_28384 v h) (hints_cons _ _ _ (der_28385 v h) (hints_cons _ _ _ (der_28386 v h) (hints_cons _ _ _ (der_28387 v h) (hints_cons _ _ _ (der_28388 v h) (hints_cons _ _ _ (der_28389 v h) (hints_cons _ _ _ (der_28390 v h) (hints_cons _ _ _ (der_28391 v h) (hints_cons _ _ _ (der_28392 v h) (hints_cons _ _ _ (der_28393 v h) (hints_cons _ _ _ (der_28394 v h) (hints_cons _ _ _ (der_28395 v h) (hints_cons _ _ _ (der_28397 v h) (hints_cons _ _ _ (der_28398 v h) (hints_cons _ _ _ (der_28399 v h) (hints_cons _ _ _ (der_28400 v h) (hints_cons _ _ _ (der_28401 v h) (hints_cons _ _ _ (der_28402 v h) (hints_cons _ _ _ (der_28403 v h) (hints_cons _ _ _ (der_28404 v h) (hints_cons _ _ _ (der_28405 v h) (hints_cons _ _ _ (der_28406 v h) (hints_cons _ _ _ (der_28407 v h) (hints_cons _ _ _ (der_28408 v h) (hints_cons _ _ _ (der_28409 v h) (hints_cons _ _ _ (der_28410 v h) (hints_cons _ _ _ (der_28411 v h) (hints_cons _ _ _ (der_28412 v h) (hints_cons _ _ _ (der_28413 v h) (hints_cons _ _ _ (der_28414 v h) (hints_cons _ _ _ (der_28415 v h) (hints_cons _ _ _ (der_28416 v h) (hints_cons _ _ _ (der_28417 v h) (hints_cons _ _ _ (der_28418 v h) (hints_cons _ _ _ (der_28419 v h) (hints_cons _ _ _ (der_28420 v h) (hints_cons _ _ _ (der_28421 v h) (hints_cons _ _ _ (der_28422 v h) (hints_cons _ _ _ (der_28423 v h) (hints_cons _ _ _ (der_28424 v h) (hints_cons _ _ _ (der_28425 v h) (hints_cons _ _ _ (der_28426 v h) (hints_cons _ _ _ (der_28427 v h) (hints_cons _ _ _ (der_28428 v h) (hints_cons _ _ _ (der_28429 v h) (hints_cons _ _ _ (der_28430 v h) (hints_cons _ _ _ (der_28431 v h) (hints_cons _ _ _ (der_28432 v h) (hints_cons _ _ _ (der_28434 v h) (hints_cons _ _ _ (der_28435 v h) (hints_cons _ _ _ (der_28436 v h) (hints_cons _ _ _ (der_28437 v h) (hints_cons _ _ _ (der_28438 v h) (hints_cons _ _ _ (der_28439 v h) (hints_cons _ _ _ (der_28440 v h) (hints_cons _ _ _ (der_28441 v h) (hints_cons _ _ _ (der_28442 v h) (hints_cons _ _ _ (der_28443 v h) (hints_cons _ _ _ (der_28444 v h) (hints_cons _ _ _ (der_28445 v h) (hints_cons _ _ _ (der_28446 v h) (hints_cons _ _ _ (der_28447 v h) (hints_cons _ _ _ (der_28448 v h) (hints_cons _ _ _ (der_28449 v h) (hints_cons _ _ _ (der_28450 v h) (hints_cons _ _ _ (der_28451 v h) (hints_cons _ _ _ (der_28452 v h) (hints_cons _ _ _ (der_28453 v h) (hints_cons _ _ _ (der_28454 v h) (hints_cons _ _ _ (der_28455 v h) (hints_cons _ _ _ (der_28456 v h) (hints_cons _ _ _ (der_28457 v h) (hints_cons _ _ _ (der_28458 v h) (hints_cons _ _ _ (der_28460 v h) (hints_cons _ _ _ (der_28461 v h) (hints_cons _ _ _ (der_28462 v h) (hints_cons _ _ _ (der_28463 v h) (hints_cons _ _ _ (der_28464 v h) (hints_cons _ _ _ (der_28465 v h) (hints_cons _ _ _ (der_28466 v h) (hints_cons _ _ _ (der_28467 v h) (hints_cons _ _ _ (der_28468 v h) (hints_cons _ _ _ (der_28469 v h) (hints_cons _ _ _ (der_28470 v h) (hints_cons _ _ _ (der_28471 v h) (hints_cons _ _ _ (der_28472 v h) (hints_cons _ _ _ (der_28473 v h) (hints_cons _ _ _ (der_28474 v h) (hints_cons _ _ _ (der_28475 v h) (hints_cons _ _ _ (der_28476 v h) (hints_cons _ _ _ (der_28477 v h) (hints_cons _ _ _ (der_28478 v h) (hints_cons _ _ _ (der_28479 v h) (hints_cons _ _ _ (der_28480 v h) (hints_cons _ _ _ (der_28481 v h) (hints_cons _ _ _ (der_28482 v h) (hints_cons _ _ _ (der_28483 v h) (hints_cons _ _ _ (der_28484 v h) (hints_cons _ _ _ (der_28485 v h) (hints_cons _ _ _ (der_28486 v h) (hints_cons _ _ _ (der_28487 v h) (hints_cons _ _ _ (der_28488 v h) (hints_cons _ _ _ (der_28489 v h) (hints_cons _ _ _ (der_28490 v h) (hints_cons _ _ _ (der_28491 v h) (hints_cons _ _ _ (der_28492 v h) (hints_cons _ _ _ (der_28493 v h) (hints_cons _ _ _ (der_28494 v h) (hints_cons _ _ _ (der_28495 v h) (hints_cons _ _ _ (der_28496 v h) (hints_cons _ _ _ (der_28497 v h) (hints_cons _ _ _ (der_28498 v h) (hints_cons _ _ _ (der_28499 v h) (hints_cons _ _ _ (der_28500 v h) (hints_cons _ _ _ (der_28501 v h) (hints_cons _ _ _ (der_28502 v h) (hints_cons _ _ _ (der_28503 v h) (hints_cons _ _ _ (der_28504 v h) (hints_cons _ _ _ (der_28505 v h) (hints_cons _ _ _ (der_28506 v h) (hints_cons _ _ _ (der_28507 v h) (hints_cons _ _ _ (der_28508 v h) (hints_cons _ _ _ (der_28509 v h) (hints_cons _ _ _ (der_28510 v h) (hints_cons _ _ _ (der_28511 v h) (hints_cons _ _ _ (der_28512 v h) (hints_cons _ _ _ (der_28513 v h) (hints_cons _ _ _ (der_28514 v h) (hints_cons _ _ _ (der_28515 v h) (hints_cons _ _ _ (der_28516 v h) (hints_cons _ _ _ (der_28517 v h) (hints_cons _ _ _ (der_28518 v h) (hints_cons _ _ _ (der_28519 v h) (hints_cons _ _ _ (der_28520 v h) (hints_cons _ _ _ (der_28521 v h) (hints_cons _ _ _ (der_28522 v h) (hints_cons _ _ _ (der_28523 v h) (hints_cons _ _ _ (der_28524 v h) (hints_cons _ _ _ (der_28525 v h) (hints_cons _ _ _ (der_28526 v h) (hints_cons _ _ _ (der_28527 v h) (hints_cons _ _ _ (der_28528 v h) (hints_cons _ _ _ (der_28529 v h) (hints_cons _ _ _ (der_28530 v h) (hints_cons _ _ _ (der_28531 v h) (hints_cons _ _ _ (der_28532 v h) (hints_cons _ _ _ (der_28533 v h) (hints_cons _ _ _ (der_28534 v h) (hints_cons _ _ _ (der_28535 v h) (hints_cons _ _ _ (der_28536 v h) (hints_cons _ _ _ (der_28537 v h) (hints_cons _ _ _ (der_28538 v h) (hints_cons _ _ _ (der_28539 v h) (hints_cons _ _ _ (der_28540 v h) (hints_cons _ _ _ (der_28541 v h) (hints_cons _ _ _ (der_28542 v h) (hints_cons _ _ _ (der_28543 v h) (hints_cons _ _ _ (der_28544 v h) (hints_cons _ _ _ (der_28545 v h) (hints_cons _ _ _ (der_28546 v h) (hints_cons _ _ _ (der_28547 v h) (hints_cons _ _ _ (der_28548 v h) (hints_cons _ _ _ (der_28549 v h) (hints_cons _ _ _ (der_28550 v h) (hints_cons _ _ _ (der_28551 v h) (hints_cons _ _ _ (der_28552 v h) (hints_cons _ _ _ (der_28553 v h) (hints_cons _ _ _ (der_28554 v h) (hints_cons _ _ _ (der_28555 v h) (hints_cons _ _ _ (der_28556 v h) (hints_cons _ _ _ (der_28557 v h) (hints_cons _ _ _ (der_28558 v h) (hints_cons _ _ _ (der_28559 v h) (hints_cons _ _ _ (der_28560 v h) (hints_cons _ _ _ (der_28561 v h) (hints_cons _ _ _ (der_28562 v h) (hints_cons _ _ _ (der_28563 v h) (hints_cons _ _ _ (der_28564 v h) (hints_cons _ _ _ (der_28565 v h) (hints_cons _ _ _ (der_28566 v h) (hints_cons _ _ _ (der_28567 v h) (hints_cons _ _ _ (der_28568 v h) (hints_cons _ _ _ (der_28569 v h) (hints_cons _ _ _ (der_28570 v h) (hints_cons _ _ _ (der_28571 v h) (hints_cons _ _ _ (der_28572 v h) (hints_cons _ _ _ (der_28573 v h) (hints_cons _ _ _ (der_28574 v h) (hints_cons _ _ _ (der_28575 v h) (hints_cons _ _ _ (der_28576 v h) (hints_cons _ _ _ (der_28577 v h) (hints_cons _ _ _ (der_28578 v h) (hints_cons _ _ _ (der_28579 v h) (hints_cons _ _ _ (der_28580 v h) (hints_cons _ _ _ (der_28581 v h) (hints_cons _ _ _ (der_28582 v h) (hints_cons _ _ _ (der_28583 v h) (hints_cons _ _ _ (der_28584 v h) (hints_cons _ _ _ (der_28585 v h) (hints_cons _ _ _ (der_28586 v h) (hints_cons _ _ _ (der_28587 v h) (hints_cons _ _ _ (der_28588 v h) (hints_cons _ _ _ (der_28589 v h) (hints_cons _ _ _ (der_28590 v h) (hints_cons _ _ _ (der_28591 v h) (hints_cons _ _ _ (der_28592 v h) (hints_cons _ _ _ (der_28593 v h) (hints_cons _ _ _ (der_28594 v h) (hints_cons _ _ _ (der_28595 v h) (hints_cons _ _ _ (der_28596 v h) (hints_cons _ _ _ (der_28597 v h) (hints_cons _ _ _ (der_28598 v h) (hints_cons _ _ _ (der_28599 v h) (hints_cons _ _ _ (der_28600 v h) (hints_cons _ _ _ (der_28601 v h) (hints_cons _ _ _ (der_28602 v h) (hints_cons _ _ _ (der_28604 v h) (hints_cons _ _ _ (der_28605 v h) (hints_cons _ _ _ (der_28606 v h) (hints_cons _ _ _ (der_28607 v h) (hints_cons _ _ _ (der_28608 v h) (hints_cons _ _ _ (der_28609 v h) (hints_cons _ _ _ (der_28610 v h) (hints_cons _ _ _ (der_28612 v h) (hints_cons _ _ _ (der_28613 v h) (hints_cons _ _ _ (der_28614 v h) (hints_cons _ _ _ (der_28615 v h) (hints_cons _ _ _ (der_28616 v h) (hints_cons _ _ _ (der_28617 v h) (hints_cons _ _ _ (der_28618 v h) (hints_cons _ _ _ (der_28619 v h) (hints_cons _ _ _ (der_28620 v h) (hints_cons _ _ _ (der_28621 v h) (hints_cons _ _ _ (der_28622 v h) (hints_cons _ _ _ (der_28623 v h) (hints_cons _ _ _ (der_28624 v h) (hints_cons _ _ _ (der_28625 v h) (hints_cons _ _ _ (der_28626 v h) (hints_cons _ _ _ (der_28627 v h) (hints_cons _ _ _ (der_28628 v h) (hints_cons _ _ _ (der_28629 v h) (hints_cons _ _ _ (der_28630 v h) (hints_cons _ _ _ (der_28631 v h) (hints_cons _ _ _ (der_28632 v h) (hints_cons _ _ _ (der_28633 v h) (hints_cons _ _ _ (der_28634 v h) (hints_cons _ _ _ (der_28635 v h) (hints_cons _ _ _ (der_28636 v h) (hints_cons _ _ _ (der_28637 v h) (hints_cons _ _ _ (der_28638 v h) (hints_cons _ _ _ (der_28639 v h) (hints_cons _ _ _ (der_28640 v h) (hints_cons _ _ _ (der_28641 v h) (hints_cons _ _ _ (der_28642 v h) (hints_cons _ _ _ (der_28643 v h) (hints_cons _ _ _ (der_28644 v h) (hints_cons _ _ _ (der_28645 v h) (hints_cons _ _ _ (der_28646 v h) (hints_cons _ _ _ (der_28647 v h) (hints_cons _ _ _ (der_28648 v h) (hints_cons _ _ _ (der_28649 v h) (hints_cons _ _ _ (der_28650 v h) (hints_cons _ _ _ (der_28651 v h) (hints_cons _ _ _ (der_28652 v h) (hints_cons _ _ _ (der_28653 v h) (hints_cons _ _ _ (der_28654 v h) (hints_cons _ _ _ (der_28655 v h) (hints_cons _ _ _ (der_28656 v h) (hints_cons _ _ _ (der_28658 v h) (hints_cons _ _ _ (der_28659 v h) (hints_cons _ _ _ (der_28660 v h) (hints_cons _ _ _ (der_28661 v h) (hints_cons _ _ _ (der_28662 v h) (hints_cons _ _ _ (der_28663 v h) (hints_cons _ _ _ (der_28664 v h) (hints_cons _ _ _ (der_28665 v h) (hints_cons _ _ _ (der_28667 v h) (hints_cons _ _ _ (der_28668 v h) (hints_cons _ _ _ (der_28670 v h) (hints_cons _ _ _ (der_28672 v h) (hints_cons _ _ _ (der_28673 v h) (hints_cons _ _ _ (der_28674 v h) (hints_cons _ _ _ (der_28675 v h) (hints_cons _ _ _ (der_28676 v h) (hints_cons _ _ _ (der_28677 v h) (hints_cons _ _ _ (der_28680 v h) (hints_cons _ _ _ (der_28681 v h) (hints_cons _ _ _ (der_28682 v h) (hints_cons _ _ _ (der_28684 v h) (hints_cons _ _ _ (der_28686 v h) (hints_cons _ _ _ (der_28687 v h) (hints_cons _ _ _ (der_28688 v h) (hints_cons _ _ _ (der_28689 v h) (hints_cons _ _ _ (der_28690 v h) (hints_cons _ _ _ (der_28691 v h) (hints_cons _ _ _ (der_28692 v h) (hints_cons _ _ _ (der_28693 v h) (hints_cons _ _ _ (der_28694 v h) (hints_cons _ _ _ (der_28695 v h) (hints_cons _ _ _ (der_28696 v h) (hints_cons _ _ _ (der_28697 v h) (hints_cons _ _ _ (der_28698 v h) (hints_cons _ _ _ (der_28699 v h) (hints_cons _ _ _ (der_28700 v h) (hints_cons _ _ _ (der_28701 v h) (hints_cons _ _ _ (der_28702 v h) (hints_cons _ _ _ (der_28703 v h) (hints_cons _ _ _ (der_28704 v h) (hints_cons _ _ _ (der_28705 v h) (hints_cons _ _ _ (der_28706 v h) (hints_cons _ _ _ (der_28707 v h) (hints_cons _ _ _ (der_28708 v h) (hints_cons _ _ _ (der_28709 v h) (hints_cons _ _ _ (der_28710 v h) (hints_cons _ _ _ (der_28711 v h) (hints_cons _ _ _ (der_28712 v h) (hints_cons _ _ _ (der_28713 v h) (hints_cons _ _ _ (der_28714 v h) (hints_cons _ _ _ (der_28715 v h) (hints_cons _ _ _ (der_28716 v h) (hints_cons _ _ _ (der_28717 v h) (hints_cons _ _ _ (der_28718 v h) (hints_cons _ _ _ (der_28719 v h) (hints_cons _ _ _ (der_28720 v h) (hints_cons _ _ _ (der_28721 v h) (hints_cons _ _ _ (der_28722 v h) (hints_cons _ _ _ (der_28723 v h) (hints_cons _ _ _ (der_28724 v h) (hints_cons _ _ _ (der_28725 v h) (hints_cons _ _ _ (der_28726 v h) (hints_cons _ _ _ (der_28727 v h) (hints_cons _ _ _ (der_28728 v h) (hints_cons _ _ _ (der_28729 v h) (hints_cons _ _ _ (der_28730 v h) (hints_cons _ _ _ (der_28731 v h) (hints_cons _ _ _ (der_28732 v h) (hints_cons _ _ _ (der_28733 v h) (hints_cons _ _ _ (der_28734 v h) (hints_cons _ _ _ (der_28735 v h) (hints_cons _ _ _ (der_28736 v h) (hints_cons _ _ _ (der_28737 v h) (hints_cons _ _ _ (der_28738 v h) (hints_cons _ _ _ (der_28739 v h) (hints_cons _ _ _ (der_28740 v h) (hints_cons _ _ _ (der_28741 v h) (hints_cons _ _ _ (der_28742 v h) (hints_cons _ _ _ (der_28743 v h) (hints_cons _ _ _ (der_28744 v h) (hints_cons _ _ _ (der_28745 v h) (hints_cons _ _ _ (der_28746 v h) (hints_cons _ _ _ (der_28747 v h) (hints_cons _ _ _ (der_28748 v h) (hints_cons _ _ _ (der_28749 v h) (hints_cons _ _ _ (der_28750 v h) (hints_cons _ _ _ (der_28751 v h) (hints_cons _ _ _ (der_28752 v h) (hints_cons _ _ _ (der_28753 v h) (hints_cons _ _ _ (der_28754 v h) (hints_cons _ _ _ (der_28755 v h) (hints_cons _ _ _ (der_28756 v h) (hints_cons _ _ _ (der_28757 v h) (hints_cons _ _ _ (der_28758 v h) (hints_cons _ _ _ (der_28759 v h) (hints_cons _ _ _ (der_28760 v h) (hints_cons _ _ _ (der_28761 v h) (hints_cons _ _ _ (der_28762 v h) (hints_cons _ _ _ (der_28763 v h) (hints_cons _ _ _ (der_28764 v h) (hints_cons _ _ _ (der_28765 v h) (hints_cons _ _ _ (der_28766 v h) (hints_cons _ _ _ (der_28767 v h) (hints_cons _ _ _ (der_28768 v h) (hints_cons _ _ _ (der_28769 v h) (hints_cons _ _ _ (der_28770 v h) (hints_cons _ _ _ (der_28771 v h) (hints_cons _ _ _ (der_28772 v h) (hints_cons _ _ _ (der_28773 v h) (hints_cons _ _ _ (der_28774 v h) (hints_cons _ _ _ (der_28775 v h) (hints_cons _ _ _ (der_28776 v h) (hints_cons _ _ _ (der_28777 v h) (hints_cons _ _ _ (der_28778 v h) (hints_cons _ _ _ (der_28780 v h) (hints_cons _ _ _ (der_28781 v h) (hints_cons _ _ _ (der_28782 v h) (hints_cons _ _ _ (der_28783 v h) (hints_cons _ _ _ (der_28784 v h) (hints_cons _ _ _ (der_28785 v h) (hints_cons _ _ _ (der_28786 v h) (hints_cons _ _ _ (der_28787 v h) (hints_cons _ _ _ (der_28788 v h) (hints_cons _ _ _ (der_28790 v h) (hints_cons _ _ _ (der_28791 v h) (hints_cons _ _ _ (der_28792 v h) (hints_cons _ _ _ (der_28793 v h) (hints_cons _ _ _ (der_28794 v h) (hints_cons _ _ _ (der_28796 v h) (hints_cons _ _ _ (der_28798 v h) (hints_cons _ _ _ (der_28799 v h) (hints_cons _ _ _ (der_28800 v h) (hints_cons _ _ _ (der_28801 v h) (hints_cons _ _ _ (der_28802 v h) (hints_cons _ _ _ (der_28803 v h) (hints_cons _ _ _ (der_28804 v h) (hints_cons _ _ _ (der_28805 v h) (hints_cons _ _ _ (der_28806 v h) (hints_cons _ _ _ (der_28807 v h) (hints_cons _ _ _ (der_28808 v h) (hints_cons _ _ _ (der_28809 v h) (hints_cons _ _ _ (der_28810 v h) (hints_cons _ _ _ (der_28811 v h) (hints_cons _ _ _ (der_28812 v h) (hints_cons _ _ _ (der_28813 v h) (hints_cons _ _ _ (der_28814 v h) (hints_cons _ _ _ (der_28815 v h) (hints_cons _ _ _ (der_28816 v h) (hints_cons _ _ _ (der_28817 v h) (hints_cons _ _ _ (der_28818 v h) (hints_cons _ _ _ (der_28819 v h) (hints_cons _ _ _ (der_28820 v h) (hints_cons _ _ _ (der_28821 v h) (hints_cons _ _ _ (der_28822 v h) (hints_cons _ _ _ (der_28823 v h) (hints_cons _ _ _ (der_28824 v h) (hints_cons _ _ _ (der_28825 v h) (hints_cons _ _ _ (der_28826 v h) (hints_cons _ _ _ (der_28827 v h) (hints_cons _ _ _ (der_28828 v h) (hints_cons _ _ _ (der_28829 v h) (hints_cons _ _ _ (der_28830 v h) (hints_cons _ _ _ (der_28831 v h) (hints_cons _ _ _ (der_28832 v h) (hints_cons _ _ _ (der_28833 v h) (hints_cons _ _ _ (der_28834 v h) (hints_cons _ _ _ (der_28835 v h) (hints_cons _ _ _ (der_28836 v h) (hints_cons _ _ _ (der_28837 v h) (hints_cons _ _ _ (der_28838 v h) (hints_cons _ _ _ (der_28839 v h) (hints_cons _ _ _ (der_28840 v h) (hints_cons _ _ _ (der_28841 v h) (hints_cons _ _ _ (der_28842 v h) (hints_cons _ _ _ (der_28843 v h) (hints_cons _ _ _ (der_28844 v h) (hints_cons _ _ _ (der_28845 v h) (hints_cons _ _ _ (der_28846 v h) (hints_cons _ _ _ (der_28847 v h) (hints_cons _ _ _ (der_28848 v h) (hints_cons _ _ _ (der_28849 v h) (hints_cons _ _ _ (der_28850 v h) (hints_cons _ _ _ (der_28851 v h) (hints_cons _ _ _ (der_28852 v h) (hints_cons _ _ _ (der_28853 v h) (hints_cons _ _ _ (der_28854 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix012 := prefix011 ++ chunk012
theorem prefix_sound012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix012, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound011 v h c hc
  · exact chunk_sound012 v h c hc
end Percolation.NReplay
