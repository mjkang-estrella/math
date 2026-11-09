import NReplay009
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_27304 : CNF.NClause := [(55,false),(80,true),(24,false),(63,false),(76,true),(84,false),(91,false)]
theorem der_27304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27304 :=
  CNF.rup_sound cl_27304 [cl_7069,cl_27300] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7069 v h) (hints_cons _ _ _ (der_27300 v h) (by intro d hd; cases hd)))
def cl_27305 : CNF.NClause := [(55,false),(24,true),(63,false),(76,true),(67,true),(84,false),(91,false)]
theorem der_27305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27305 :=
  CNF.rup_sound cl_27305 [cl_7070,cl_27290] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7070 v h) (hints_cons _ _ _ (der_27290 v h) (by intro d hd; cases hd)))
def cl_27306 : CNF.NClause := [(55,false),(80,true),(24,false),(76,true),(63,true),(84,false),(91,false)]
theorem der_27306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27306 :=
  CNF.rup_sound cl_27306 [cl_7071,cl_27302] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7071 v h) (hints_cons _ _ _ (der_27302 v h) (by intro d hd; cases hd)))
def cl_27307 : CNF.NClause := [(55,false),(24,true),(67,true),(76,true),(63,true),(84,false),(91,false)]
theorem der_27307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27307 :=
  CNF.rup_sound cl_27307 [cl_7072,cl_27292] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7072 v h) (hints_cons _ _ _ (der_27292 v h) (by intro d hd; cases hd)))
def cl_27308 : CNF.NClause := [(55,false),(84,true),(76,false),(67,false),(91,false),(80,false),(63,false)]
theorem der_27308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27308 :=
  CNF.rup_sound cl_27308 [cl_7074,cl_7073] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7074 v h) (hints_cons _ _ _ (inp_7073 v h) (by intro d hd; cases hd)))
def cl_27309 : CNF.NClause := [(55,false),(84,true),(24,false),(80,false),(67,false),(76,false),(91,false)]
theorem der_27309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27309 :=
  CNF.rup_sound cl_27309 [cl_7075,cl_27308] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7075 v h) (hints_cons _ _ _ (der_27308 v h) (by intro d hd; cases hd)))
def cl_27310 : CNF.NClause := [(55,false),(84,true),(24,true),(76,false),(67,false),(80,false),(91,false)]
theorem der_27310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27310 :=
  CNF.rup_sound cl_27310 [cl_7076,cl_27308] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7076 v h) (hints_cons _ _ _ (der_27308 v h) (by intro d hd; cases hd)))
def cl_27311 : CNF.NClause := [(55,false),(84,true),(24,false),(63,false),(91,false),(76,false),(80,false)]
theorem der_27311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27311 :=
  CNF.rup_sound cl_27311 [cl_7077,cl_27308] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7077 v h) (hints_cons _ _ _ (der_27308 v h) (by intro d hd; cases hd)))
def cl_27312 : CNF.NClause := [(55,false),(84,true),(24,true),(63,false),(76,false),(80,false),(91,false)]
theorem der_27312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27312 :=
  CNF.rup_sound cl_27312 [cl_7078,cl_27308] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7078 v h) (hints_cons _ _ _ (der_27308 v h) (by intro d hd; cases hd)))
def cl_27313 : CNF.NClause := [(55,false),(84,true),(24,false),(63,true),(80,false),(76,false),(91,false)]
theorem der_27313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27313 :=
  CNF.rup_sound cl_27313 [cl_7079,cl_27309] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7079 v h) (hints_cons _ _ _ (der_27309 v h) (by intro d hd; cases hd)))
def cl_27314 : CNF.NClause := [(55,false),(84,true),(67,true),(63,true),(80,false),(76,false),(91,false)]
theorem der_27314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27314 :=
  CNF.rup_sound cl_27314 [cl_7080,cl_27313] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7080 v h) (hints_cons _ _ _ (der_27313 v h) (by intro d hd; cases hd)))
def cl_27315 : CNF.NClause := [(55,false),(24,false),(76,true),(63,false),(67,false),(80,false),(91,false)]
theorem der_27315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27315 :=
  CNF.rup_sound cl_27315 [cl_7081,cl_27286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7081 v h) (hints_cons _ _ _ (der_27286 v h) (by intro d hd; cases hd)))
def cl_27316 : CNF.NClause := [(55,false),(24,true),(67,false),(63,false),(76,true),(80,false),(91,false)]
theorem der_27316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27316 :=
  CNF.rup_sound cl_27316 [cl_7082,cl_27286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7082 v h) (hints_cons _ _ _ (der_27286 v h) (by intro d hd; cases hd)))
def cl_27317 : CNF.NClause := [(55,false),(84,true),(24,false),(80,false),(67,false),(63,true),(91,false)]
theorem der_27317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27317 :=
  CNF.rup_sound cl_27317 [cl_7083,cl_27313] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7083 v h) (hints_cons _ _ _ (der_27313 v h) (by intro d hd; cases hd)))
def cl_27318 : CNF.NClause := [(55,false),(24,true),(63,true),(76,true),(67,false),(80,false),(91,false)]
theorem der_27318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27318 :=
  CNF.rup_sound cl_27318 [cl_7084,cl_27288] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7084 v h) (hints_cons _ _ _ (der_27288 v h) (by intro d hd; cases hd)))
def cl_27319 : CNF.NClause := [(55,false),(24,false),(63,false),(76,true),(67,true),(80,false),(91,false)]
theorem der_27319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27319 :=
  CNF.rup_sound cl_27319 [cl_7085,cl_27289] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7085 v h) (hints_cons _ _ _ (der_27289 v h) (by intro d hd; cases hd)))
def cl_27320 : CNF.NClause := [(55,false),(84,true),(63,false),(76,true),(67,true),(80,false),(91,false)]
theorem der_27320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27320 :=
  CNF.rup_sound cl_27320 [cl_7086,cl_27319] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7086 v h) (hints_cons _ _ _ (der_27319 v h) (by intro d hd; cases hd)))
def cl_27321 : CNF.NClause := [(55,false),(84,true),(24,false),(67,true),(63,true),(80,false),(91,false)]
theorem der_27321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27321 :=
  CNF.rup_sound cl_27321 [cl_7087,cl_27313] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7087 v h) (hints_cons _ _ _ (der_27313 v h) (by intro d hd; cases hd)))
def cl_27322 : CNF.NClause := [(55,false),(84,true),(24,true),(76,true),(63,true),(80,false),(91,false)]
theorem der_27322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27322 :=
  CNF.rup_sound cl_27322 [cl_7088,cl_27318] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7088 v h) (hints_cons _ _ _ (der_27318 v h) (by intro d hd; cases hd)))
def cl_27323 : CNF.NClause := [(55,false),(24,false),(67,false),(76,false),(63,false),(80,true),(91,false)]
theorem der_27323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27323 :=
  CNF.rup_sound cl_27323 [cl_7089,cl_7057] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7089 v h) (hints_cons _ _ _ (inp_7057 v h) (by intro d hd; cases hd)))
def cl_27324 : CNF.NClause := [(55,false),(84,true),(24,true),(67,false),(63,false),(76,false),(91,false)]
theorem der_27324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27324 :=
  CNF.rup_sound cl_27324 [cl_7090,cl_27308] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7090 v h) (hints_cons _ _ _ (der_27308 v h) (by intro d hd; cases hd)))
def cl_27325 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,false),(80,true),(91,false)]
theorem der_27325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27325 :=
  CNF.rup_sound cl_27325 [cl_7091,cl_27295] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7091 v h) (hints_cons _ _ _ (der_27295 v h) (by intro d hd; cases hd)))
def cl_27326 : CNF.NClause := [(55,false),(24,true),(63,true),(76,false),(67,false),(80,true),(91,false)]
theorem der_27326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27326 :=
  CNF.rup_sound cl_27326 [cl_7092,cl_27295] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7092 v h) (hints_cons _ _ _ (der_27295 v h) (by intro d hd; cases hd)))
def cl_27327 : CNF.NClause := [(55,false),(24,false),(63,false),(76,false),(67,true),(80,true),(91,false)]
theorem der_27327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27327 :=
  CNF.rup_sound cl_27327 [cl_7093,cl_27297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7093 v h) (hints_cons _ _ _ (der_27297 v h) (by intro d hd; cases hd)))
def cl_27328 : CNF.NClause := [(55,false),(24,true),(63,false),(76,false),(67,true),(80,true),(91,false)]
theorem der_27328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27328 :=
  CNF.rup_sound cl_27328 [cl_7094,cl_27297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7094 v h) (hints_cons _ _ _ (der_27297 v h) (by intro d hd; cases hd)))
def cl_27329 : CNF.NClause := [(55,false),(84,true),(24,false),(67,true),(63,true),(76,false),(91,false)]
theorem der_27329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27329 :=
  CNF.rup_sound cl_27329 [cl_7095,cl_27313] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7095 v h) (hints_cons _ _ _ (der_27313 v h) (by intro d hd; cases hd)))
def cl_27330 : CNF.NClause := [(55,false),(84,true),(24,true),(67,true),(63,true),(76,false),(91,false)]
theorem der_27330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27330 :=
  CNF.rup_sound cl_27330 [cl_7096,cl_27314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7096 v h) (hints_cons _ _ _ (der_27314 v h) (by intro d hd; cases hd)))
def cl_27331 : CNF.NClause := [(55,false),(24,false),(67,false),(63,false),(76,true),(80,true),(91,false)]
theorem der_27331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27331 :=
  CNF.rup_sound cl_27331 [cl_7097,cl_27300] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7097 v h) (hints_cons _ _ _ (der_27300 v h) (by intro d hd; cases hd)))
def cl_27332 : CNF.NClause := [(55,false),(24,true),(76,true),(63,false),(67,false),(80,true),(91,false)]
theorem der_27332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27332 :=
  CNF.rup_sound cl_27332 [cl_7098,cl_27301] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7098 v h) (hints_cons _ _ _ (der_27301 v h) (by intro d hd; cases hd)))
def cl_27333 : CNF.NClause := [(55,false),(84,true),(24,false),(63,true),(67,false),(80,true),(91,false)]
theorem der_27333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27333 :=
  CNF.rup_sound cl_27333 [cl_7099,cl_27325] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7099 v h) (hints_cons _ _ _ (der_27325 v h) (by intro d hd; cases hd)))
def cl_27334 : CNF.NClause := [(55,false),(84,true),(24,true),(63,true),(76,true),(67,false),(91,false)]
theorem der_27334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27334 :=
  CNF.rup_sound cl_27334 [cl_7100,cl_27318] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7100 v h) (hints_cons _ _ _ (der_27318 v h) (by intro d hd; cases hd)))
def cl_27335 : CNF.NClause := [(55,false),(24,false),(63,false),(76,true),(67,true),(84,true),(91,false)]
theorem der_27335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27335 :=
  CNF.rup_sound cl_27335 [cl_7101,cl_27319] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7101 v h) (hints_cons _ _ _ (der_27319 v h) (by intro d hd; cases hd)))
def cl_27336 : CNF.NClause := [(55,false),(80,true),(63,false),(76,true),(67,true),(84,true),(91,false)]
theorem der_27336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27336 :=
  CNF.rup_sound cl_27336 [cl_7102,cl_27335] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7102 v h) (hints_cons _ _ _ (der_27335 v h) (by intro d hd; cases hd)))
def cl_27337 : CNF.NClause := [(55,false),(80,true),(24,false),(67,true),(76,true),(84,true),(91,false)]
theorem der_27337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27337 :=
  CNF.rup_sound cl_27337 [cl_7103,cl_27335] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7103 v h) (hints_cons _ _ _ (der_27335 v h) (by intro d hd; cases hd)))
def cl_27338 : CNF.NClause := [(55,false),(80,true),(24,true),(76,true),(63,true),(84,true),(91,false)]
theorem der_27338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27338 :=
  CNF.rup_sound cl_27338 [cl_7104,cl_27334] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7104 v h) (hints_cons _ _ _ (der_27334 v h) (by intro d hd; cases hd)))
def cl_27339 : CNF.NClause := [(55,false),(67,false),(24,true),(63,false),(76,false),(80,false),(84,false)]
theorem der_27339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27339 :=
  CNF.rup_sound cl_27339 [cl_7106,cl_7042] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7106 v h) (hints_cons _ _ _ (inp_7042 v h) (by intro d hd; cases hd)))
def cl_27340 : CNF.NClause := [(55,false),(67,false),(24,false),(63,true),(84,false),(76,false),(80,false)]
theorem der_27340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27340 :=
  CNF.rup_sound cl_27340 [cl_7107,cl_7043] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7107 v h) (hints_cons _ _ _ (inp_7043 v h) (by intro d hd; cases hd)))
def cl_27341 : CNF.NClause := [(55,false),(24,true),(67,false),(76,false),(80,false),(84,false),(63,true)]
theorem der_27341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27341 :=
  CNF.rup_sound cl_27341 [cl_7108,cl_27282] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7108 v h) (hints_cons _ _ _ (der_27282 v h) (by intro d hd; cases hd)))
def cl_27342 : CNF.NClause := [(55,false),(67,true),(24,false),(63,false),(76,false),(80,false),(84,false)]
theorem der_27342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27342 :=
  CNF.rup_sound cl_27342 [cl_7109,cl_7045] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7109 v h) (hints_cons _ _ _ (inp_7045 v h) (by intro d hd; cases hd)))
def cl_27343 : CNF.NClause := [(55,false),(67,true),(63,false),(76,false),(80,false),(84,false),(91,true)]
theorem der_27343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27343 :=
  CNF.rup_sound cl_27343 [cl_7110,cl_27342] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7110 v h) (hints_cons _ _ _ (der_27342 v h) (by intro d hd; cases hd)))
def cl_27344 : CNF.NClause := [(55,false),(76,false),(24,false),(67,true),(80,false),(84,false),(91,true)]
theorem der_27344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27344 :=
  CNF.rup_sound cl_27344 [cl_7111,cl_27342] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7111 v h) (hints_cons _ _ _ (der_27342 v h) (by intro d hd; cases hd)))
def cl_27345 : CNF.NClause := [(55,false),(24,true),(76,false),(67,true),(80,false),(84,false),(63,true)]
theorem der_27345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27345 :=
  CNF.rup_sound cl_27345 [cl_7112,cl_27285] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7112 v h) (hints_cons _ _ _ (der_27285 v h) (by intro d hd; cases hd)))
def cl_27346 : CNF.NClause := [(55,false),(24,false),(76,true),(63,false),(67,false),(84,false),(80,false)]
theorem der_27346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27346 :=
  CNF.rup_sound cl_27346 [cl_7113,cl_27286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7113 v h) (hints_cons _ _ _ (der_27286 v h) (by intro d hd; cases hd)))
def cl_27347 : CNF.NClause := [(55,false),(67,false),(24,true),(80,false),(84,false),(63,false),(76,true)]
theorem der_27347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27347 :=
  CNF.rup_sound cl_27347 [cl_7114,cl_27286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7114 v h) (hints_cons _ _ _ (der_27286 v h) (by intro d hd; cases hd)))
def cl_27348 : CNF.NClause := [(55,false),(24,false),(80,false),(67,false),(76,true),(84,false),(63,true)]
theorem der_27348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27348 :=
  CNF.rup_sound cl_27348 [cl_7115,cl_27287] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7115 v h) (hints_cons _ _ _ (der_27287 v h) (by intro d hd; cases hd)))
def cl_27349 : CNF.NClause := [(55,false),(24,true),(67,false),(76,true),(80,false),(84,false),(63,true)]
theorem der_27349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27349 :=
  CNF.rup_sound cl_27349 [cl_7116,cl_27318] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7116 v h) (hints_cons _ _ _ (der_27318 v h) (by intro d hd; cases hd)))
def cl_27350 : CNF.NClause := [(55,false),(67,true),(24,false),(63,false),(80,false),(76,true),(84,false)]
theorem der_27350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27350 :=
  CNF.rup_sound cl_27350 [cl_7117,cl_27289] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7117 v h) (hints_cons _ _ _ (der_27289 v h) (by intro d hd; cases hd)))
def cl_27351 : CNF.NClause := [(55,false),(67,true),(63,false),(76,true),(80,false),(84,false),(91,true)]
theorem der_27351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27351 :=
  CNF.rup_sound cl_27351 [cl_7118,cl_27350] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7118 v h) (hints_cons _ _ _ (der_27350 v h) (by intro d hd; cases hd)))
def cl_27352 : CNF.NClause := [(55,false),(80,false),(24,false),(67,true),(76,true),(84,false),(91,true)]
theorem der_27352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27352 :=
  CNF.rup_sound cl_27352 [cl_7119,cl_27350] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7119 v h) (hints_cons _ _ _ (der_27350 v h) (by intro d hd; cases hd)))
def cl_27353 : CNF.NClause := [(55,false),(80,false),(24,true),(67,true),(76,true),(63,true),(84,false)]
theorem der_27353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27353 :=
  CNF.rup_sound cl_27353 [cl_7120,cl_27292] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7120 v h) (hints_cons _ _ _ (der_27292 v h) (by intro d hd; cases hd)))
def cl_27354 : CNF.NClause := [(55,false),(24,false),(67,false),(76,false),(63,false),(84,false),(80,true)]
theorem der_27354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27354 :=
  CNF.rup_sound cl_27354 [cl_7121,cl_7057] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7121 v h) (hints_cons _ _ _ (inp_7057 v h) (by intro d hd; cases hd)))
def cl_27355 : CNF.NClause := [(55,false),(80,true),(24,true),(67,false),(76,false),(84,false),(63,false)]
theorem der_27355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27355 :=
  CNF.rup_sound cl_27355 [cl_7122,cl_27293] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7122 v h) (hints_cons _ _ _ (der_27293 v h) (by intro d hd; cases hd)))
def cl_27356 : CNF.NClause := [(55,false),(80,true),(24,false),(63,true),(67,false),(76,false),(84,false)]
theorem der_27356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27356 :=
  CNF.rup_sound cl_27356 [cl_7123,cl_27295] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7123 v h) (hints_cons _ _ _ (der_27295 v h) (by intro d hd; cases hd)))
def cl_27357 : CNF.NClause := [(55,false),(80,true),(24,true),(67,false),(76,false),(63,true),(84,false)]
theorem der_27357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27357 :=
  CNF.rup_sound cl_27357 [cl_7124,cl_27295] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7124 v h) (hints_cons _ _ _ (der_27295 v h) (by intro d hd; cases hd)))
def cl_27358 : CNF.NClause := [(55,false),(80,true),(24,false),(63,false),(76,false),(67,true),(84,false)]
theorem der_27358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27358 :=
  CNF.rup_sound cl_27358 [cl_7125,cl_27296] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7125 v h) (hints_cons _ _ _ (der_27296 v h) (by intro d hd; cases hd)))
def cl_27359 : CNF.NClause := [(55,false),(80,true),(24,true),(63,false),(76,false),(84,false),(91,true)]
theorem der_27359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27359 :=
  CNF.rup_sound cl_27359 [cl_7126,cl_27355] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7126 v h) (hints_cons _ _ _ (der_27355 v h) (by intro d hd; cases hd)))
def cl_27360 : CNF.NClause := [(55,false),(80,true),(24,false),(63,true),(76,false),(84,false),(91,true)]
theorem der_27360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27360 :=
  CNF.rup_sound cl_27360 [cl_7127,cl_27356] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7127 v h) (hints_cons _ _ _ (der_27356 v h) (by intro d hd; cases hd)))
def cl_27361 : CNF.NClause := [(55,false),(80,true),(24,true),(67,true),(63,true),(76,false),(84,false)]
theorem der_27361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27361 :=
  CNF.rup_sound cl_27361 [cl_7128,cl_27299] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7128 v h) (hints_cons _ _ _ (der_27299 v h) (by intro d hd; cases hd)))
def cl_27362 : CNF.NClause := [(55,false),(24,false),(84,false),(63,false),(67,false),(76,true),(80,true)]
theorem der_27362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27362 :=
  CNF.rup_sound cl_27362 [cl_7129,cl_27300] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7129 v h) (hints_cons _ _ _ (der_27300 v h) (by intro d hd; cases hd)))
def cl_27363 : CNF.NClause := [(55,false),(80,true),(24,true),(84,false),(91,true),(67,false),(63,false)]
theorem der_27363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27363 :=
  CNF.rup_sound cl_27363 [cl_7130,cl_27355] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7130 v h) (hints_cons _ _ _ (der_27355 v h) (by intro d hd; cases hd)))
def cl_27364 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,true),(84,false),(91,true)]
theorem der_27364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27364 :=
  CNF.rup_sound cl_27364 [cl_7131,cl_27348] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7131 v h) (hints_cons _ _ _ (der_27348 v h) (by intro d hd; cases hd)))
def cl_27365 : CNF.NClause := [(55,false),(80,true),(24,true),(67,false),(76,true),(63,true),(84,false)]
theorem der_27365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27365 :=
  CNF.rup_sound cl_27365 [cl_7132,cl_27303] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7132 v h) (hints_cons _ _ _ (der_27303 v h) (by intro d hd; cases hd)))
def cl_27366 : CNF.NClause := [(55,false),(24,false),(63,false),(76,true),(67,true),(84,false),(91,true)]
theorem der_27366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27366 :=
  CNF.rup_sound cl_27366 [cl_7133,cl_27350] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7133 v h) (hints_cons _ _ _ (der_27350 v h) (by intro d hd; cases hd)))
def cl_27367 : CNF.NClause := [(55,false),(80,true),(24,true),(63,false),(76,true),(67,true),(84,false)]
theorem der_27367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27367 :=
  CNF.rup_sound cl_27367 [cl_7134,cl_27305] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7134 v h) (hints_cons _ _ _ (der_27305 v h) (by intro d hd; cases hd)))
def cl_27368 : CNF.NClause := [(55,false),(80,true),(24,false),(67,true),(76,true),(84,false),(91,true)]
theorem der_27368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27368 :=
  CNF.rup_sound cl_27368 [cl_7135,cl_27366] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7135 v h) (hints_cons _ _ _ (der_27366 v h) (by intro d hd; cases hd)))
def cl_27369 : CNF.NClause := [(55,false),(80,true),(24,true),(67,true),(76,true),(84,false),(91,true)]
theorem der_27369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27369 :=
  CNF.rup_sound cl_27369 [cl_7136,cl_27367] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7136 v h) (hints_cons _ _ _ (der_27367 v h) (by intro d hd; cases hd)))
def cl_27370 : CNF.NClause := [(55,false),(24,false),(67,false),(76,false),(80,false),(63,false),(84,true)]
theorem der_27370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27370 :=
  CNF.rup_sound cl_27370 [cl_7137,cl_27308] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7137 v h) (hints_cons _ _ _ (der_27308 v h) (by intro d hd; cases hd)))
def cl_27371 : CNF.NClause := [(55,false),(84,true),(24,true),(67,false),(63,false),(80,false),(76,false)]
theorem der_27371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27371 :=
  CNF.rup_sound cl_27371 [cl_7138,cl_27308] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7138 v h) (hints_cons _ _ _ (der_27308 v h) (by intro d hd; cases hd)))
def cl_27372 : CNF.NClause := [(55,false),(84,true),(24,false),(80,false),(67,false),(76,false),(63,true)]
theorem der_27372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27372 :=
  CNF.rup_sound cl_27372 [cl_7139,cl_27313] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7139 v h) (hints_cons _ _ _ (der_27313 v h) (by intro d hd; cases hd)))
def cl_27373 : CNF.NClause := [(55,false),(24,true),(67,false),(76,false),(80,false),(63,true),(91,true)]
theorem der_27373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27373 :=
  CNF.rup_sound cl_27373 [cl_7140,cl_27341] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7140 v h) (hints_cons _ _ _ (der_27341 v h) (by intro d hd; cases hd)))
def cl_27374 : CNF.NClause := [(55,false),(84,true),(24,false),(63,false),(76,false),(80,false),(91,true)]
theorem der_27374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27374 :=
  CNF.rup_sound cl_27374 [cl_7141,cl_27370] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7141 v h) (hints_cons _ _ _ (der_27370 v h) (by intro d hd; cases hd)))
def cl_27375 : CNF.NClause := [(55,false),(84,true),(24,true),(63,false),(76,false),(80,false),(91,true)]
theorem der_27375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27375 :=
  CNF.rup_sound cl_27375 [cl_7142,cl_27371] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7142 v h) (hints_cons _ _ _ (der_27371 v h) (by intro d hd; cases hd)))
def cl_27376 : CNF.NClause := [(55,false),(84,true),(24,false),(67,true),(63,true),(80,false),(76,false)]
theorem der_27376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27376 :=
  CNF.rup_sound cl_27376 [cl_7143,cl_27313] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7143 v h) (hints_cons _ _ _ (der_27313 v h) (by intro d hd; cases hd)))
def cl_27377 : CNF.NClause := [(55,false),(24,true),(67,true),(63,true),(80,false),(76,false),(91,true)]
theorem der_27377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27377 :=
  CNF.rup_sound cl_27377 [cl_7144,cl_27345] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7144 v h) (hints_cons _ _ _ (der_27345 v h) (by intro d hd; cases hd)))
def cl_27379 : CNF.NClause := [(55,false),(84,true),(24,true),(67,false),(63,false),(80,false),(91,true)]
theorem der_27379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27379 :=
  CNF.rup_sound cl_27379 [cl_7146,cl_27371] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7146 v h) (hints_cons _ _ _ (der_27371 v h) (by intro d hd; cases hd)))
def cl_27380 : CNF.NClause := [(55,false),(24,false),(80,false),(67,false),(76,true),(63,true),(91,true)]
theorem der_27380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27380 :=
  CNF.rup_sound cl_27380 [cl_7147,cl_27348] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7147 v h) (hints_cons _ _ _ (der_27348 v h) (by intro d hd; cases hd)))
def cl_27381 : CNF.NClause := [(55,false),(84,true),(24,true),(67,false),(76,true),(80,false),(63,true)]
theorem der_27381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27381 :=
  CNF.rup_sound cl_27381 [cl_7148,cl_27318] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7148 v h) (hints_cons _ _ _ (der_27318 v h) (by intro d hd; cases hd)))
def cl_27382 : CNF.NClause := [(55,false),(24,false),(63,false),(76,true),(67,true),(80,false),(91,true)]
theorem der_27382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27382 :=
  CNF.rup_sound cl_27382 [cl_7149,cl_27350] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7149 v h) (hints_cons _ _ _ (der_27350 v h) (by intro d hd; cases hd)))
def cl_27383 : CNF.NClause := [(55,false),(84,true),(24,true),(63,false),(76,true),(67,true),(80,false)]
theorem der_27383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27383 :=
  CNF.rup_sound cl_27383 [cl_7150,cl_27320] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7150 v h) (hints_cons _ _ _ (der_27320 v h) (by intro d hd; cases hd)))
def cl_27384 : CNF.NClause := [(55,false),(84,true),(24,false),(67,true),(63,true),(80,false),(91,true)]
theorem der_27384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27384 :=
  CNF.rup_sound cl_27384 [cl_7151,cl_27376] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7151 v h) (hints_cons _ _ _ (der_27376 v h) (by intro d hd; cases hd)))
def cl_27385 : CNF.NClause := [(55,false),(84,true),(24,true),(67,true),(76,true),(80,false),(91,true)]
theorem der_27385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27385 :=
  CNF.rup_sound cl_27385 [cl_7152,cl_27383] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7152 v h) (hints_cons _ _ _ (der_27383 v h) (by intro d hd; cases hd)))
def cl_27386 : CNF.NClause := [(55,false),(84,true),(24,false),(67,false),(76,false),(63,false),(91,true)]
theorem der_27386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27386 :=
  CNF.rup_sound cl_27386 [cl_7153,cl_27370] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7153 v h) (hints_cons _ _ _ (der_27370 v h) (by intro d hd; cases hd)))
def cl_27387 : CNF.NClause := [(55,false),(84,true),(24,true),(67,false),(63,false),(76,false),(91,true)]
theorem der_27387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27387 :=
  CNF.rup_sound cl_27387 [cl_7154,cl_27371] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7154 v h) (hints_cons _ _ _ (der_27371 v h) (by intro d hd; cases hd)))
def cl_27388 : CNF.NClause := [(55,false),(84,true),(24,false),(63,true),(67,false),(76,false),(80,true)]
theorem der_27388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27388 :=
  CNF.rup_sound cl_27388 [cl_7155,cl_27325] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7155 v h) (hints_cons _ _ _ (der_27325 v h) (by intro d hd; cases hd)))
def cl_27389 : CNF.NClause := [(55,false),(84,true),(67,false),(76,false),(63,true),(80,true),(91,true)]
theorem der_27389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27389 :=
  CNF.rup_sound cl_27389 [cl_7156,cl_27388] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7156 v h) (hints_cons _ _ _ (der_27388 v h) (by intro d hd; cases hd)))
def cl_27391 : CNF.NClause := [(55,false),(84,true),(24,true),(63,false),(76,false),(67,true),(80,true)]
theorem der_27391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27391 :=
  CNF.rup_sound cl_27391 [cl_7158,cl_27328] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7158 v h) (hints_cons _ _ _ (der_27328 v h) (by intro d hd; cases hd)))
def cl_27393 : CNF.NClause := [(55,false),(24,true),(67,true),(63,true),(76,false),(80,true),(91,true)]
theorem der_27393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27393 :=
  CNF.rup_sound cl_27393 [cl_7160,cl_27361] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7160 v h) (hints_cons _ _ _ (der_27361 v h) (by intro d hd; cases hd)))
def cl_27394 : CNF.NClause := [(55,false),(24,false),(67,false),(63,false),(76,true),(80,true),(91,true)]
theorem der_27394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27394 :=
  CNF.rup_sound cl_27394 [cl_7161,cl_27362] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7161 v h) (hints_cons _ _ _ (der_27362 v h) (by intro d hd; cases hd)))
def cl_27395 : CNF.NClause := [(55,false),(84,true),(24,true),(67,false),(63,false),(80,true),(91,true)]
theorem der_27395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27395 :=
  CNF.rup_sound cl_27395 [cl_7162,cl_27387] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7162 v h) (hints_cons _ _ _ (der_27387 v h) (by intro d hd; cases hd)))
def cl_27396 : CNF.NClause := [(55,false),(84,true),(24,false),(63,true),(67,false),(80,true),(91,true)]
theorem der_27396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27396 :=
  CNF.rup_sound cl_27396 [cl_7163,cl_27388] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7163 v h) (hints_cons _ _ _ (der_27388 v h) (by intro d hd; cases hd)))
def cl_27397 : CNF.NClause := [(55,false),(80,true),(24,true),(67,false),(76,true),(63,true),(84,true)]
theorem der_27397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27397 :=
  CNF.rup_sound cl_27397 [cl_7164,cl_27334] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7164 v h) (hints_cons _ _ _ (der_27334 v h) (by intro d hd; cases hd)))
def cl_27398 : CNF.NClause := [(55,false),(80,true),(24,false),(63,false),(76,true),(67,true),(91,true)]
theorem der_27398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27398 :=
  CNF.rup_sound cl_27398 [cl_7165,cl_27368] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7165 v h) (hints_cons _ _ _ (der_27368 v h) (by intro d hd; cases hd)))
def cl_27399 : CNF.NClause := [(55,false),(80,true),(24,true),(63,false),(76,true),(67,true),(91,true)]
theorem der_27399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27399 :=
  CNF.rup_sound cl_27399 [cl_7166,cl_27367] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7166 v h) (hints_cons _ _ _ (der_27367 v h) (by intro d hd; cases hd)))
def cl_27401 : CNF.NClause := [(55,false),(80,true),(24,true),(67,true),(63,true),(84,true),(91,true)]
theorem der_27401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27401 :=
  CNF.rup_sound cl_27401 [cl_7168,cl_27393] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7168 v h) (hints_cons _ _ _ (der_27393 v h) (by intro d hd; cases hd)))
def cl_27402 : CNF.NClause := [(46,false),(77,true),(81,false),(79,false),(78,false),(80,false),(92,false)]
theorem der_27402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27402 :=
  CNF.rup_sound cl_27402 [cl_5892,cl_5891] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5892 v h) (hints_cons _ _ _ (inp_5891 v h) (by intro d hd; cases hd)))
def cl_27403 : CNF.NClause := [(46,false),(15,true),(80,false),(79,false),(77,false),(81,false),(92,false)]
theorem der_27403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27403 :=
  CNF.rup_sound cl_27403 [cl_5894,cl_5890] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5894 v h) (hints_cons _ _ _ (inp_5890 v h) (by intro d hd; cases hd)))
def cl_27404 : CNF.NClause := [(46,false),(78,true),(15,false),(79,false),(80,false),(81,false),(92,false)]
theorem der_27404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27404 :=
  CNF.rup_sound cl_27404 [cl_5895,cl_5893] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5895 v h) (hints_cons _ _ _ (inp_5893 v h) (by intro d hd; cases hd)))
def cl_27405 : CNF.NClause := [(46,false),(78,true),(77,true),(79,false),(80,false),(81,false),(92,false)]
theorem der_27405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27405 :=
  CNF.rup_sound cl_27405 [cl_5896,cl_27404] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5896 v h) (hints_cons _ _ _ (der_27404 v h) (by intro d hd; cases hd)))
def cl_27406 : CNF.NClause := [(46,false),(92,false),(15,true),(78,false),(77,false),(81,false),(80,false)]
theorem der_27406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27406 :=
  CNF.rup_sound cl_27406 [cl_5898,cl_5890] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5898 v h) (hints_cons _ _ _ (inp_5890 v h) (by intro d hd; cases hd)))
def cl_27407 : CNF.NClause := [(46,false),(15,false),(92,false),(77,true),(78,false),(81,false),(80,false)]
theorem der_27407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27407 :=
  CNF.rup_sound cl_27407 [cl_5899,cl_26325] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5899 v h) (hints_cons _ _ _ (der_26325 v h) (by intro d hd; cases hd)))
def cl_27408 : CNF.NClause := [(46,false),(79,true),(78,false),(77,true),(80,false),(81,false),(92,false)]
theorem der_27408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27408 :=
  CNF.rup_sound cl_27408 [cl_5900,cl_27407] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5900 v h) (hints_cons _ _ _ (der_27407 v h) (by intro d hd; cases hd)))
def cl_27409 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(80,false),(81,false),(92,false)]
theorem der_27409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27409 :=
  CNF.rup_sound cl_27409 [cl_5901,cl_27404] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5901 v h) (hints_cons _ _ _ (der_27404 v h) (by intro d hd; cases hd)))
def cl_27410 : CNF.NClause := [(46,false),(79,true),(15,true),(77,false),(80,false),(81,false),(92,false)]
theorem der_27410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27410 :=
  CNF.rup_sound cl_27410 [cl_5902,cl_27406] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5902 v h) (hints_cons _ _ _ (der_27406 v h) (by intro d hd; cases hd)))
def cl_27411 : CNF.NClause := [(46,false),(78,true),(15,false),(77,true),(80,false),(81,false),(92,false)]
theorem der_27411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27411 :=
  CNF.rup_sound cl_27411 [cl_5903,cl_27404] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5903 v h) (hints_cons _ _ _ (der_27404 v h) (by intro d hd; cases hd)))
def cl_27412 : CNF.NClause := [(46,false),(78,true),(77,true),(79,true),(80,false),(81,false),(92,false)]
theorem der_27412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27412 :=
  CNF.rup_sound cl_27412 [cl_5904,cl_27411] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5904 v h) (hints_cons _ _ _ (der_27411 v h) (by intro d hd; cases hd)))
def cl_27413 : CNF.NClause := [(46,false),(80,true),(15,false),(79,false),(81,false),(78,false),(92,false)]
theorem der_27413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27413 :=
  CNF.rup_sound cl_27413 [cl_5905,cl_26325] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5905 v h) (hints_cons _ _ _ (der_26325 v h) (by intro d hd; cases hd)))
def cl_27414 : CNF.NClause := [(46,false),(92,false),(78,false),(79,false),(77,false),(81,false),(80,true)]
theorem der_27414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27414 :=
  CNF.rup_sound cl_27414 [cl_5906,cl_27413] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5906 v h) (hints_cons _ _ _ (der_27413 v h) (by intro d hd; cases hd)))
def cl_27415 : CNF.NClause := [(46,false),(15,true),(78,false),(79,false),(81,false),(80,true),(92,false)]
theorem der_27415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27415 :=
  CNF.rup_sound cl_27415 [cl_5908,cl_27414] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5908 v h) (hints_cons _ _ _ (der_27414 v h) (by intro d hd; cases hd)))
def cl_27416 : CNF.NClause := [(46,false),(78,true),(15,false),(77,false),(79,false),(81,false),(92,false)]
theorem der_27416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27416 :=
  CNF.rup_sound cl_27416 [cl_5909,cl_27404] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5909 v h) (hints_cons _ _ _ (der_27404 v h) (by intro d hd; cases hd)))
def cl_27417 : CNF.NClause := [(46,false),(15,true),(77,false),(79,false),(80,true),(81,false),(92,false)]
theorem der_27417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27417 :=
  CNF.rup_sound cl_27417 [cl_5910,cl_27415] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5910 v h) (hints_cons _ _ _ (der_27415 v h) (by intro d hd; cases hd)))
def cl_27418 : CNF.NClause := [(46,false),(15,false),(77,true),(79,false),(80,true),(81,false),(92,false)]
theorem der_27418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27418 :=
  CNF.rup_sound cl_27418 [cl_5911,cl_26326] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5911 v h) (hints_cons _ _ _ (der_26326 v h) (by intro d hd; cases hd)))
def cl_27419 : CNF.NClause := [(46,false),(15,true),(77,true),(79,false),(80,true),(81,false),(92,false)]
theorem der_27419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27419 :=
  CNF.rup_sound cl_27419 [cl_5912,cl_27415] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5912 v h) (hints_cons _ _ _ (der_27415 v h) (by intro d hd; cases hd)))
def cl_27420 : CNF.NClause := [(46,false),(15,false),(77,false),(80,true),(78,false),(81,false),(92,false)]
theorem der_27420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27420 :=
  CNF.rup_sound cl_27420 [cl_5913,cl_27413] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5913 v h) (hints_cons _ _ _ (der_27413 v h) (by intro d hd; cases hd)))
def cl_27421 : CNF.NClause := [(46,false),(79,true),(15,true),(78,false),(77,false),(81,false),(92,false)]
theorem der_27421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27421 :=
  CNF.rup_sound cl_27421 [cl_5914,cl_27406] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5914 v h) (hints_cons _ _ _ (der_27406 v h) (by intro d hd; cases hd)))
def cl_27422 : CNF.NClause := [(46,false),(15,false),(80,true),(77,true),(78,false),(81,false),(92,false)]
theorem der_27422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27422 :=
  CNF.rup_sound cl_27422 [cl_5915,cl_26325] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5915 v h) (hints_cons _ _ _ (der_26325 v h) (by intro d hd; cases hd)))
def cl_27423 : CNF.NClause := [(46,false),(15,true),(78,false),(77,true),(80,true),(81,false),(92,false)]
theorem der_27423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27423 :=
  CNF.rup_sound cl_27423 [cl_5916,cl_27419] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5916 v h) (hints_cons _ _ _ (der_27419 v h) (by intro d hd; cases hd)))
def cl_27424 : CNF.NClause := [(46,false),(79,true),(15,false),(77,false),(78,true),(81,false),(92,false)]
theorem der_27424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27424 :=
  CNF.rup_sound cl_27424 [cl_5917,cl_27409] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5917 v h) (hints_cons _ _ _ (der_27409 v h) (by intro d hd; cases hd)))
def cl_27425 : CNF.NClause := [(46,false),(79,true),(15,true),(77,false),(78,true),(81,false),(92,false)]
theorem der_27425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27425 :=
  CNF.rup_sound cl_27425 [cl_5918,cl_27410] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5918 v h) (hints_cons _ _ _ (der_27410 v h) (by intro d hd; cases hd)))
def cl_27426 : CNF.NClause := [(46,false),(78,true),(15,false),(77,true),(79,true),(81,false),(92,false)]
theorem der_27426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27426 :=
  CNF.rup_sound cl_27426 [cl_5919,cl_27411] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5919 v h) (hints_cons _ _ _ (der_27411 v h) (by intro d hd; cases hd)))
def cl_27427 : CNF.NClause := [(46,false),(78,true),(77,true),(79,true),(80,true),(81,false),(92,false)]
theorem der_27427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27427 :=
  CNF.rup_sound cl_27427 [cl_5920,cl_27426] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5920 v h) (hints_cons _ _ _ (der_27426 v h) (by intro d hd; cases hd)))
def cl_27428 : CNF.NClause := [(46,false),(15,true),(78,false),(79,false),(80,false),(77,false),(92,false)]
theorem der_27428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27428 :=
  CNF.rup_sound cl_27428 [cl_5922,cl_27406] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5922 v h) (hints_cons _ _ _ (der_27406 v h) (by intro d hd; cases hd)))
def cl_27429 : CNF.NClause := [(46,false),(15,false),(77,true),(79,false),(80,false),(78,false),(92,false)]
theorem der_27429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27429 :=
  CNF.rup_sound cl_27429 [cl_5923,cl_5891] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5923 v h) (hints_cons _ _ _ (inp_5891 v h) (by intro d hd; cases hd)))
def cl_27430 : CNF.NClause := [(46,false),(81,true),(78,false),(79,false),(80,false),(77,true),(92,false)]
theorem der_27430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27430 :=
  CNF.rup_sound cl_27430 [cl_5924,cl_27429] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5924 v h) (hints_cons _ _ _ (der_27429 v h) (by intro d hd; cases hd)))
def cl_27431 : CNF.NClause := [(46,false),(78,true),(15,false),(77,false),(79,false),(92,false),(80,false)]
theorem der_27431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27431 :=
  CNF.rup_sound cl_27431 [cl_5925,cl_27404] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5925 v h) (hints_cons _ _ _ (der_27404 v h) (by intro d hd; cases hd)))
def cl_27432 : CNF.NClause := [(46,false),(92,false),(15,true),(77,false),(79,false),(81,true),(80,false)]
theorem der_27432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27432 :=
  CNF.rup_sound cl_27432 [cl_5926,cl_27428] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5926 v h) (hints_cons _ _ _ (der_27428 v h) (by intro d hd; cases hd)))
def cl_27433 : CNF.NClause := [(46,false),(78,true),(15,false),(77,true),(79,false),(80,false),(92,false)]
theorem der_27433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27433 :=
  CNF.rup_sound cl_27433 [cl_5927,cl_27404] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5927 v h) (hints_cons _ _ _ (der_27404 v h) (by intro d hd; cases hd)))
def cl_27434 : CNF.NClause := [(46,false),(78,true),(77,true),(79,false),(80,false),(81,true),(92,false)]
theorem der_27434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27434 :=
  CNF.rup_sound cl_27434 [cl_5928,cl_27433] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5928 v h) (hints_cons _ _ _ (der_27433 v h) (by intro d hd; cases hd)))
def cl_27435 : CNF.NClause := [(46,false),(15,false),(77,false),(79,true),(80,false),(78,false),(92,false)]
theorem der_27435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27435 :=
  CNF.rup_sound cl_27435 [cl_5929,cl_5897] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5929 v h) (hints_cons _ _ _ (inp_5897 v h) (by intro d hd; cases hd)))
def cl_27436 : CNF.NClause := [(46,false),(15,true),(78,false),(77,false),(80,false),(79,true),(92,false)]
theorem der_27436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27436 :=
  CNF.rup_sound cl_27436 [cl_5930,cl_27406] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5930 v h) (hints_cons _ _ _ (der_27406 v h) (by intro d hd; cases hd)))
def cl_27437 : CNF.NClause := [(46,false),(15,false),(77,true),(79,true),(80,false),(78,false),(92,false)]
theorem der_27437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27437 :=
  CNF.rup_sound cl_27437 [cl_5931,cl_27407] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5931 v h) (hints_cons _ _ _ (der_27407 v h) (by intro d hd; cases hd)))
def cl_27438 : CNF.NClause := [(46,false),(15,true),(78,false),(77,true),(80,false),(81,true),(92,false)]
theorem der_27438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27438 :=
  CNF.rup_sound cl_27438 [cl_5932,cl_27430] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5932 v h) (hints_cons _ _ _ (der_27430 v h) (by intro d hd; cases hd)))
def cl_27439 : CNF.NClause := [(46,false),(79,true),(15,false),(77,false),(80,false),(81,true),(92,false)]
theorem der_27439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27439 :=
  CNF.rup_sound cl_27439 [cl_5933,cl_27435] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5933 v h) (hints_cons _ _ _ (der_27435 v h) (by intro d hd; cases hd)))
def cl_27440 : CNF.NClause := [(46,false),(79,true),(77,false),(78,true),(80,false),(81,true),(92,false)]
theorem der_27440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27440 :=
  CNF.rup_sound cl_27440 [cl_5934,cl_27439] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5934 v h) (hints_cons _ _ _ (der_27439 v h) (by intro d hd; cases hd)))
def cl_27441 : CNF.NClause := [(46,false),(78,true),(15,false),(77,true),(79,true),(80,false),(92,false)]
theorem der_27441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27441 :=
  CNF.rup_sound cl_27441 [cl_5935,cl_27426] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5935 v h) (hints_cons _ _ _ (der_27426 v h) (by intro d hd; cases hd)))
def cl_27442 : CNF.NClause := [(46,false),(78,true),(77,true),(79,true),(80,false),(81,true),(92,false)]
theorem der_27442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27442 :=
  CNF.rup_sound cl_27442 [cl_5936,cl_27441] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5936 v h) (hints_cons _ _ _ (der_27441 v h) (by intro d hd; cases hd)))
def cl_27443 : CNF.NClause := [(46,false),(15,false),(77,false),(79,false),(78,false),(80,true),(92,false)]
theorem der_27443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27443 :=
  CNF.rup_sound cl_27443 [cl_5937,cl_27413] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5937 v h) (hints_cons _ _ _ (der_27413 v h) (by intro d hd; cases hd)))
def cl_27444 : CNF.NClause := [(46,false),(15,true),(78,false),(79,false),(77,false),(80,true),(92,false)]
theorem der_27444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27444 :=
  CNF.rup_sound cl_27444 [cl_5938,cl_27415] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5938 v h) (hints_cons _ _ _ (der_27415 v h) (by intro d hd; cases hd)))
def cl_27445 : CNF.NClause := [(46,false),(15,true),(78,false),(79,false),(80,true),(77,true),(92,false)]
theorem der_27445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27445 :=
  CNF.rup_sound cl_27445 [cl_5940,cl_27415] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5940 v h) (hints_cons _ _ _ (der_27415 v h) (by intro d hd; cases hd)))
def cl_27446 : CNF.NClause := [(46,false),(78,true),(15,false),(77,false),(79,false),(80,true),(92,false)]
theorem der_27446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27446 :=
  CNF.rup_sound cl_27446 [cl_5941,cl_27416] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5941 v h) (hints_cons _ _ _ (der_27416 v h) (by intro d hd; cases hd)))
def cl_27447 : CNF.NClause := [(46,false),(78,true),(77,false),(79,false),(80,true),(81,true),(92,false)]
theorem der_27447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27447 :=
  CNF.rup_sound cl_27447 [cl_5942,cl_27446] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5942 v h) (hints_cons _ _ _ (der_27446 v h) (by intro d hd; cases hd)))
def cl_27448 : CNF.NClause := [(46,false),(78,true),(15,false),(77,true),(79,false),(81,true),(92,false)]
theorem der_27448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27448 :=
  CNF.rup_sound cl_27448 [cl_5943,cl_27433] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5943 v h) (hints_cons _ _ _ (der_27433 v h) (by intro d hd; cases hd)))
def cl_27449 : CNF.NClause := [(46,false),(78,true),(15,true),(79,false),(80,true),(81,true),(92,false)]
theorem der_27449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27449 :=
  CNF.rup_sound cl_27449 [cl_5944,cl_27447] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5944 v h) (hints_cons _ _ _ (der_27447 v h) (by intro d hd; cases hd)))
def cl_27450 : CNF.NClause := [(46,false),(81,true),(15,false),(77,false),(78,false),(80,true),(92,false)]
theorem der_27450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27450 :=
  CNF.rup_sound cl_27450 [cl_5945,cl_27443] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5945 v h) (hints_cons _ _ _ (der_27443 v h) (by intro d hd; cases hd)))
def cl_27451 : CNF.NClause := [(46,false),(81,true),(78,false),(77,false),(79,true),(80,true),(92,false)]
theorem der_27451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27451 :=
  CNF.rup_sound cl_27451 [cl_5946,cl_27450] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5946 v h) (hints_cons _ _ _ (der_27450 v h) (by intro d hd; cases hd)))
def cl_27452 : CNF.NClause := [(46,false),(15,false),(77,true),(79,true),(78,false),(80,true),(92,false)]
theorem der_27452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27452 :=
  CNF.rup_sound cl_27452 [cl_5947,cl_27422] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5947 v h) (hints_cons _ _ _ (der_27422 v h) (by intro d hd; cases hd)))
def cl_27453 : CNF.NClause := [(46,false),(15,true),(78,false),(77,true),(80,true),(81,true),(92,false)]
theorem der_27453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27453 :=
  CNF.rup_sound cl_27453 [cl_5948,cl_27445] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5948 v h) (hints_cons _ _ _ (der_27445 v h) (by intro d hd; cases hd)))
def cl_27454 : CNF.NClause := [(46,false),(79,true),(15,false),(77,false),(78,true),(81,true),(92,false)]
theorem der_27454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27454 :=
  CNF.rup_sound cl_27454 [cl_5949,cl_27439] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5949 v h) (hints_cons _ _ _ (der_27439 v h) (by intro d hd; cases hd)))
def cl_27455 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(80,true),(81,true),(92,false)]
theorem der_27455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27455 :=
  CNF.rup_sound cl_27455 [cl_5950,cl_27449] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5950 v h) (hints_cons _ _ _ (der_27449 v h) (by intro d hd; cases hd)))
def cl_27456 : CNF.NClause := [(46,false),(78,true),(15,false),(77,true),(79,true),(80,true),(92,false)]
theorem der_27456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27456 :=
  CNF.rup_sound cl_27456 [cl_5951,cl_27426] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5951 v h) (hints_cons _ _ _ (der_27426 v h) (by intro d hd; cases hd)))
def cl_27457 : CNF.NClause := [(46,false),(78,true),(15,true),(77,true),(80,true),(81,true),(92,false)]
theorem der_27457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27457 :=
  CNF.rup_sound cl_27457 [cl_5952,cl_27449] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5952 v h) (hints_cons _ _ _ (der_27449 v h) (by intro d hd; cases hd)))
def cl_27458 : CNF.NClause := [(46,false),(92,true),(15,false),(80,false),(78,false),(81,false),(79,false)]
theorem der_27458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27458 :=
  CNF.rup_sound cl_27458 [cl_5953,cl_26327] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5953 v h) (hints_cons _ _ _ (der_26327 v h) (by intro d hd; cases hd)))
def cl_27459 : CNF.NClause := [(46,false),(92,true),(81,false),(78,false),(79,false),(80,false),(77,false)]
theorem der_27459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27459 :=
  CNF.rup_sound cl_27459 [cl_5954,cl_27458] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5954 v h) (hints_cons _ _ _ (der_27458 v h) (by intro d hd; cases hd)))
def cl_27460 : CNF.NClause := [(46,false),(77,true),(15,true),(81,false),(79,false),(78,false),(80,false)]
theorem der_27460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27460 :=
  CNF.rup_sound cl_27460 [cl_5956,cl_27402] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5956 v h) (hints_cons _ _ _ (der_27402 v h) (by intro d hd; cases hd)))
def cl_27461 : CNF.NClause := [(46,false),(78,true),(15,false),(77,false),(79,false),(80,false),(81,false)]
theorem der_27461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27461 :=
  CNF.rup_sound cl_27461 [cl_5957,cl_27404] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5957 v h) (hints_cons _ _ _ (der_27404 v h) (by intro d hd; cases hd)))
def cl_27462 : CNF.NClause := [(46,false),(78,true),(80,false),(79,false),(77,false),(81,false),(92,true)]
theorem der_27462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27462 :=
  CNF.rup_sound cl_27462 [cl_5958,cl_27461] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5958 v h) (hints_cons _ _ _ (der_27461 v h) (by intro d hd; cases hd)))
def cl_27463 : CNF.NClause := [(46,false),(78,true),(15,false),(77,true),(79,false),(80,false),(81,false)]
theorem der_27463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27463 :=
  CNF.rup_sound cl_27463 [cl_5959,cl_27433] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5959 v h) (hints_cons _ _ _ (der_27433 v h) (by intro d hd; cases hd)))
def cl_27464 : CNF.NClause := [(46,false),(78,true),(15,true),(77,true),(79,false),(80,false),(81,false)]
theorem der_27464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27464 :=
  CNF.rup_sound cl_27464 [cl_5960,cl_27405] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5960 v h) (hints_cons _ _ _ (der_27405 v h) (by intro d hd; cases hd)))
def cl_27465 : CNF.NClause := [(46,false),(79,true),(15,false),(80,false),(77,false),(78,false),(81,false)]
theorem der_27465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27465 :=
  CNF.rup_sound cl_27465 [cl_5961,cl_27435] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5961 v h) (hints_cons _ _ _ (der_27435 v h) (by intro d hd; cases hd)))
def cl_27466 : CNF.NClause := [(46,false),(79,true),(77,false),(80,false),(78,false),(81,false),(92,true)]
theorem der_27466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27466 :=
  CNF.rup_sound cl_27466 [cl_5962,cl_27465] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5962 v h) (hints_cons _ _ _ (der_27465 v h) (by intro d hd; cases hd)))
def cl_27467 : CNF.NClause := [(46,false),(79,true),(15,false),(80,false),(78,false),(81,false),(92,true)]
theorem der_27467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27467 :=
  CNF.rup_sound cl_27467 [cl_5963,cl_27465] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5963 v h) (hints_cons _ _ _ (der_27465 v h) (by intro d hd; cases hd)))
def cl_27468 : CNF.NClause := [(46,false),(15,true),(78,false),(77,true),(80,false),(81,false),(92,true)]
theorem der_27468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27468 :=
  CNF.rup_sound cl_27468 [cl_5964,cl_27460] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5964 v h) (hints_cons _ _ _ (der_27460 v h) (by intro d hd; cases hd)))
def cl_27469 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(80,false),(81,false),(92,true)]
theorem der_27469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27469 :=
  CNF.rup_sound cl_27469 [cl_5965,cl_27462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5965 v h) (hints_cons _ _ _ (der_27462 v h) (by intro d hd; cases hd)))
def cl_27470 : CNF.NClause := [(46,false),(15,true),(77,false),(78,true),(80,false),(81,false),(92,true)]
theorem der_27470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27470 :=
  CNF.rup_sound cl_27470 [cl_5966,cl_27462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5966 v h) (hints_cons _ _ _ (der_27462 v h) (by intro d hd; cases hd)))
def cl_27471 : CNF.NClause := [(46,false),(78,true),(15,false),(77,true),(79,true),(80,false),(81,false)]
theorem der_27471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27471 :=
  CNF.rup_sound cl_27471 [cl_5967,cl_27426] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5967 v h) (hints_cons _ _ _ (der_27426 v h) (by intro d hd; cases hd)))
def cl_27472 : CNF.NClause := [(46,false),(15,true),(77,true),(79,true),(80,false),(81,false),(92,true)]
theorem der_27472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27472 :=
  CNF.rup_sound cl_27472 [cl_5968,cl_27468] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5968 v h) (hints_cons _ _ _ (der_27468 v h) (by intro d hd; cases hd)))
def cl_27473 : CNF.NClause := [(46,false),(80,true),(15,false),(81,false),(77,false),(78,false),(79,false)]
theorem der_27473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27473 :=
  CNF.rup_sound cl_27473 [cl_5969,cl_27413] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5969 v h) (hints_cons _ _ _ (der_27413 v h) (by intro d hd; cases hd)))
def cl_27474 : CNF.NClause := [(46,false),(80,true),(15,true),(81,false),(79,false),(78,false),(77,false)]
theorem der_27474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27474 :=
  CNF.rup_sound cl_27474 [cl_5970,cl_27415] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5970 v h) (hints_cons _ _ _ (der_27415 v h) (by intro d hd; cases hd)))
def cl_27475 : CNF.NClause := [(46,false),(77,true),(15,true),(78,false),(79,false),(81,false),(92,true)]
theorem der_27475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27475 :=
  CNF.rup_sound cl_27475 [cl_5972,cl_27468] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5972 v h) (hints_cons _ _ _ (der_27468 v h) (by intro d hd; cases hd)))
def cl_27476 : CNF.NClause := [(46,false),(78,true),(15,false),(77,false),(79,false),(80,true),(81,false)]
theorem der_27476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27476 :=
  CNF.rup_sound cl_27476 [cl_5973,cl_27446] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5973 v h) (hints_cons _ _ _ (der_27446 v h) (by intro d hd; cases hd)))
def cl_27477 : CNF.NClause := [(46,false),(78,true),(77,false),(79,false),(80,true),(81,false),(92,true)]
theorem der_27477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27477 :=
  CNF.rup_sound cl_27477 [cl_5974,cl_27476] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5974 v h) (hints_cons _ _ _ (der_27476 v h) (by intro d hd; cases hd)))
def cl_27478 : CNF.NClause := [(46,false),(78,true),(15,false),(79,false),(80,true),(81,false),(92,true)]
theorem der_27478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27478 :=
  CNF.rup_sound cl_27478 [cl_5975,cl_27476] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5975 v h) (hints_cons _ _ _ (der_27476 v h) (by intro d hd; cases hd)))
def cl_27479 : CNF.NClause := [(46,false),(15,true),(77,true),(79,false),(80,true),(81,false),(92,true)]
theorem der_27479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27479 :=
  CNF.rup_sound cl_27479 [cl_5976,cl_27475] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5976 v h) (hints_cons _ _ _ (der_27475 v h) (by intro d hd; cases hd)))
def cl_27480 : CNF.NClause := [(46,false),(79,true),(15,false),(77,false),(78,false),(81,false),(92,true)]
theorem der_27480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27480 :=
  CNF.rup_sound cl_27480 [cl_5977,cl_27465] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5977 v h) (hints_cons _ _ _ (der_27465 v h) (by intro d hd; cases hd)))
def cl_27481 : CNF.NClause := [(46,false),(15,true),(77,false),(80,true),(78,false),(81,false),(92,true)]
theorem der_27481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27481 :=
  CNF.rup_sound cl_27481 [cl_5978,cl_27474] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5978 v h) (hints_cons _ _ _ (der_27474 v h) (by intro d hd; cases hd)))
def cl_27482 : CNF.NClause := [(46,false),(15,false),(80,true),(77,true),(78,false),(81,false),(92,true)]
theorem der_27482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27482 :=
  CNF.rup_sound cl_27482 [cl_5979,cl_26329] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5979 v h) (hints_cons _ _ _ (der_26329 v h) (by intro d hd; cases hd)))
def cl_27483 : CNF.NClause := [(46,false),(79,true),(15,true),(78,false),(77,true),(81,false),(92,true)]
theorem der_27483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27483 :=
  CNF.rup_sound cl_27483 [cl_5980,cl_27468] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5980 v h) (hints_cons _ _ _ (der_27468 v h) (by intro d hd; cases hd)))
def cl_27484 : CNF.NClause := [(46,false),(15,false),(77,false),(78,true),(80,true),(81,false),(92,true)]
theorem der_27484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27484 :=
  CNF.rup_sound cl_27484 [cl_5981,cl_27476] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5981 v h) (hints_cons _ _ _ (der_27476 v h) (by intro d hd; cases hd)))
def cl_27485 : CNF.NClause := [(46,false),(79,true),(15,true),(77,false),(78,true),(81,false),(92,true)]
theorem der_27485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27485 :=
  CNF.rup_sound cl_27485 [cl_5982,cl_27470] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5982 v h) (hints_cons _ _ _ (der_27470 v h) (by intro d hd; cases hd)))
def cl_27486 : CNF.NClause := [(46,false),(78,true),(15,false),(77,true),(79,true),(80,true),(81,false)]
theorem der_27486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27486 :=
  CNF.rup_sound cl_27486 [cl_5983,cl_27426] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5983 v h) (hints_cons _ _ _ (der_27426 v h) (by intro d hd; cases hd)))
def cl_27487 : CNF.NClause := [(46,false),(78,true),(15,true),(79,true),(80,true),(81,false),(92,true)]
theorem der_27487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27487 :=
  CNF.rup_sound cl_27487 [cl_5984,cl_27485] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5984 v h) (hints_cons _ _ _ (der_27485 v h) (by intro d hd; cases hd)))
def cl_27488 : CNF.NClause := [(46,false),(81,true),(15,false),(77,false),(79,false),(78,false),(80,false)]
theorem der_27488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27488 :=
  CNF.rup_sound cl_27488 [cl_5985,cl_5921] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5985 v h) (hints_cons _ _ _ (inp_5921 v h) (by intro d hd; cases hd)))
def cl_27489 : CNF.NClause := [(46,false),(81,true),(15,true),(77,false),(79,false),(78,false),(80,false)]
theorem der_27489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27489 :=
  CNF.rup_sound cl_27489 [cl_5986,cl_27428] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5986 v h) (hints_cons _ _ _ (der_27428 v h) (by intro d hd; cases hd)))
def cl_27490 : CNF.NClause := [(46,false),(15,false),(77,true),(79,false),(80,false),(78,false),(92,true)]
theorem der_27490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27490 :=
  CNF.rup_sound cl_27490 [cl_5987,cl_26328] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5987 v h) (hints_cons _ _ _ (der_26328 v h) (by intro d hd; cases hd)))
def cl_27491 : CNF.NClause := [(46,false),(15,true),(78,false),(79,false),(80,false),(77,true),(92,true)]
theorem der_27491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27491 :=
  CNF.rup_sound cl_27491 [cl_5988,cl_27468] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5988 v h) (hints_cons _ _ _ (der_27468 v h) (by intro d hd; cases hd)))
def cl_27492 : CNF.NClause := [(46,false),(78,true),(15,false),(92,true),(79,false),(77,false),(80,false)]
theorem der_27492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27492 :=
  CNF.rup_sound cl_27492 [cl_5989,cl_27461] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5989 v h) (hints_cons _ _ _ (der_27461 v h) (by intro d hd; cases hd)))
def cl_27493 : CNF.NClause := [(46,false),(78,true),(15,true),(92,true),(79,false),(77,false),(80,false)]
theorem der_27493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27493 :=
  CNF.rup_sound cl_27493 [cl_5990,cl_27470] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5990 v h) (hints_cons _ _ _ (der_27470 v h) (by intro d hd; cases hd)))
def cl_27494 : CNF.NClause := [(46,false),(78,true),(15,false),(77,true),(79,false),(80,false),(81,true)]
theorem der_27494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27494 :=
  CNF.rup_sound cl_27494 [cl_5991,cl_27433] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5991 v h) (hints_cons _ _ _ (der_27433 v h) (by intro d hd; cases hd)))
def cl_27495 : CNF.NClause := [(46,false),(15,true),(77,true),(79,false),(80,false),(81,true),(92,true)]
theorem der_27495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27495 :=
  CNF.rup_sound cl_27495 [cl_5992,cl_27491] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5992 v h) (hints_cons _ _ _ (der_27491 v h) (by intro d hd; cases hd)))
def cl_27496 : CNF.NClause := [(46,false),(15,false),(77,false),(78,false),(80,false),(81,true),(92,true)]
theorem der_27496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27496 :=
  CNF.rup_sound cl_27496 [cl_5993,cl_27488] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5993 v h) (hints_cons _ _ _ (der_27488 v h) (by intro d hd; cases hd)))
def cl_27497 : CNF.NClause := [(46,false),(79,true),(15,true),(77,false),(78,false),(80,false),(81,true)]
theorem der_27497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27497 :=
  CNF.rup_sound cl_27497 [cl_5994,cl_27436] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5994 v h) (hints_cons _ _ _ (der_27436 v h) (by intro d hd; cases hd)))
def cl_27498 : CNF.NClause := [(46,false),(79,true),(15,false),(77,true),(78,false),(80,false),(81,true)]
theorem der_27498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27498 :=
  CNF.rup_sound cl_27498 [cl_5995,cl_27437] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5995 v h) (hints_cons _ _ _ (der_27437 v h) (by intro d hd; cases hd)))
def cl_27499 : CNF.NClause := [(46,false),(79,true),(15,true),(78,false),(77,true),(80,false),(92,true)]
theorem der_27499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27499 :=
  CNF.rup_sound cl_27499 [cl_5996,cl_27468] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5996 v h) (hints_cons _ _ _ (der_27468 v h) (by intro d hd; cases hd)))
def cl_27500 : CNF.NClause := [(46,false),(79,true),(15,false),(77,false),(78,true),(80,false),(81,true)]
theorem der_27500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27500 :=
  CNF.rup_sound cl_27500 [cl_5997,cl_27439] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5997 v h) (hints_cons _ _ _ (der_27439 v h) (by intro d hd; cases hd)))
def cl_27501 : CNF.NClause := [(46,false),(79,true),(15,true),(77,false),(78,true),(80,false),(92,true)]
theorem der_27501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27501 :=
  CNF.rup_sound cl_27501 [cl_5998,cl_27485] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5998 v h) (hints_cons _ _ _ (der_27485 v h) (by intro d hd; cases hd)))
def cl_27502 : CNF.NClause := [(46,false),(78,true),(15,false),(77,true),(79,true),(80,false),(81,true)]
theorem der_27502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27502 :=
  CNF.rup_sound cl_27502 [cl_5999,cl_27441] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5999 v h) (hints_cons _ _ _ (der_27441 v h) (by intro d hd; cases hd)))
def cl_27503 : CNF.NClause := [(46,false),(78,true),(15,true),(77,true),(80,false),(81,true),(92,true)]
theorem der_27503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27503 :=
  CNF.rup_sound cl_27503 [cl_6000,cl_27495] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6000 v h) (hints_cons _ _ _ (der_27495 v h) (by intro d hd; cases hd)))
def cl_27504 : CNF.NClause := [(46,false),(81,true),(15,false),(77,false),(79,false),(78,false),(80,true)]
theorem der_27504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27504 :=
  CNF.rup_sound cl_27504 [cl_6001,cl_27450] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6001 v h) (hints_cons _ _ _ (der_27450 v h) (by intro d hd; cases hd)))
def cl_27505 : CNF.NClause := [(46,false),(81,true),(77,false),(79,false),(78,false),(80,true),(92,true)]
theorem der_27505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27505 :=
  CNF.rup_sound cl_27505 [cl_6002,cl_27504] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6002 v h) (hints_cons _ _ _ (der_27504 v h) (by intro d hd; cases hd)))
def cl_27506 : CNF.NClause := [(46,false),(81,true),(15,true),(78,false),(79,false),(77,true),(92,true)]
theorem der_27506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27506 :=
  CNF.rup_sound cl_27506 [cl_6004,cl_27495] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6004 v h) (hints_cons _ _ _ (der_27495 v h) (by intro d hd; cases hd)))
def cl_27507 : CNF.NClause := [(46,false),(78,true),(15,false),(77,false),(79,false),(80,true),(92,true)]
theorem der_27507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27507 :=
  CNF.rup_sound cl_27507 [cl_6005,cl_27476] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6005 v h) (hints_cons _ _ _ (der_27476 v h) (by intro d hd; cases hd)))
def cl_27508 : CNF.NClause := [(46,false),(78,true),(15,true),(77,false),(79,false),(80,true),(81,true)]
theorem der_27508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27508 :=
  CNF.rup_sound cl_27508 [cl_6006,cl_27449] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6006 v h) (hints_cons _ _ _ (der_27449 v h) (by intro d hd; cases hd)))
def cl_27509 : CNF.NClause := [(46,false),(78,true),(15,false),(77,true),(79,false),(80,true),(92,true)]
theorem der_27509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27509 :=
  CNF.rup_sound cl_27509 [cl_6007,cl_27478] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6007 v h) (hints_cons _ _ _ (der_27478 v h) (by intro d hd; cases hd)))
def cl_27510 : CNF.NClause := [(46,false),(78,true),(15,true),(77,true),(79,false),(80,true),(81,true)]
theorem der_27510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27510 :=
  CNF.rup_sound cl_27510 [cl_6008,cl_27449] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6008 v h) (hints_cons _ _ _ (der_27449 v h) (by intro d hd; cases hd)))
def cl_27511 : CNF.NClause := [(46,false),(81,true),(15,false),(77,false),(78,false),(80,true),(92,true)]
theorem der_27511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27511 :=
  CNF.rup_sound cl_27511 [cl_6009,cl_27504] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6009 v h) (hints_cons _ _ _ (der_27504 v h) (by intro d hd; cases hd)))
def cl_27512 : CNF.NClause := [(46,false),(81,true),(77,false),(79,true),(78,false),(80,true),(92,true)]
theorem der_27512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27512 :=
  CNF.rup_sound cl_27512 [cl_6010,cl_27511] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6010 v h) (hints_cons _ _ _ (der_27511 v h) (by intro d hd; cases hd)))
def cl_27513 : CNF.NClause := [(46,false),(81,true),(15,false),(79,true),(78,false),(80,true),(92,true)]
theorem der_27513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27513 :=
  CNF.rup_sound cl_27513 [cl_6011,cl_27511] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6011 v h) (hints_cons _ _ _ (der_27511 v h) (by intro d hd; cases hd)))
def cl_27514 : CNF.NClause := [(46,false),(79,true),(78,false),(77,true),(80,true),(81,true),(92,true)]
theorem der_27514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27514 :=
  CNF.rup_sound cl_27514 [cl_6012,cl_27513] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6012 v h) (hints_cons _ _ _ (der_27513 v h) (by intro d hd; cases hd)))
def cl_27515 : CNF.NClause := [(46,false),(79,true),(15,false),(77,false),(78,true),(80,true),(81,true)]
theorem der_27515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27515 :=
  CNF.rup_sound cl_27515 [cl_6013,cl_27454] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6013 v h) (hints_cons _ _ _ (der_27454 v h) (by intro d hd; cases hd)))
def cl_27516 : CNF.NClause := [(46,false),(79,true),(15,true),(77,false),(78,true),(80,true),(92,true)]
theorem der_27516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27516 :=
  CNF.rup_sound cl_27516 [cl_6014,cl_27485] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6014 v h) (hints_cons _ _ _ (der_27485 v h) (by intro d hd; cases hd)))
def cl_27517 : CNF.NClause := [(46,false),(78,true),(15,false),(79,true),(80,true),(81,true),(92,true)]
theorem der_27517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27517 :=
  CNF.rup_sound cl_27517 [cl_6015,cl_27515] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6015 v h) (hints_cons _ _ _ (der_27515 v h) (by intro d hd; cases hd)))
def cl_27518 : CNF.NClause := [(46,false),(78,true),(15,true),(77,true),(79,true),(80,true),(81,true)]
theorem der_27518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27518 :=
  CNF.rup_sound cl_27518 [cl_6016,cl_27457] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6016 v h) (hints_cons _ _ _ (der_27457 v h) (by intro d hd; cases hd)))
def cl_27519 : CNF.NClause := [(42,false),(66,true),(80,false),(72,false),(90,false),(83,false),(69,false)]
theorem der_27519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27519 :=
  CNF.rup_sound cl_27519 [cl_5380,cl_5379] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5380 v h) (hints_cons _ _ _ (inp_5379 v h) (by intro d hd; cases hd)))
def cl_27520 : CNF.NClause := [(42,false),(69,true),(72,false),(66,false),(90,false),(83,false),(80,false)]
theorem der_27520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27520 :=
  CNF.rup_sound cl_27520 [cl_5382,cl_5381] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5382 v h) (hints_cons _ _ _ (inp_5381 v h) (by intro d hd; cases hd)))
def cl_27521 : CNF.NClause := [(42,false),(66,true),(11,false),(72,false),(80,false),(83,false),(90,false)]
theorem der_27521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27521 :=
  CNF.rup_sound cl_27521 [cl_5383,cl_5379] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5383 v h) (hints_cons _ _ _ (inp_5379 v h) (by intro d hd; cases hd)))
def cl_27522 : CNF.NClause := [(42,false),(11,true),(69,true),(72,false),(80,false),(83,false),(90,false)]
theorem der_27522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27522 :=
  CNF.rup_sound cl_27522 [cl_5384,cl_27520] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5384 v h) (hints_cons _ _ _ (der_27520 v h) (by intro d hd; cases hd)))
def cl_27523 : CNF.NClause := [(42,false),(72,true),(69,false),(80,false),(66,false),(83,false),(90,false)]
theorem der_27523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27523 :=
  CNF.rup_sound cl_27523 [cl_5386,cl_5385] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5386 v h) (hints_cons _ _ _ (inp_5385 v h) (by intro d hd; cases hd)))
def cl_27524 : CNF.NClause := [(42,false),(66,true),(11,false),(69,false),(80,false),(83,false),(90,false)]
theorem der_27524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27524 :=
  CNF.rup_sound cl_27524 [cl_5387,cl_5379] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5387 v h) (hints_cons _ _ _ (inp_5379 v h) (by intro d hd; cases hd)))
def cl_27525 : CNF.NClause := [(42,false),(66,true),(72,true),(69,false),(80,false),(83,false),(90,false)]
theorem der_27525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27525 :=
  CNF.rup_sound cl_27525 [cl_5388,cl_27524] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5388 v h) (hints_cons _ _ _ (der_27524 v h) (by intro d hd; cases hd)))
def cl_27526 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(80,false),(83,false),(90,false)]
theorem der_27526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27526 :=
  CNF.rup_sound cl_27526 [cl_5389,cl_27520] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5389 v h) (hints_cons _ _ _ (der_27520 v h) (by intro d hd; cases hd)))
def cl_27527 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(80,false),(83,false),(90,false)]
theorem der_27527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27527 :=
  CNF.rup_sound cl_27527 [cl_5390,cl_27520] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5390 v h) (hints_cons _ _ _ (der_27520 v h) (by intro d hd; cases hd)))
def cl_27528 : CNF.NClause := [(42,false),(66,true),(11,false),(72,true),(80,false),(83,false),(90,false)]
theorem der_27528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27528 :=
  CNF.rup_sound cl_27528 [cl_5391,cl_27524] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5391 v h) (hints_cons _ _ _ (der_27524 v h) (by intro d hd; cases hd)))
def cl_27529 : CNF.NClause := [(42,false),(66,true),(11,true),(69,true),(80,false),(83,false),(90,false)]
theorem der_27529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27529 :=
  CNF.rup_sound cl_27529 [cl_5392,cl_27522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5392 v h) (hints_cons _ _ _ (der_27522 v h) (by intro d hd; cases hd)))
def cl_27530 : CNF.NClause := [(42,false),(11,true),(83,false),(90,false),(66,false),(69,false),(72,false)]
theorem der_27530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27530 :=
  CNF.rup_sound cl_27530 [cl_5394,cl_5378] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5394 v h) (hints_cons _ _ _ (inp_5378 v h) (by intro d hd; cases hd)))
def cl_27531 : CNF.NClause := [(42,false),(66,true),(11,false),(69,false),(72,false),(83,false),(90,false)]
theorem der_27531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27531 :=
  CNF.rup_sound cl_27531 [cl_5395,cl_5379] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5395 v h) (hints_cons _ _ _ (inp_5379 v h) (by intro d hd; cases hd)))
def cl_27532 : CNF.NClause := [(42,false),(11,true),(90,false),(72,false),(69,false),(80,true),(83,false)]
theorem der_27532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27532 :=
  CNF.rup_sound cl_27532 [cl_5396,cl_27530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5396 v h) (hints_cons _ _ _ (der_27530 v h) (by intro d hd; cases hd)))
def cl_27533 : CNF.NClause := [(42,false),(69,true),(11,false),(83,false),(66,false),(72,false),(90,false)]
theorem der_27533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27533 :=
  CNF.rup_sound cl_27533 [cl_5397,cl_5381] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5397 v h) (hints_cons _ _ _ (inp_5381 v h) (by intro d hd; cases hd)))
def cl_27534 : CNF.NClause := [(42,false),(11,true),(66,false),(83,false),(72,false),(90,false),(80,true)]
theorem der_27534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27534 :=
  CNF.rup_sound cl_27534 [cl_5398,cl_27530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5398 v h) (hints_cons _ _ _ (der_27530 v h) (by intro d hd; cases hd)))
def cl_27535 : CNF.NClause := [(42,false),(66,true),(11,false),(72,false),(80,true),(83,false),(90,false)]
theorem der_27535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27535 :=
  CNF.rup_sound cl_27535 [cl_5399,cl_27531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5399 v h) (hints_cons _ _ _ (der_27531 v h) (by intro d hd; cases hd)))
def cl_27536 : CNF.NClause := [(42,false),(66,true),(69,true),(72,false),(80,true),(83,false),(90,false)]
theorem der_27536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27536 :=
  CNF.rup_sound cl_27536 [cl_5400,cl_27535] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5400 v h) (hints_cons _ _ _ (der_27535 v h) (by intro d hd; cases hd)))
def cl_27537 : CNF.NClause := [(42,false),(80,true),(11,false),(66,false),(69,false),(83,false),(90,false)]
theorem der_27537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27537 :=
  CNF.rup_sound cl_27537 [cl_5401,cl_5393] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5401 v h) (hints_cons _ _ _ (inp_5393 v h) (by intro d hd; cases hd)))
def cl_27538 : CNF.NClause := [(42,false),(80,true),(11,true),(66,false),(83,false),(69,false),(90,false)]
theorem der_27538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27538 :=
  CNF.rup_sound cl_27538 [cl_5402,cl_27530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5402 v h) (hints_cons _ _ _ (der_27530 v h) (by intro d hd; cases hd)))
def cl_27539 : CNF.NClause := [(42,false),(66,true),(11,false),(69,false),(80,true),(83,false),(90,false)]
theorem der_27539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27539 :=
  CNF.rup_sound cl_27539 [cl_5403,cl_27535] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5403 v h) (hints_cons _ _ _ (der_27535 v h) (by intro d hd; cases hd)))
def cl_27540 : CNF.NClause := [(42,false),(66,true),(11,true),(83,false),(69,false),(80,true),(90,false)]
theorem der_27540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27540 :=
  CNF.rup_sound cl_27540 [cl_5404,cl_27532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5404 v h) (hints_cons _ _ _ (der_27532 v h) (by intro d hd; cases hd)))
def cl_27541 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(80,true),(83,false),(90,false)]
theorem der_27541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27541 :=
  CNF.rup_sound cl_27541 [cl_5405,cl_27533] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5405 v h) (hints_cons _ _ _ (der_27533 v h) (by intro d hd; cases hd)))
def cl_27542 : CNF.NClause := [(42,false),(72,true),(66,false),(69,true),(80,true),(83,false),(90,false)]
theorem der_27542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27542 :=
  CNF.rup_sound cl_27542 [cl_5406,cl_27541] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5406 v h) (hints_cons _ _ _ (der_27541 v h) (by intro d hd; cases hd)))
def cl_27543 : CNF.NClause := [(42,false),(66,true),(11,false),(69,true),(80,true),(83,false),(90,false)]
theorem der_27543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27543 :=
  CNF.rup_sound cl_27543 [cl_5407,cl_27535] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5407 v h) (hints_cons _ _ _ (der_27535 v h) (by intro d hd; cases hd)))
def cl_27544 : CNF.NClause := [(42,false),(66,true),(11,true),(72,true),(80,true),(83,false),(90,false)]
theorem der_27544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27544 :=
  CNF.rup_sound cl_27544 [cl_5408,cl_27540] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5408 v h) (hints_cons _ _ _ (der_27540 v h) (by intro d hd; cases hd)))
def cl_27545 : CNF.NClause := [(42,false),(11,true),(66,false),(72,false),(69,false),(80,false),(90,false)]
theorem der_27545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27545 :=
  CNF.rup_sound cl_27545 [cl_5410,cl_27530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5410 v h) (hints_cons _ _ _ (der_27530 v h) (by intro d hd; cases hd)))
def cl_27546 : CNF.NClause := [(42,false),(66,true),(11,false),(69,false),(72,false),(80,false),(90,false)]
theorem der_27546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27546 :=
  CNF.rup_sound cl_27546 [cl_5411,cl_5379] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5411 v h) (hints_cons _ _ _ (inp_5379 v h) (by intro d hd; cases hd)))
def cl_27547 : CNF.NClause := [(42,false),(83,true),(66,true),(72,false),(69,false),(80,false),(90,false)]
theorem der_27547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27547 :=
  CNF.rup_sound cl_27547 [cl_5412,cl_27546] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5412 v h) (hints_cons _ _ _ (der_27546 v h) (by intro d hd; cases hd)))
def cl_27548 : CNF.NClause := [(42,false),(11,false),(66,false),(72,false),(80,false),(69,true),(90,false)]
theorem der_27548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27548 :=
  CNF.rup_sound cl_27548 [cl_5413,cl_5381] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5413 v h) (hints_cons _ _ _ (inp_5381 v h) (by intro d hd; cases hd)))
def cl_27549 : CNF.NClause := [(42,false),(83,true),(66,false),(72,false),(80,false),(69,true),(90,false)]
theorem der_27549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27549 :=
  CNF.rup_sound cl_27549 [cl_5414,cl_27548] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5414 v h) (hints_cons _ _ _ (der_27548 v h) (by intro d hd; cases hd)))
def cl_27550 : CNF.NClause := [(42,false),(66,true),(11,false),(72,false),(80,false),(83,true),(90,false)]
theorem der_27550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27550 :=
  CNF.rup_sound cl_27550 [cl_5415,cl_27546] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5415 v h) (hints_cons _ _ _ (der_27546 v h) (by intro d hd; cases hd)))
def cl_27551 : CNF.NClause := [(42,false),(11,true),(69,true),(72,false),(80,false),(83,true),(90,false)]
theorem der_27551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27551 :=
  CNF.rup_sound cl_27551 [cl_5416,cl_27549] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5416 v h) (hints_cons _ _ _ (der_27549 v h) (by intro d hd; cases hd)))
def cl_27552 : CNF.NClause := [(42,false),(83,true),(11,false),(66,false),(80,false),(69,false),(90,false)]
theorem der_27552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27552 :=
  CNF.rup_sound cl_27552 [cl_5417,cl_5409] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5417 v h) (hints_cons _ _ _ (inp_5409 v h) (by intro d hd; cases hd)))
def cl_27553 : CNF.NClause := [(42,false),(83,true),(11,true),(66,false),(69,false),(80,false),(90,false)]
theorem der_27553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27553 :=
  CNF.rup_sound cl_27553 [cl_5418,cl_27545] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5418 v h) (hints_cons _ _ _ (der_27545 v h) (by intro d hd; cases hd)))
def cl_27554 : CNF.NClause := [(42,false),(66,true),(11,false),(69,false),(80,false),(83,true),(90,false)]
theorem der_27554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27554 :=
  CNF.rup_sound cl_27554 [cl_5419,cl_27546] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5419 v h) (hints_cons _ _ _ (der_27546 v h) (by intro d hd; cases hd)))
def cl_27555 : CNF.NClause := [(42,false),(83,true),(11,true),(72,true),(69,false),(80,false),(90,false)]
theorem der_27555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27555 :=
  CNF.rup_sound cl_27555 [cl_5420,cl_27553] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5420 v h) (hints_cons _ _ _ (der_27553 v h) (by intro d hd; cases hd)))
def cl_27556 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(80,false),(83,true),(90,false)]
theorem der_27556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27556 :=
  CNF.rup_sound cl_27556 [cl_5421,cl_27548] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5421 v h) (hints_cons _ _ _ (der_27548 v h) (by intro d hd; cases hd)))
def cl_27557 : CNF.NClause := [(42,false),(72,true),(11,true),(66,false),(80,false),(83,true),(90,false)]
theorem der_27557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27557 :=
  CNF.rup_sound cl_27557 [cl_5422,cl_27553] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5422 v h) (hints_cons _ _ _ (der_27553 v h) (by intro d hd; cases hd)))
def cl_27558 : CNF.NClause := [(42,false),(66,true),(11,false),(72,true),(80,false),(83,true),(90,false)]
theorem der_27558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27558 :=
  CNF.rup_sound cl_27558 [cl_5423,cl_27554] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5423 v h) (hints_cons _ _ _ (der_27554 v h) (by intro d hd; cases hd)))
def cl_27559 : CNF.NClause := [(42,false),(66,true),(11,true),(69,true),(72,true),(80,false),(90,false)]
theorem der_27559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27559 :=
  CNF.rup_sound cl_27559 [cl_5424,cl_27529] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5424 v h) (hints_cons _ _ _ (der_27529 v h) (by intro d hd; cases hd)))
def cl_27560 : CNF.NClause := [(42,false),(11,false),(66,false),(72,false),(69,false),(80,true),(90,false)]
theorem der_27560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27560 :=
  CNF.rup_sound cl_27560 [cl_5425,cl_27537] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5425 v h) (hints_cons _ _ _ (der_27537 v h) (by intro d hd; cases hd)))
def cl_27561 : CNF.NClause := [(42,false),(11,true),(66,false),(72,false),(69,false),(80,true),(90,false)]
theorem der_27561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27561 :=
  CNF.rup_sound cl_27561 [cl_5426,cl_27530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5426 v h) (hints_cons _ _ _ (der_27530 v h) (by intro d hd; cases hd)))
def cl_27562 : CNF.NClause := [(42,false),(66,true),(11,false),(69,false),(72,false),(80,true),(90,false)]
theorem der_27562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27562 :=
  CNF.rup_sound cl_27562 [cl_5427,cl_27535] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5427 v h) (hints_cons _ _ _ (der_27535 v h) (by intro d hd; cases hd)))
def cl_27563 : CNF.NClause := [(42,false),(11,true),(66,true),(72,false),(69,false),(80,true),(90,false)]
theorem der_27563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27563 :=
  CNF.rup_sound cl_27563 [cl_5428,cl_27540] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5428 v h) (hints_cons _ _ _ (der_27540 v h) (by intro d hd; cases hd)))
def cl_27564 : CNF.NClause := [(42,false),(11,false),(66,false),(72,false),(80,true),(69,true),(90,false)]
theorem der_27564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27564 :=
  CNF.rup_sound cl_27564 [cl_5429,cl_27541] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5429 v h) (hints_cons _ _ _ (der_27541 v h) (by intro d hd; cases hd)))
def cl_27565 : CNF.NClause := [(42,false),(83,true),(66,false),(72,false),(80,true),(69,true),(90,false)]
theorem der_27565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27565 :=
  CNF.rup_sound cl_27565 [cl_5430,cl_27564] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5430 v h) (hints_cons _ _ _ (der_27564 v h) (by intro d hd; cases hd)))
def cl_27566 : CNF.NClause := [(42,false),(66,true),(11,false),(69,true),(72,false),(80,true),(90,false)]
theorem der_27566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27566 :=
  CNF.rup_sound cl_27566 [cl_5431,cl_27535] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5431 v h) (hints_cons _ _ _ (der_27535 v h) (by intro d hd; cases hd)))
def cl_27567 : CNF.NClause := [(42,false),(11,true),(69,true),(72,false),(80,true),(83,true),(90,false)]
theorem der_27567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27567 :=
  CNF.rup_sound cl_27567 [cl_5432,cl_27565] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5432 v h) (hints_cons _ _ _ (der_27565 v h) (by intro d hd; cases hd)))
def cl_27568 : CNF.NClause := [(42,false),(11,false),(66,false),(72,true),(69,false),(80,true),(90,false)]
theorem der_27568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27568 :=
  CNF.rup_sound cl_27568 [cl_5433,cl_27537] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5433 v h) (hints_cons _ _ _ (der_27537 v h) (by intro d hd; cases hd)))
def cl_27569 : CNF.NClause := [(42,false),(83,true),(11,true),(66,false),(72,true),(69,false),(90,false)]
theorem der_27569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27569 :=
  CNF.rup_sound cl_27569 [cl_5434,cl_27553] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5434 v h) (hints_cons _ _ _ (der_27553 v h) (by intro d hd; cases hd)))
def cl_27570 : CNF.NClause := [(42,false),(66,true),(11,false),(69,false),(72,true),(83,true),(90,false)]
theorem der_27570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27570 :=
  CNF.rup_sound cl_27570 [cl_5435,cl_27554] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5435 v h) (hints_cons _ _ _ (der_27554 v h) (by intro d hd; cases hd)))
def cl_27571 : CNF.NClause := [(42,false),(11,true),(66,true),(72,true),(69,false),(80,true),(90,false)]
theorem der_27571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27571 :=
  CNF.rup_sound cl_27571 [cl_5436,cl_27540] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5436 v h) (hints_cons _ _ _ (der_27540 v h) (by intro d hd; cases hd)))
def cl_27572 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(80,true),(83,true),(90,false)]
theorem der_27572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27572 :=
  CNF.rup_sound cl_27572 [cl_5437,cl_27564] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5437 v h) (hints_cons _ _ _ (der_27564 v h) (by intro d hd; cases hd)))
def cl_27573 : CNF.NClause := [(42,false),(72,true),(11,true),(66,false),(69,true),(80,true),(90,false)]
theorem der_27573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27573 :=
  CNF.rup_sound cl_27573 [cl_5438,cl_27542] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5438 v h) (hints_cons _ _ _ (der_27542 v h) (by intro d hd; cases hd)))
def cl_27574 : CNF.NClause := [(42,false),(66,true),(11,false),(69,true),(80,true),(83,true),(90,false)]
theorem der_27574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27574 :=
  CNF.rup_sound cl_27574 [cl_5439,cl_27566] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5439 v h) (hints_cons _ _ _ (der_27566 v h) (by intro d hd; cases hd)))
def cl_27575 : CNF.NClause := [(42,false),(11,true),(69,true),(72,true),(80,true),(83,true),(90,false)]
theorem der_27575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27575 :=
  CNF.rup_sound cl_27575 [cl_5440,cl_27573] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5440 v h) (hints_cons _ _ _ (der_27573 v h) (by intro d hd; cases hd)))
def cl_27576 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(72,false),(80,false),(83,false)]
theorem der_27576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27576 :=
  CNF.rup_sound cl_27576 [cl_5442,cl_27530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5442 v h) (hints_cons _ _ _ (der_27530 v h) (by intro d hd; cases hd)))
def cl_27577 : CNF.NClause := [(42,false),(66,true),(11,false),(69,false),(72,false),(80,false),(83,false)]
theorem der_27577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27577 :=
  CNF.rup_sound cl_27577 [cl_5443,cl_27546] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5443 v h) (hints_cons _ _ _ (der_27546 v h) (by intro d hd; cases hd)))
def cl_27578 : CNF.NClause := [(42,false),(66,true),(80,false),(72,false),(69,false),(83,false),(90,true)]
theorem der_27578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27578 :=
  CNF.rup_sound cl_27578 [cl_5444,cl_27577] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5444 v h) (hints_cons _ _ _ (der_27577 v h) (by intro d hd; cases hd)))
def cl_27579 : CNF.NClause := [(42,false),(11,false),(66,false),(72,false),(80,false),(83,false),(69,true)]
theorem der_27579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27579 :=
  CNF.rup_sound cl_27579 [cl_5445,cl_27526] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5445 v h) (hints_cons _ _ _ (der_27526 v h) (by intro d hd; cases hd)))
def cl_27580 : CNF.NClause := [(42,false),(11,true),(66,false),(72,false),(80,false),(83,false),(69,true)]
theorem der_27580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27580 :=
  CNF.rup_sound cl_27580 [cl_5446,cl_27522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5446 v h) (hints_cons _ _ _ (der_27522 v h) (by intro d hd; cases hd)))
def cl_27581 : CNF.NClause := [(42,false),(11,false),(69,true),(72,false),(80,false),(83,false),(90,true)]
theorem der_27581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27581 :=
  CNF.rup_sound cl_27581 [cl_5447,cl_27579] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5447 v h) (hints_cons _ _ _ (der_27579 v h) (by intro d hd; cases hd)))
def cl_27582 : CNF.NClause := [(42,false),(66,true),(11,true),(69,true),(72,false),(80,false),(83,false)]
theorem der_27582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27582 :=
  CNF.rup_sound cl_27582 [cl_5448,cl_27522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5448 v h) (hints_cons _ _ _ (der_27522 v h) (by intro d hd; cases hd)))
def cl_27583 : CNF.NClause := [(42,false),(72,true),(11,false),(66,false),(80,false),(83,false),(69,false)]
theorem der_27583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27583 :=
  CNF.rup_sound cl_27583 [cl_5449,cl_5385] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5449 v h) (hints_cons _ _ _ (inp_5385 v h) (by intro d hd; cases hd)))
def cl_27584 : CNF.NClause := [(42,false),(11,true),(66,false),(69,false),(90,true),(83,false),(80,false)]
theorem der_27584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27584 :=
  CNF.rup_sound cl_27584 [cl_5450,cl_27576] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5450 v h) (hints_cons _ _ _ (der_27576 v h) (by intro d hd; cases hd)))
def cl_27585 : CNF.NClause := [(42,false),(66,true),(11,false),(69,false),(72,true),(80,false),(83,false)]
theorem der_27585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27585 :=
  CNF.rup_sound cl_27585 [cl_5451,cl_27524] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5451 v h) (hints_cons _ _ _ (der_27524 v h) (by intro d hd; cases hd)))
def cl_27586 : CNF.NClause := [(42,false),(72,true),(11,true),(66,true),(69,false),(83,false),(80,false)]
theorem der_27586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27586 :=
  CNF.rup_sound cl_27586 [cl_5452,cl_27525] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5452 v h) (hints_cons _ _ _ (der_27525 v h) (by intro d hd; cases hd)))
def cl_27587 : CNF.NClause := [(42,false),(72,true),(11,false),(66,false),(80,false),(83,false),(90,true)]
theorem der_27587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27587 :=
  CNF.rup_sound cl_27587 [cl_5453,cl_27583] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5453 v h) (hints_cons _ _ _ (der_27583 v h) (by intro d hd; cases hd)))
def cl_27588 : CNF.NClause := [(42,false),(11,true),(66,false),(69,true),(80,false),(83,false),(90,true)]
theorem der_27588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27588 :=
  CNF.rup_sound cl_27588 [cl_5454,cl_27580] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5454 v h) (hints_cons _ _ _ (der_27580 v h) (by intro d hd; cases hd)))
def cl_27589 : CNF.NClause := [(42,false),(66,true),(11,false),(72,true),(80,false),(83,false),(90,true)]
theorem der_27589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27589 :=
  CNF.rup_sound cl_27589 [cl_5455,cl_27585] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5455 v h) (hints_cons _ _ _ (der_27585 v h) (by intro d hd; cases hd)))
def cl_27590 : CNF.NClause := [(42,false),(66,true),(11,true),(69,true),(80,false),(83,false),(90,true)]
theorem der_27590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27590 :=
  CNF.rup_sound cl_27590 [cl_5456,cl_27582] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5456 v h) (hints_cons _ _ _ (der_27582 v h) (by intro d hd; cases hd)))
def cl_27591 : CNF.NClause := [(42,false),(90,true),(11,false),(66,false),(69,false),(83,false),(72,false)]
theorem der_27591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27591 :=
  CNF.rup_sound cl_27591 [cl_5457,cl_5441] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5457 v h) (hints_cons _ _ _ (inp_5441 v h) (by intro d hd; cases hd)))
def cl_27592 : CNF.NClause := [(42,false),(11,true),(66,false),(72,false),(69,false),(83,false),(80,true)]
theorem der_27592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27592 :=
  CNF.rup_sound cl_27592 [cl_5458,cl_27530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5458 v h) (hints_cons _ _ _ (der_27530 v h) (by intro d hd; cases hd)))
def cl_27593 : CNF.NClause := [(42,false),(66,true),(11,false),(69,false),(72,false),(80,true),(83,false)]
theorem der_27593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27593 :=
  CNF.rup_sound cl_27593 [cl_5459,cl_27535] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5459 v h) (hints_cons _ _ _ (der_27535 v h) (by intro d hd; cases hd)))
def cl_27594 : CNF.NClause := [(42,false),(11,true),(66,true),(72,false),(69,false),(83,false),(80,true)]
theorem der_27594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27594 :=
  CNF.rup_sound cl_27594 [cl_5460,cl_27540] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5460 v h) (hints_cons _ _ _ (der_27540 v h) (by intro d hd; cases hd)))
def cl_27595 : CNF.NClause := [(42,false),(11,false),(66,false),(72,false),(80,true),(83,false),(69,true)]
theorem der_27595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27595 :=
  CNF.rup_sound cl_27595 [cl_5461,cl_27564] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5461 v h) (hints_cons _ _ _ (der_27564 v h) (by intro d hd; cases hd)))
def cl_27596 : CNF.NClause := [(42,false),(11,true),(66,false),(72,false),(80,true),(83,false),(69,true)]
theorem der_27596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27596 :=
  CNF.rup_sound cl_27596 [cl_5462,cl_27534] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5462 v h) (hints_cons _ _ _ (der_27534 v h) (by intro d hd; cases hd)))
def cl_27598 : CNF.NClause := [(42,false),(66,true),(11,true),(69,true),(72,false),(83,false),(90,true)]
theorem der_27598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27598 :=
  CNF.rup_sound cl_27598 [cl_5464,cl_27582] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5464 v h) (hints_cons _ _ _ (der_27582 v h) (by intro d hd; cases hd)))
def cl_27599 : CNF.NClause := [(42,false),(72,true),(11,false),(66,false),(80,true),(69,false),(83,false)]
theorem der_27599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27599 :=
  CNF.rup_sound cl_27599 [cl_5465,cl_27568] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5465 v h) (hints_cons _ _ _ (der_27568 v h) (by intro d hd; cases hd)))
def cl_27600 : CNF.NClause := [(42,false),(90,true),(11,true),(66,false),(72,true),(69,false),(83,false)]
theorem der_27600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27600 :=
  CNF.rup_sound cl_27600 [cl_5466,cl_27584] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5466 v h) (hints_cons _ _ _ (der_27584 v h) (by intro d hd; cases hd)))
def cl_27601 : CNF.NClause := [(42,false),(66,true),(11,false),(69,false),(72,true),(83,false),(90,true)]
theorem der_27601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27601 :=
  CNF.rup_sound cl_27601 [cl_5467,cl_27585] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5467 v h) (hints_cons _ _ _ (der_27585 v h) (by intro d hd; cases hd)))
def cl_27602 : CNF.NClause := [(42,false),(66,true),(11,true),(80,true),(72,true),(69,false),(83,false)]
theorem der_27602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27602 :=
  CNF.rup_sound cl_27602 [cl_5468,cl_27540] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5468 v h) (hints_cons _ _ _ (der_27540 v h) (by intro d hd; cases hd)))
def cl_27603 : CNF.NClause := [(42,false),(72,true),(11,false),(66,false),(69,true),(80,true),(83,false)]
theorem der_27603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27603 :=
  CNF.rup_sound cl_27603 [cl_5469,cl_27542] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5469 v h) (hints_cons _ _ _ (der_27542 v h) (by intro d hd; cases hd)))
def cl_27604 : CNF.NClause := [(42,false),(72,true),(11,true),(66,false),(69,true),(80,true),(83,false)]
theorem der_27604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27604 :=
  CNF.rup_sound cl_27604 [cl_5470,cl_27573] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5470 v h) (hints_cons _ _ _ (der_27573 v h) (by intro d hd; cases hd)))
def cl_27606 : CNF.NClause := [(42,false),(66,true),(11,true),(69,true),(72,true),(83,false),(90,true)]
theorem der_27606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27606 :=
  CNF.rup_sound cl_27606 [cl_5472,cl_27590] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5472 v h) (hints_cons _ _ _ (der_27590 v h) (by intro d hd; cases hd)))
def cl_27607 : CNF.NClause := [(42,false),(83,true),(11,false),(66,false),(72,false),(69,false),(80,false)]
theorem der_27607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27607 :=
  CNF.rup_sound cl_27607 [cl_5473,cl_5409] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5473 v h) (hints_cons _ _ _ (inp_5409 v h) (by intro d hd; cases hd)))
def cl_27608 : CNF.NClause := [(42,false),(83,true),(11,true),(66,false),(72,false),(69,false),(80,false)]
theorem der_27608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27608 :=
  CNF.rup_sound cl_27608 [cl_5474,cl_27553] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5474 v h) (hints_cons _ _ _ (der_27553 v h) (by intro d hd; cases hd)))
def cl_27609 : CNF.NClause := [(42,false),(66,true),(11,false),(69,false),(72,false),(80,false),(83,true)]
theorem der_27609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27609 :=
  CNF.rup_sound cl_27609 [cl_5475,cl_27546] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5475 v h) (hints_cons _ _ _ (der_27546 v h) (by intro d hd; cases hd)))
def cl_27610 : CNF.NClause := [(42,false),(83,true),(11,true),(72,false),(69,false),(80,false),(90,true)]
theorem der_27610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27610 :=
  CNF.rup_sound cl_27610 [cl_5476,cl_27608] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5476 v h) (hints_cons _ _ _ (der_27608 v h) (by intro d hd; cases hd)))
def cl_27611 : CNF.NClause := [(42,false),(83,true),(11,false),(66,false),(72,false),(80,false),(69,true)]
theorem der_27611 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27611 :=
  CNF.rup_sound cl_27611 [cl_5477,cl_27548] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5477 v h) (hints_cons _ _ _ (der_27548 v h) (by intro d hd; cases hd)))
def cl_27612 : CNF.NClause := [(42,false),(83,true),(11,true),(66,false),(72,false),(80,false),(90,true)]
theorem der_27612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27612 :=
  CNF.rup_sound cl_27612 [cl_5478,cl_27608] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5478 v h) (hints_cons _ _ _ (der_27608 v h) (by intro d hd; cases hd)))
def cl_27614 : CNF.NClause := [(42,false),(66,true),(11,true),(69,true),(72,false),(80,false),(90,true)]
theorem der_27614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27614 :=
  CNF.rup_sound cl_27614 [cl_5480,cl_27582] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5480 v h) (hints_cons _ _ _ (der_27582 v h) (by intro d hd; cases hd)))
def cl_27615 : CNF.NClause := [(42,false),(83,true),(11,false),(66,false),(80,false),(69,false),(90,true)]
theorem der_27615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27615 :=
  CNF.rup_sound cl_27615 [cl_5481,cl_27607] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5481 v h) (hints_cons _ _ _ (der_27607 v h) (by intro d hd; cases hd)))
def cl_27616 : CNF.NClause := [(42,false),(83,true),(11,true),(66,false),(72,true),(69,false),(80,false)]
theorem der_27616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27616 :=
  CNF.rup_sound cl_27616 [cl_5482,cl_27553] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5482 v h) (hints_cons _ _ _ (der_27553 v h) (by intro d hd; cases hd)))
def cl_27617 : CNF.NClause := [(42,false),(66,true),(11,false),(69,false),(72,true),(80,false),(83,true)]
theorem der_27617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27617 :=
  CNF.rup_sound cl_27617 [cl_5483,cl_27554] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5483 v h) (hints_cons _ _ _ (der_27554 v h) (by intro d hd; cases hd)))
def cl_27618 : CNF.NClause := [(42,false),(83,true),(66,true),(72,true),(69,false),(80,false),(90,true)]
theorem der_27618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27618 :=
  CNF.rup_sound cl_27618 [cl_5484,cl_27617] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5484 v h) (hints_cons _ _ _ (der_27617 v h) (by intro d hd; cases hd)))
def cl_27619 : CNF.NClause := [(42,false),(72,true),(11,false),(66,false),(69,true),(80,false),(83,true)]
theorem der_27619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27619 :=
  CNF.rup_sound cl_27619 [cl_5485,cl_27556] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5485 v h) (hints_cons _ _ _ (der_27556 v h) (by intro d hd; cases hd)))
def cl_27620 : CNF.NClause := [(42,false),(72,true),(11,true),(66,false),(69,true),(80,false),(83,true)]
theorem der_27620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27620 :=
  CNF.rup_sound cl_27620 [cl_5486,cl_27557] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5486 v h) (hints_cons _ _ _ (der_27557 v h) (by intro d hd; cases hd)))
def cl_27621 : CNF.NClause := [(42,false),(66,true),(11,false),(72,true),(80,false),(83,true),(90,true)]
theorem der_27621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27621 :=
  CNF.rup_sound cl_27621 [cl_5487,cl_27617] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5487 v h) (hints_cons _ _ _ (der_27617 v h) (by intro d hd; cases hd)))
def cl_27622 : CNF.NClause := [(42,false),(66,true),(11,true),(69,true),(72,true),(80,false),(90,true)]
theorem der_27622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27622 :=
  CNF.rup_sound cl_27622 [cl_5488,cl_27606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5488 v h) (hints_cons _ _ _ (der_27606 v h) (by intro d hd; cases hd)))
def cl_27623 : CNF.NClause := [(42,false),(83,true),(11,false),(66,false),(72,false),(69,false),(80,true)]
theorem der_27623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27623 :=
  CNF.rup_sound cl_27623 [cl_5489,cl_27560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5489 v h) (hints_cons _ _ _ (der_27560 v h) (by intro d hd; cases hd)))
def cl_27624 : CNF.NClause := [(42,false),(83,true),(11,true),(66,false),(72,false),(69,false),(90,true)]
theorem der_27624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27624 :=
  CNF.rup_sound cl_27624 [cl_5490,cl_27608] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5490 v h) (hints_cons _ _ _ (der_27608 v h) (by intro d hd; cases hd)))
def cl_27625 : CNF.NClause := [(42,false),(66,true),(11,false),(69,false),(72,false),(83,true),(90,true)]
theorem der_27625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27625 :=
  CNF.rup_sound cl_27625 [cl_5491,cl_27609] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5491 v h) (hints_cons _ _ _ (der_27609 v h) (by intro d hd; cases hd)))
def cl_27626 : CNF.NClause := [(42,false),(83,true),(66,true),(72,false),(69,false),(80,true),(90,true)]
theorem der_27626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27626 :=
  CNF.rup_sound cl_27626 [cl_5492,cl_27625] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5492 v h) (hints_cons _ _ _ (der_27625 v h) (by intro d hd; cases hd)))
def cl_27627 : CNF.NClause := [(42,false),(83,true),(11,false),(66,false),(72,false),(80,true),(69,true)]
theorem der_27627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27627 :=
  CNF.rup_sound cl_27627 [cl_5493,cl_27564] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5493 v h) (hints_cons _ _ _ (der_27564 v h) (by intro d hd; cases hd)))
def cl_27628 : CNF.NClause := [(42,false),(11,true),(66,false),(72,false),(80,true),(69,true),(90,true)]
theorem der_27628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27628 :=
  CNF.rup_sound cl_27628 [cl_5494,cl_27596] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5494 v h) (hints_cons _ _ _ (der_27596 v h) (by intro d hd; cases hd)))
def cl_27631 : CNF.NClause := [(42,false),(83,true),(11,false),(66,false),(69,false),(80,true),(90,true)]
theorem der_27631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27631 :=
  CNF.rup_sound cl_27631 [cl_5497,cl_27623] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5497 v h) (hints_cons _ _ _ (der_27623 v h) (by intro d hd; cases hd)))
def cl_27632 : CNF.NClause := [(42,false),(83,true),(11,true),(66,false),(69,false),(80,true),(90,true)]
theorem der_27632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27632 :=
  CNF.rup_sound cl_27632 [cl_5498,cl_27624] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5498 v h) (hints_cons _ _ _ (der_27624 v h) (by intro d hd; cases hd)))
def cl_27634 : CNF.NClause := [(42,false),(83,true),(11,true),(72,true),(69,false),(80,true),(90,true)]
theorem der_27634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27634 :=
  CNF.rup_sound cl_27634 [cl_5500,cl_27632] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5500 v h) (hints_cons _ _ _ (der_27632 v h) (by intro d hd; cases hd)))
def cl_27635 : CNF.NClause := [(42,false),(11,false),(66,false),(69,true),(80,true),(83,true),(90,true)]
theorem der_27635 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27635 :=
  CNF.rup_sound cl_27635 [cl_5501,cl_27627] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5501 v h) (hints_cons _ _ _ (der_27627 v h) (by intro d hd; cases hd)))
def cl_27636 : CNF.NClause := [(42,false),(72,true),(11,true),(66,false),(69,true),(80,true),(83,true)]
theorem der_27636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27636 :=
  CNF.rup_sound cl_27636 [cl_5502,cl_27573] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5502 v h) (hints_cons _ _ _ (der_27573 v h) (by intro d hd; cases hd)))
def cl_27638 : CNF.NClause := [(42,false),(66,true),(11,true),(69,true),(72,true),(80,true),(90,true)]
theorem der_27638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27638 :=
  CNF.rup_sound cl_27638 [cl_5504,cl_27606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5504 v h) (hints_cons _ _ _ (der_27606 v h) (by intro d hd; cases hd)))
def cl_27639 : CNF.NClause := [(34,false),(80,false),(3,true),(75,false),(70,false),(85,false),(87,false)]
theorem der_27639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27639 :=
  CNF.rup_sound cl_27639 [cl_4356,cl_4354] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4356 v h) (hints_cons _ _ _ (inp_4354 v h) (by intro d hd; cases hd)))
def cl_27640 : CNF.NClause := [(34,false),(3,true),(80,false),(65,false),(75,false),(85,false),(87,false)]
theorem der_27640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27640 :=
  CNF.rup_sound cl_27640 [cl_4358,cl_4354] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4358 v h) (hints_cons _ _ _ (inp_4354 v h) (by intro d hd; cases hd)))
def cl_27641 : CNF.NClause := [(34,false),(65,true),(3,false),(75,false),(80,false),(85,false),(87,false)]
theorem der_27641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27641 :=
  CNF.rup_sound cl_27641 [cl_4359,cl_4355] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4359 v h) (hints_cons _ _ _ (inp_4355 v h) (by intro d hd; cases hd)))
def cl_27642 : CNF.NClause := [(34,false),(65,true),(3,true),(75,false),(80,false),(85,false),(87,false)]
theorem der_27642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27642 :=
  CNF.rup_sound cl_27642 [cl_4360,cl_27639] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4360 v h) (hints_cons _ _ _ (der_27639 v h) (by intro d hd; cases hd)))
def cl_27643 : CNF.NClause := [(34,false),(3,true),(85,false),(70,false),(65,false),(87,false),(80,false)]
theorem der_27643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27643 :=
  CNF.rup_sound cl_27643 [cl_4362,cl_4354] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4362 v h) (hints_cons _ _ _ (inp_4354 v h) (by intro d hd; cases hd)))
def cl_27644 : CNF.NClause := [(34,false),(65,true),(3,false),(70,false),(80,false),(85,false),(87,false)]
theorem der_27644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27644 :=
  CNF.rup_sound cl_27644 [cl_4363,cl_4355] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4363 v h) (hints_cons _ _ _ (inp_4355 v h) (by intro d hd; cases hd)))
def cl_27645 : CNF.NClause := [(34,false),(65,true),(3,true),(70,false),(80,false),(85,false),(87,false)]
theorem der_27645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27645 :=
  CNF.rup_sound cl_27645 [cl_4364,cl_27642] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4364 v h) (hints_cons _ _ _ (der_27642 v h) (by intro d hd; cases hd)))
def cl_27646 : CNF.NClause := [(34,false),(3,false),(65,false),(70,true),(80,false),(85,false),(87,false)]
theorem der_27646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27646 :=
  CNF.rup_sound cl_27646 [cl_4365,cl_4357] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4365 v h) (hints_cons _ _ _ (inp_4357 v h) (by intro d hd; cases hd)))
def cl_27647 : CNF.NClause := [(34,false),(75,true),(65,false),(70,true),(80,false),(85,false),(87,false)]
theorem der_27647 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27647 :=
  CNF.rup_sound cl_27647 [cl_4366,cl_27646] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4366 v h) (hints_cons _ _ _ (der_27646 v h) (by intro d hd; cases hd)))
def cl_27648 : CNF.NClause := [(34,false),(3,false),(70,true),(75,true),(80,false),(85,false),(87,false)]
theorem der_27648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27648 :=
  CNF.rup_sound cl_27648 [cl_4367,cl_27646] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4367 v h) (hints_cons _ _ _ (der_27646 v h) (by intro d hd; cases hd)))
def cl_27649 : CNF.NClause := [(34,false),(65,true),(70,true),(75,true),(80,false),(85,false),(87,false)]
theorem der_27649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27649 :=
  CNF.rup_sound cl_27649 [cl_4368,cl_27648] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4368 v h) (hints_cons _ _ _ (der_27648 v h) (by intro d hd; cases hd)))
def cl_27650 : CNF.NClause := [(34,false),(80,true),(85,false),(87,false),(65,false),(70,false),(75,false)]
theorem der_27650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27650 :=
  CNF.rup_sound cl_27650 [cl_4370,cl_4369] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4370 v h) (hints_cons _ _ _ (inp_4369 v h) (by intro d hd; cases hd)))
def cl_27651 : CNF.NClause := [(34,false),(3,false),(70,false),(75,false),(80,true),(85,false),(87,false)]
theorem der_27651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27651 :=
  CNF.rup_sound cl_27651 [cl_4371,cl_4369] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4371 v h) (hints_cons _ _ _ (inp_4369 v h) (by intro d hd; cases hd)))
def cl_27652 : CNF.NClause := [(34,false),(80,true),(75,false),(70,false),(65,true),(85,false),(87,false)]
theorem der_27652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27652 :=
  CNF.rup_sound cl_27652 [cl_4372,cl_27651] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4372 v h) (hints_cons _ _ _ (der_27651 v h) (by intro d hd; cases hd)))
def cl_27653 : CNF.NClause := [(34,false),(85,false),(3,false),(65,false),(75,false),(80,true),(87,false)]
theorem der_27653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27653 :=
  CNF.rup_sound cl_27653 [cl_4373,cl_4369] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4373 v h) (hints_cons _ _ _ (inp_4369 v h) (by intro d hd; cases hd)))
def cl_27654 : CNF.NClause := [(34,false),(80,true),(65,false),(75,false),(85,false),(70,true),(87,false)]
theorem der_27654 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27654 :=
  CNF.rup_sound cl_27654 [cl_4374,cl_27653] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4374 v h) (hints_cons _ _ _ (der_27653 v h) (by intro d hd; cases hd)))
def cl_27655 : CNF.NClause := [(34,false),(65,true),(3,false),(75,false),(80,true),(85,false),(87,false)]
theorem der_27655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27655 :=
  CNF.rup_sound cl_27655 [cl_4375,cl_27652] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4375 v h) (hints_cons _ _ _ (der_27652 v h) (by intro d hd; cases hd)))
def cl_27656 : CNF.NClause := [(34,false),(65,true),(3,true),(75,false),(80,true),(85,false),(87,false)]
theorem der_27656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27656 :=
  CNF.rup_sound cl_27656 [cl_4376,cl_27652] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4376 v h) (hints_cons _ _ _ (der_27652 v h) (by intro d hd; cases hd)))
def cl_27657 : CNF.NClause := [(34,false),(80,true),(3,false),(65,false),(70,false),(85,false),(87,false)]
theorem der_27657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27657 :=
  CNF.rup_sound cl_27657 [cl_4377,cl_4369] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4377 v h) (hints_cons _ _ _ (inp_4369 v h) (by intro d hd; cases hd)))
def cl_27658 : CNF.NClause := [(34,false),(75,true),(70,false),(65,false),(85,false),(80,true),(87,false)]
theorem der_27658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27658 :=
  CNF.rup_sound cl_27658 [cl_4378,cl_27657] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4378 v h) (hints_cons _ _ _ (der_27657 v h) (by intro d hd; cases hd)))
def cl_27659 : CNF.NClause := [(34,false),(65,true),(3,false),(70,false),(80,true),(85,false),(87,false)]
theorem der_27659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27659 :=
  CNF.rup_sound cl_27659 [cl_4379,cl_27652] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4379 v h) (hints_cons _ _ _ (der_27652 v h) (by intro d hd; cases hd)))
def cl_27660 : CNF.NClause := [(34,false),(65,true),(3,true),(85,false),(70,false),(80,true),(87,false)]
theorem der_27660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27660 :=
  CNF.rup_sound cl_27660 [cl_4380,cl_27652] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4380 v h) (hints_cons _ _ _ (der_27652 v h) (by intro d hd; cases hd)))
def cl_27661 : CNF.NClause := [(34,false),(75,true),(3,false),(65,false),(70,true),(85,false),(87,false)]
theorem der_27661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27661 :=
  CNF.rup_sound cl_27661 [cl_4381,cl_27646] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4381 v h) (hints_cons _ _ _ (der_27646 v h) (by intro d hd; cases hd)))
def cl_27662 : CNF.NClause := [(34,false),(75,true),(65,false),(70,true),(80,true),(85,false),(87,false)]
theorem der_27662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27662 :=
  CNF.rup_sound cl_27662 [cl_4382,cl_27661] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4382 v h) (hints_cons _ _ _ (der_27661 v h) (by intro d hd; cases hd)))
def cl_27663 : CNF.NClause := [(34,false),(65,true),(3,false),(70,true),(80,true),(85,false),(87,false)]
theorem der_27663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27663 :=
  CNF.rup_sound cl_27663 [cl_4383,cl_27655] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4383 v h) (hints_cons _ _ _ (der_27655 v h) (by intro d hd; cases hd)))
def cl_27664 : CNF.NClause := [(34,false),(65,true),(70,true),(75,true),(80,true),(85,false),(87,false)]
theorem der_27664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27664 :=
  CNF.rup_sound cl_27664 [cl_4384,cl_27663] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4384 v h) (hints_cons _ _ _ (der_27663 v h) (by intro d hd; cases hd)))
def cl_27665 : CNF.NClause := [(34,false),(3,true),(80,false),(70,false),(75,false),(65,false),(87,false)]
theorem der_27665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27665 :=
  CNF.rup_sound cl_27665 [cl_4386,cl_27643] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4386 v h) (hints_cons _ _ _ (der_27643 v h) (by intro d hd; cases hd)))
def cl_27666 : CNF.NClause := [(34,false),(3,false),(70,false),(75,false),(80,false),(85,true),(87,false)]
theorem der_27666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27666 :=
  CNF.rup_sound cl_27666 [cl_4387,cl_4385] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4387 v h) (hints_cons _ _ _ (inp_4385 v h) (by intro d hd; cases hd)))
def cl_27667 : CNF.NClause := [(34,false),(85,true),(65,true),(70,false),(80,false),(75,false),(87,false)]
theorem der_27667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27667 :=
  CNF.rup_sound cl_27667 [cl_4388,cl_27666] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4388 v h) (hints_cons _ _ _ (der_27666 v h) (by intro d hd; cases hd)))
def cl_27668 : CNF.NClause := [(34,false),(3,false),(65,false),(80,false),(75,false),(85,true),(87,false)]
theorem der_27668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27668 :=
  CNF.rup_sound cl_27668 [cl_4389,cl_4385] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4389 v h) (hints_cons _ _ _ (inp_4385 v h) (by intro d hd; cases hd)))
def cl_27669 : CNF.NClause := [(34,false),(3,true),(80,false),(65,false),(75,false),(85,true),(87,false)]
theorem der_27669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27669 :=
  CNF.rup_sound cl_27669 [cl_4390,cl_27665] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4390 v h) (hints_cons _ _ _ (der_27665 v h) (by intro d hd; cases hd)))
def cl_27670 : CNF.NClause := [(34,false),(65,true),(3,false),(75,false),(80,false),(85,true),(87,false)]
theorem der_27670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27670 :=
  CNF.rup_sound cl_27670 [cl_4391,cl_27666] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4391 v h) (hints_cons _ _ _ (der_27666 v h) (by intro d hd; cases hd)))
def cl_27671 : CNF.NClause := [(34,false),(65,true),(70,true),(75,false),(80,false),(85,true),(87,false)]
theorem der_27671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27671 :=
  CNF.rup_sound cl_27671 [cl_4392,cl_27670] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4392 v h) (hints_cons _ _ _ (der_27670 v h) (by intro d hd; cases hd)))
def cl_27672 : CNF.NClause := [(34,false),(3,false),(65,false),(70,false),(80,false),(85,true),(87,false)]
theorem der_27672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27672 :=
  CNF.rup_sound cl_27672 [cl_4393,cl_27666] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4393 v h) (hints_cons _ _ _ (der_27666 v h) (by intro d hd; cases hd)))
def cl_27673 : CNF.NClause := [(34,false),(75,true),(70,false),(65,false),(80,false),(85,true),(87,false)]
theorem der_27673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27673 :=
  CNF.rup_sound cl_27673 [cl_4394,cl_27672] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4394 v h) (hints_cons _ _ _ (der_27672 v h) (by intro d hd; cases hd)))
def cl_27674 : CNF.NClause := [(34,false),(65,true),(3,false),(70,false),(80,false),(85,true),(87,false)]
theorem der_27674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27674 :=
  CNF.rup_sound cl_27674 [cl_4395,cl_27670] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4395 v h) (hints_cons _ _ _ (der_27670 v h) (by intro d hd; cases hd)))
def cl_27675 : CNF.NClause := [(34,false),(75,true),(3,true),(65,true),(70,false),(80,false),(87,false)]
theorem der_27675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27675 :=
  CNF.rup_sound cl_27675 [cl_4396,cl_27645] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4396 v h) (hints_cons _ _ _ (der_27645 v h) (by intro d hd; cases hd)))
def cl_27676 : CNF.NClause := [(34,false),(75,true),(3,false),(65,false),(70,true),(80,false),(87,false)]
theorem der_27676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27676 :=
  CNF.rup_sound cl_27676 [cl_4397,cl_27646] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4397 v h) (hints_cons _ _ _ (der_27646 v h) (by intro d hd; cases hd)))
def cl_27677 : CNF.NClause := [(34,false),(75,true),(65,false),(70,true),(80,false),(85,true),(87,false)]
theorem der_27677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27677 :=
  CNF.rup_sound cl_27677 [cl_4398,cl_27676] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4398 v h) (hints_cons _ _ _ (der_27676 v h) (by intro d hd; cases hd)))
def cl_27678 : CNF.NClause := [(34,false),(65,true),(3,false),(70,true),(80,false),(85,true),(87,false)]
theorem der_27678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27678 :=
  CNF.rup_sound cl_27678 [cl_4399,cl_27670] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4399 v h) (hints_cons _ _ _ (der_27670 v h) (by intro d hd; cases hd)))
def cl_27679 : CNF.NClause := [(34,false),(65,true),(70,true),(75,true),(80,false),(85,true),(87,false)]
theorem der_27679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27679 :=
  CNF.rup_sound cl_27679 [cl_4400,cl_27678] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4400 v h) (hints_cons _ _ _ (der_27678 v h) (by intro d hd; cases hd)))
def cl_27680 : CNF.NClause := [(34,false),(80,true),(3,false),(65,false),(75,false),(70,false),(87,false)]
theorem der_27680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27680 :=
  CNF.rup_sound cl_27680 [cl_4401,cl_4369] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4401 v h) (hints_cons _ _ _ (inp_4369 v h) (by intro d hd; cases hd)))
def cl_27681 : CNF.NClause := [(34,false),(3,true),(70,false),(75,false),(65,false),(85,true),(87,false)]
theorem der_27681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27681 :=
  CNF.rup_sound cl_27681 [cl_4402,cl_27665] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4402 v h) (hints_cons _ _ _ (der_27665 v h) (by intro d hd; cases hd)))
def cl_27682 : CNF.NClause := [(34,false),(65,true),(3,false),(70,false),(75,false),(80,true),(87,false)]
theorem der_27682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27682 :=
  CNF.rup_sound cl_27682 [cl_4403,cl_27652] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4403 v h) (hints_cons _ _ _ (der_27652 v h) (by intro d hd; cases hd)))
def cl_27683 : CNF.NClause := [(34,false),(80,true),(3,true),(75,false),(70,false),(65,true),(87,false)]
theorem der_27683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27683 :=
  CNF.rup_sound cl_27683 [cl_4404,cl_27652] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4404 v h) (hints_cons _ _ _ (der_27652 v h) (by intro d hd; cases hd)))
def cl_27684 : CNF.NClause := [(34,false),(80,true),(3,false),(65,false),(75,false),(70,true),(87,false)]
theorem der_27684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27684 :=
  CNF.rup_sound cl_27684 [cl_4405,cl_27653] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4405 v h) (hints_cons _ _ _ (der_27653 v h) (by intro d hd; cases hd)))
def cl_27685 : CNF.NClause := [(34,false),(80,true),(65,false),(75,false),(70,true),(85,true),(87,false)]
theorem der_27685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27685 :=
  CNF.rup_sound cl_27685 [cl_4406,cl_27684] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4406 v h) (hints_cons _ _ _ (der_27684 v h) (by intro d hd; cases hd)))
def cl_27686 : CNF.NClause := [(34,false),(65,true),(3,false),(70,true),(75,false),(80,true),(87,false)]
theorem der_27686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27686 :=
  CNF.rup_sound cl_27686 [cl_4407,cl_27655] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4407 v h) (hints_cons _ _ _ (der_27655 v h) (by intro d hd; cases hd)))
def cl_27687 : CNF.NClause := [(34,false),(65,true),(3,true),(70,true),(75,false),(80,true),(87,false)]
theorem der_27687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27687 :=
  CNF.rup_sound cl_27687 [cl_4408,cl_27656] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4408 v h) (hints_cons _ _ _ (der_27656 v h) (by intro d hd; cases hd)))
def cl_27688 : CNF.NClause := [(34,false),(80,true),(3,false),(65,false),(70,false),(75,true),(87,false)]
theorem der_27688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27688 :=
  CNF.rup_sound cl_27688 [cl_4409,cl_27657] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4409 v h) (hints_cons _ _ _ (der_27657 v h) (by intro d hd; cases hd)))
def cl_27689 : CNF.NClause := [(34,false),(80,true),(3,true),(70,false),(65,false),(85,true),(87,false)]
theorem der_27689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27689 :=
  CNF.rup_sound cl_27689 [cl_4410,cl_27681] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4410 v h) (hints_cons _ _ _ (der_27681 v h) (by intro d hd; cases hd)))
def cl_27690 : CNF.NClause := [(34,false),(65,true),(3,false),(70,false),(75,true),(80,true),(87,false)]
theorem der_27690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27690 :=
  CNF.rup_sound cl_27690 [cl_4411,cl_27659] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4411 v h) (hints_cons _ _ _ (der_27659 v h) (by intro d hd; cases hd)))
def cl_27691 : CNF.NClause := [(34,false),(80,true),(65,true),(70,false),(75,true),(85,true),(87,false)]
theorem der_27691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27691 :=
  CNF.rup_sound cl_27691 [cl_4412,cl_27690] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4412 v h) (hints_cons _ _ _ (der_27690 v h) (by intro d hd; cases hd)))
def cl_27692 : CNF.NClause := [(34,false),(75,true),(3,false),(65,false),(70,true),(85,true),(87,false)]
theorem der_27692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27692 :=
  CNF.rup_sound cl_27692 [cl_4413,cl_27676] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4413 v h) (hints_cons _ _ _ (der_27676 v h) (by intro d hd; cases hd)))
def cl_27693 : CNF.NClause := [(34,false),(75,true),(65,false),(70,true),(80,true),(85,true),(87,false)]
theorem der_27693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27693 :=
  CNF.rup_sound cl_27693 [cl_4414,cl_27692] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4414 v h) (hints_cons _ _ _ (der_27692 v h) (by intro d hd; cases hd)))
def cl_27694 : CNF.NClause := [(34,false),(65,true),(3,false),(70,true),(75,true),(80,true),(87,false)]
theorem der_27694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27694 :=
  CNF.rup_sound cl_27694 [cl_4415,cl_27663] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4415 v h) (hints_cons _ _ _ (der_27663 v h) (by intro d hd; cases hd)))
def cl_27695 : CNF.NClause := [(34,false),(65,true),(70,true),(75,true),(80,true),(85,true),(87,false)]
theorem der_27695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27695 :=
  CNF.rup_sound cl_27695 [cl_4416,cl_27694] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4416 v h) (hints_cons _ _ _ (der_27694 v h) (by intro d hd; cases hd)))
def cl_27696 : CNF.NClause := [(34,false),(80,false),(3,true),(75,false),(70,false),(85,false),(65,false)]
theorem der_27696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27696 :=
  CNF.rup_sound cl_27696 [cl_4418,cl_27643] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4418 v h) (hints_cons _ _ _ (der_27643 v h) (by intro d hd; cases hd)))
def cl_27697 : CNF.NClause := [(34,false),(65,true),(3,false),(70,false),(75,false),(80,false),(85,false)]
theorem der_27697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27697 :=
  CNF.rup_sound cl_27697 [cl_4419,cl_4355] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4419 v h) (hints_cons _ _ _ (inp_4355 v h) (by intro d hd; cases hd)))
def cl_27698 : CNF.NClause := [(34,false),(65,true),(3,true),(70,false),(85,false),(75,false),(80,false)]
theorem der_27698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27698 :=
  CNF.rup_sound cl_27698 [cl_4420,cl_27642] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4420 v h) (hints_cons _ _ _ (der_27642 v h) (by intro d hd; cases hd)))
def cl_27699 : CNF.NClause := [(34,false),(3,false),(80,false),(75,false),(70,true),(65,false),(85,false)]
theorem der_27699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27699 :=
  CNF.rup_sound cl_27699 [cl_4421,cl_4357] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4421 v h) (hints_cons _ _ _ (inp_4357 v h) (by intro d hd; cases hd)))
def cl_27700 : CNF.NClause := [(34,false),(70,true),(3,true),(80,false),(75,false),(85,false),(65,false)]
theorem der_27700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27700 :=
  CNF.rup_sound cl_27700 [cl_4422,cl_27640] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4422 v h) (hints_cons _ _ _ (der_27640 v h) (by intro d hd; cases hd)))
def cl_27702 : CNF.NClause := [(34,false),(65,true),(3,true),(70,true),(75,false),(80,false),(85,false)]
theorem der_27702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27702 :=
  CNF.rup_sound cl_27702 [cl_4424,cl_27642] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4424 v h) (hints_cons _ _ _ (der_27642 v h) (by intro d hd; cases hd)))
def cl_27703 : CNF.NClause := [(34,false),(75,true),(3,false),(65,false),(70,false),(80,false),(85,false)]
theorem der_27703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27703 :=
  CNF.rup_sound cl_27703 [cl_4425,cl_4361] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4425 v h) (hints_cons _ _ _ (inp_4361 v h) (by intro d hd; cases hd)))
def cl_27704 : CNF.NClause := [(34,false),(75,true),(65,false),(87,true),(80,false),(85,false),(70,false)]
theorem der_27704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27704 :=
  CNF.rup_sound cl_27704 [cl_4426,cl_27703] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4426 v h) (hints_cons _ _ _ (der_27703 v h) (by intro d hd; cases hd)))
def cl_27705 : CNF.NClause := [(34,false),(3,false),(70,false),(75,true),(80,false),(85,false),(87,true)]
theorem der_27705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27705 :=
  CNF.rup_sound cl_27705 [cl_4427,cl_27703] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4427 v h) (hints_cons _ _ _ (der_27703 v h) (by intro d hd; cases hd)))
def cl_27706 : CNF.NClause := [(34,false),(65,true),(3,true),(75,true),(70,false),(80,false),(85,false)]
theorem der_27706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27706 :=
  CNF.rup_sound cl_27706 [cl_4428,cl_27645] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4428 v h) (hints_cons _ _ _ (der_27645 v h) (by intro d hd; cases hd)))
def cl_27707 : CNF.NClause := [(34,false),(75,true),(3,false),(65,false),(70,true),(80,false),(85,false)]
theorem der_27707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27707 :=
  CNF.rup_sound cl_27707 [cl_4429,cl_27676] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4429 v h) (hints_cons _ _ _ (der_27676 v h) (by intro d hd; cases hd)))
def cl_27708 : CNF.NClause := [(34,false),(75,true),(65,false),(70,true),(80,false),(85,false),(87,true)]
theorem der_27708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27708 :=
  CNF.rup_sound cl_27708 [cl_4430,cl_27707] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4430 v h) (hints_cons _ _ _ (der_27707 v h) (by intro d hd; cases hd)))
def cl_27709 : CNF.NClause := [(34,false),(65,true),(3,false),(70,true),(75,true),(80,false),(85,false)]
theorem der_27709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27709 :=
  CNF.rup_sound cl_27709 [cl_4431,cl_27648] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4431 v h) (hints_cons _ _ _ (der_27648 v h) (by intro d hd; cases hd)))
def cl_27710 : CNF.NClause := [(34,false),(65,true),(70,true),(75,true),(80,false),(85,false),(87,true)]
theorem der_27710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27710 :=
  CNF.rup_sound cl_27710 [cl_4432,cl_27709] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4432 v h) (hints_cons _ _ _ (der_27709 v h) (by intro d hd; cases hd)))
def cl_27711 : CNF.NClause := [(34,false),(80,true),(3,false),(65,false),(75,false),(70,false),(85,false)]
theorem der_27711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27711 :=
  CNF.rup_sound cl_27711 [cl_4433,cl_4369] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4433 v h) (hints_cons _ _ _ (inp_4369 v h) (by intro d hd; cases hd)))
def cl_27712 : CNF.NClause := [(34,false),(80,true),(75,false),(70,false),(87,true),(65,false),(85,false)]
theorem der_27712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27712 :=
  CNF.rup_sound cl_27712 [cl_4434,cl_27711] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4434 v h) (hints_cons _ _ _ (der_27711 v h) (by intro d hd; cases hd)))
def cl_27713 : CNF.NClause := [(34,false),(65,true),(3,false),(70,false),(75,false),(80,true),(85,false)]
theorem der_27713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27713 :=
  CNF.rup_sound cl_27713 [cl_4435,cl_27652] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4435 v h) (hints_cons _ _ _ (der_27652 v h) (by intro d hd; cases hd)))
def cl_27714 : CNF.NClause := [(34,false),(80,true),(3,true),(65,true),(75,false),(70,false),(85,false)]
theorem der_27714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27714 :=
  CNF.rup_sound cl_27714 [cl_4436,cl_27652] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4436 v h) (hints_cons _ _ _ (der_27652 v h) (by intro d hd; cases hd)))
def cl_27715 : CNF.NClause := [(34,false),(85,false),(3,false),(65,false),(75,false),(70,true),(80,true)]
theorem der_27715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27715 :=
  CNF.rup_sound cl_27715 [cl_4437,cl_27653] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4437 v h) (hints_cons _ _ _ (der_27653 v h) (by intro d hd; cases hd)))
def cl_27716 : CNF.NClause := [(34,false),(3,true),(65,false),(75,false),(70,true),(85,false),(87,true)]
theorem der_27716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27716 :=
  CNF.rup_sound cl_27716 [cl_4438,cl_27700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4438 v h) (hints_cons _ _ _ (der_27700 v h) (by intro d hd; cases hd)))
def cl_27717 : CNF.NClause := [(34,false),(65,true),(3,false),(70,true),(75,false),(80,true),(85,false)]
theorem der_27717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27717 :=
  CNF.rup_sound cl_27717 [cl_4439,cl_27655] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4439 v h) (hints_cons _ _ _ (der_27655 v h) (by intro d hd; cases hd)))
def cl_27718 : CNF.NClause := [(34,false),(65,true),(70,true),(75,false),(80,true),(85,false),(87,true)]
theorem der_27718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27718 :=
  CNF.rup_sound cl_27718 [cl_4440,cl_27717] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4440 v h) (hints_cons _ _ _ (der_27717 v h) (by intro d hd; cases hd)))
def cl_27719 : CNF.NClause := [(34,false),(87,true),(3,false),(65,false),(70,false),(75,true),(85,false)]
theorem der_27719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27719 :=
  CNF.rup_sound cl_27719 [cl_4441,cl_27703] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4441 v h) (hints_cons _ _ _ (der_27703 v h) (by intro d hd; cases hd)))
def cl_27720 : CNF.NClause := [(34,false),(75,true),(3,true),(70,false),(65,false),(80,true),(85,false)]
theorem der_27720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27720 :=
  CNF.rup_sound cl_27720 [cl_4442,cl_27658] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4442 v h) (hints_cons _ _ _ (der_27658 v h) (by intro d hd; cases hd)))
def cl_27721 : CNF.NClause := [(34,false),(65,true),(3,false),(70,false),(75,true),(80,true),(85,false)]
theorem der_27721 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27721 :=
  CNF.rup_sound cl_27721 [cl_4443,cl_27659] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4443 v h) (hints_cons _ _ _ (der_27659 v h) (by intro d hd; cases hd)))
def cl_27722 : CNF.NClause := [(34,false),(65,true),(87,true),(70,false),(75,true),(80,true),(85,false)]
theorem der_27722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27722 :=
  CNF.rup_sound cl_27722 [cl_4444,cl_27721] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4444 v h) (hints_cons _ _ _ (der_27721 v h) (by intro d hd; cases hd)))
def cl_27723 : CNF.NClause := [(34,false),(75,true),(3,false),(65,false),(70,true),(85,false),(87,true)]
theorem der_27723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27723 :=
  CNF.rup_sound cl_27723 [cl_4445,cl_27707] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4445 v h) (hints_cons _ _ _ (der_27707 v h) (by intro d hd; cases hd)))
def cl_27724 : CNF.NClause := [(34,false),(75,true),(3,true),(65,false),(80,true),(85,false),(87,true)]
theorem der_27724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27724 :=
  CNF.rup_sound cl_27724 [cl_4446,cl_27720] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4446 v h) (hints_cons _ _ _ (der_27720 v h) (by intro d hd; cases hd)))
def cl_27725 : CNF.NClause := [(34,false),(65,true),(3,false),(70,true),(75,true),(80,true),(85,false)]
theorem der_27725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27725 :=
  CNF.rup_sound cl_27725 [cl_4447,cl_27663] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4447 v h) (hints_cons _ _ _ (der_27663 v h) (by intro d hd; cases hd)))
def cl_27726 : CNF.NClause := [(34,false),(65,true),(3,true),(70,true),(75,true),(80,true),(85,false)]
theorem der_27726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27726 :=
  CNF.rup_sound cl_27726 [cl_4448,cl_27664] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4448 v h) (hints_cons _ _ _ (der_27664 v h) (by intro d hd; cases hd)))
def cl_27727 : CNF.NClause := [(34,false),(3,false),(80,false),(75,false),(70,false),(65,false),(85,true)]
theorem der_27727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27727 :=
  CNF.rup_sound cl_27727 [cl_4449,cl_27668] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4449 v h) (hints_cons _ _ _ (der_27668 v h) (by intro d hd; cases hd)))
def cl_27728 : CNF.NClause := [(34,false),(80,false),(3,true),(85,true),(70,false),(75,false),(65,false)]
theorem der_27728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27728 :=
  CNF.rup_sound cl_27728 [cl_4450,cl_27665] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4450 v h) (hints_cons _ _ _ (der_27665 v h) (by intro d hd; cases hd)))
def cl_27729 : CNF.NClause := [(34,false),(65,true),(3,false),(70,false),(75,false),(80,false),(85,true)]
theorem der_27729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27729 :=
  CNF.rup_sound cl_27729 [cl_4451,cl_27670] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4451 v h) (hints_cons _ _ _ (der_27670 v h) (by intro d hd; cases hd)))
def cl_27730 : CNF.NClause := [(34,false),(85,true),(3,true),(70,false),(75,false),(80,false),(87,true)]
theorem der_27730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27730 :=
  CNF.rup_sound cl_27730 [cl_4452,cl_27728] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4452 v h) (hints_cons _ _ _ (der_27728 v h) (by intro d hd; cases hd)))
def cl_27731 : CNF.NClause := [(34,false),(3,false),(80,false),(75,false),(70,true),(85,true),(65,false)]
theorem der_27731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27731 :=
  CNF.rup_sound cl_27731 [cl_4453,cl_27668] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4453 v h) (hints_cons _ _ _ (der_27668 v h) (by intro d hd; cases hd)))
def cl_27732 : CNF.NClause := [(34,false),(70,true),(3,true),(65,false),(75,false),(85,true),(80,false)]
theorem der_27732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27732 :=
  CNF.rup_sound cl_27732 [cl_4454,cl_27669] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4454 v h) (hints_cons _ _ _ (der_27669 v h) (by intro d hd; cases hd)))
def cl_27733 : CNF.NClause := [(34,false),(65,true),(3,false),(70,true),(75,false),(80,false),(85,true)]
theorem der_27733 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27733 :=
  CNF.rup_sound cl_27733 [cl_4455,cl_27670] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4455 v h) (hints_cons _ _ _ (der_27670 v h) (by intro d hd; cases hd)))
def cl_27734 : CNF.NClause := [(34,false),(65,true),(70,true),(75,false),(80,false),(85,true),(87,true)]
theorem der_27734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27734 :=
  CNF.rup_sound cl_27734 [cl_4456,cl_27733] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4456 v h) (hints_cons _ _ _ (der_27733 v h) (by intro d hd; cases hd)))
def cl_27735 : CNF.NClause := [(34,false),(75,true),(3,false),(65,false),(70,false),(80,false),(87,true)]
theorem der_27735 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27735 :=
  CNF.rup_sound cl_27735 [cl_4457,cl_27703] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4457 v h) (hints_cons _ _ _ (der_27703 v h) (by intro d hd; cases hd)))
def cl_27736 : CNF.NClause := [(34,false),(75,true),(3,true),(65,false),(70,false),(80,false),(85,true)]
theorem der_27736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27736 :=
  CNF.rup_sound cl_27736 [cl_4458,cl_27673] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4458 v h) (hints_cons _ _ _ (der_27673 v h) (by intro d hd; cases hd)))
def cl_27737 : CNF.NClause := [(34,false),(65,true),(3,false),(70,false),(80,false),(85,true),(87,true)]
theorem der_27737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27737 :=
  CNF.rup_sound cl_27737 [cl_4459,cl_27729] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4459 v h) (hints_cons _ _ _ (der_27729 v h) (by intro d hd; cases hd)))
def cl_27738 : CNF.NClause := [(34,false),(75,true),(3,true),(70,false),(80,false),(85,true),(87,true)]
theorem der_27738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27738 :=
  CNF.rup_sound cl_27738 [cl_4460,cl_27736] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4460 v h) (hints_cons _ _ _ (der_27736 v h) (by intro d hd; cases hd)))
def cl_27739 : CNF.NClause := [(34,false),(75,true),(3,false),(65,false),(70,true),(80,false),(85,true)]
theorem der_27739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27739 :=
  CNF.rup_sound cl_27739 [cl_4461,cl_27676] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4461 v h) (hints_cons _ _ _ (der_27676 v h) (by intro d hd; cases hd)))
def cl_27740 : CNF.NClause := [(34,false),(75,true),(3,true),(65,false),(80,false),(85,true),(87,true)]
theorem der_27740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27740 :=
  CNF.rup_sound cl_27740 [cl_4462,cl_27736] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4462 v h) (hints_cons _ _ _ (der_27736 v h) (by intro d hd; cases hd)))
def cl_27741 : CNF.NClause := [(34,false),(65,true),(3,false),(70,true),(80,false),(85,true),(87,true)]
theorem der_27741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27741 :=
  CNF.rup_sound cl_27741 [cl_4463,cl_27733] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4463 v h) (hints_cons _ _ _ (der_27733 v h) (by intro d hd; cases hd)))
def cl_27742 : CNF.NClause := [(34,false),(65,true),(3,true),(70,true),(75,true),(80,false),(85,true)]
theorem der_27742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27742 :=
  CNF.rup_sound cl_27742 [cl_4464,cl_27679] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4464 v h) (hints_cons _ _ _ (der_27679 v h) (by intro d hd; cases hd)))
def cl_27743 : CNF.NClause := [(34,false),(80,true),(3,false),(65,false),(75,false),(70,false),(87,true)]
theorem der_27743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27743 :=
  CNF.rup_sound cl_27743 [cl_4465,cl_27711] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4465 v h) (hints_cons _ _ _ (der_27711 v h) (by intro d hd; cases hd)))
def cl_27744 : CNF.NClause := [(34,false),(80,true),(3,true),(65,false),(75,false),(70,false),(85,true)]
theorem der_27744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27744 :=
  CNF.rup_sound cl_27744 [cl_4466,cl_27681] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4466 v h) (hints_cons _ _ _ (der_27681 v h) (by intro d hd; cases hd)))
def cl_27745 : CNF.NClause := [(34,false),(65,true),(3,false),(70,false),(75,false),(80,true),(85,true)]
theorem der_27745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27745 :=
  CNF.rup_sound cl_27745 [cl_4467,cl_27682] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4467 v h) (hints_cons _ _ _ (der_27682 v h) (by intro d hd; cases hd)))
def cl_27746 : CNF.NClause := [(34,false),(80,true),(3,true),(65,true),(75,false),(70,false),(85,true)]
theorem der_27746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27746 :=
  CNF.rup_sound cl_27746 [cl_4468,cl_27683] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4468 v h) (hints_cons _ _ _ (der_27683 v h) (by intro d hd; cases hd)))
def cl_27747 : CNF.NClause := [(34,false),(80,true),(3,false),(65,false),(75,false),(70,true),(85,true)]
theorem der_27747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27747 :=
  CNF.rup_sound cl_27747 [cl_4469,cl_27684] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4469 v h) (hints_cons _ _ _ (der_27684 v h) (by intro d hd; cases hd)))
def cl_27748 : CNF.NClause := [(34,false),(80,true),(3,true),(65,false),(75,false),(85,true),(87,true)]
theorem der_27748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27748 :=
  CNF.rup_sound cl_27748 [cl_4470,cl_27744] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4470 v h) (hints_cons _ _ _ (der_27744 v h) (by intro d hd; cases hd)))
def cl_27749 : CNF.NClause := [(34,false),(65,true),(3,false),(70,true),(75,false),(80,true),(87,true)]
theorem der_27749 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27749 :=
  CNF.rup_sound cl_27749 [cl_4471,cl_27717] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4471 v h) (hints_cons _ _ _ (der_27717 v h) (by intro d hd; cases hd)))
def cl_27750 : CNF.NClause := [(34,false),(65,true),(3,true),(70,true),(75,false),(80,true),(85,true)]
theorem der_27750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27750 :=
  CNF.rup_sound cl_27750 [cl_4472,cl_27687] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4472 v h) (hints_cons _ _ _ (der_27687 v h) (by intro d hd; cases hd)))
def cl_27751 : CNF.NClause := [(34,false),(80,true),(3,false),(65,false),(70,false),(75,true),(85,true)]
theorem der_27751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27751 :=
  CNF.rup_sound cl_27751 [cl_4473,cl_27688] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4473 v h) (hints_cons _ _ _ (der_27688 v h) (by intro d hd; cases hd)))
def cl_27752 : CNF.NClause := [(34,false),(80,true),(65,false),(70,false),(75,true),(85,true),(87,true)]
theorem der_27752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27752 :=
  CNF.rup_sound cl_27752 [cl_4474,cl_27751] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4474 v h) (hints_cons _ _ _ (der_27751 v h) (by intro d hd; cases hd)))
def cl_27753 : CNF.NClause := [(34,false),(65,true),(3,false),(70,false),(75,true),(80,true),(85,true)]
theorem der_27753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27753 :=
  CNF.rup_sound cl_27753 [cl_4475,cl_27690] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4475 v h) (hints_cons _ _ _ (der_27690 v h) (by intro d hd; cases hd)))
def cl_27754 : CNF.NClause := [(34,false),(80,true),(65,true),(70,false),(75,true),(85,true),(87,true)]
theorem der_27754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27754 :=
  CNF.rup_sound cl_27754 [cl_4476,cl_27753] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4476 v h) (hints_cons _ _ _ (der_27753 v h) (by intro d hd; cases hd)))
def cl_27755 : CNF.NClause := [(34,false),(75,true),(3,false),(65,false),(80,true),(85,true),(87,true)]
theorem der_27755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27755 :=
  CNF.rup_sound cl_27755 [cl_4477,cl_27751] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4477 v h) (hints_cons _ _ _ (der_27751 v h) (by intro d hd; cases hd)))
def cl_27756 : CNF.NClause := [(34,false),(75,true),(65,false),(70,true),(80,true),(85,true),(87,true)]
theorem der_27756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27756 :=
  CNF.rup_sound cl_27756 [cl_4478,cl_27755] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4478 v h) (hints_cons _ _ _ (der_27755 v h) (by intro d hd; cases hd)))
def cl_27757 : CNF.NClause := [(34,false),(3,false),(70,true),(75,true),(80,true),(85,true),(87,true)]
theorem der_27757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27757 :=
  CNF.rup_sound cl_27757 [cl_4479,cl_27756] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4479 v h) (hints_cons _ _ _ (der_27756 v h) (by intro d hd; cases hd)))
def cl_27758 : CNF.NClause := [(34,false),(3,true),(70,true),(75,true),(80,true),(85,true),(87,true)]
theorem der_27758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27758 :=
  CNF.rup_sound cl_27758 [cl_4480,cl_27756] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4480 v h) (hints_cons _ _ _ (der_27756 v h) (by intro d hd; cases hd)))
def cl_27759 : CNF.NClause := [(48,false),(70,false),(83,false),(77,false),(64,true),(88,false),(76,false)]
theorem der_27759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27759 :=
  CNF.rup_sound cl_27759 [cl_6148,cl_6147] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6148 v h) (hints_cons _ _ _ (inp_6147 v h) (by intro d hd; cases hd)))
def cl_27760 : CNF.NClause := [(48,false),(70,true),(64,false),(83,false),(77,false),(76,false),(88,false)]
theorem der_27760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27760 :=
  CNF.rup_sound cl_27760 [cl_6150,cl_6149] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6150 v h) (hints_cons _ _ _ (inp_6149 v h) (by intro d hd; cases hd)))
def cl_27761 : CNF.NClause := [(48,false),(88,false),(17,false),(70,true),(77,false),(83,false),(76,false)]
theorem der_27761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27761 :=
  CNF.rup_sound cl_27761 [cl_6151,cl_6149] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6151 v h) (hints_cons _ _ _ (inp_6149 v h) (by intro d hd; cases hd)))
def cl_27762 : CNF.NClause := [(48,false),(70,true),(77,false),(64,true),(83,false),(88,false),(76,false)]
theorem der_27762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27762 :=
  CNF.rup_sound cl_27762 [cl_6152,cl_27761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6152 v h) (hints_cons _ _ _ (der_27761 v h) (by intro d hd; cases hd)))
def cl_27763 : CNF.NClause := [(48,false),(88,false),(70,false),(76,true),(83,false),(64,false),(77,false)]
theorem der_27763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27763 :=
  CNF.rup_sound cl_27763 [cl_6153,cl_6154] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6153 v h) (hints_cons _ _ _ (inp_6154 v h) (by intro d hd; cases hd)))
def cl_27764 : CNF.NClause := [(48,false),(70,false),(17,false),(88,false),(77,false),(83,false),(76,true)]
theorem der_27764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27764 :=
  CNF.rup_sound cl_27764 [cl_6155,cl_27763] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6155 v h) (hints_cons _ _ _ (der_27763 v h) (by intro d hd; cases hd)))
def cl_27765 : CNF.NClause := [(48,false),(70,false),(83,false),(88,false),(76,true),(77,false),(64,true)]
theorem der_27765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27765 :=
  CNF.rup_sound cl_27765 [cl_6156,cl_27764] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6156 v h) (hints_cons _ _ _ (der_27764 v h) (by intro d hd; cases hd)))
def cl_27766 : CNF.NClause := [(48,false),(88,false),(17,false),(70,true),(64,false),(77,false),(83,false)]
theorem der_27766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27766 :=
  CNF.rup_sound cl_27766 [cl_6157,cl_6149] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6157 v h) (hints_cons _ _ _ (inp_6149 v h) (by intro d hd; cases hd)))
def cl_27767 : CNF.NClause := [(48,false),(70,true),(88,false),(77,false),(83,false),(76,true),(64,false)]
theorem der_27767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27767 :=
  CNF.rup_sound cl_27767 [cl_6158,cl_27766] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6158 v h) (hints_cons _ _ _ (der_27766 v h) (by intro d hd; cases hd)))
def cl_27768 : CNF.NClause := [(48,false),(88,false),(17,false),(77,false),(64,true),(83,false),(70,true)]
theorem der_27768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27768 :=
  CNF.rup_sound cl_27768 [cl_6159,cl_27761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6159 v h) (hints_cons _ _ _ (der_27761 v h) (by intro d hd; cases hd)))
def cl_27769 : CNF.NClause := [(48,false),(70,true),(17,true),(76,true),(88,false),(77,false),(83,false)]
theorem der_27769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27769 :=
  CNF.rup_sound cl_27769 [cl_6160,cl_27767] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6160 v h) (hints_cons _ _ _ (der_27767 v h) (by intro d hd; cases hd)))
def cl_27770 : CNF.NClause := [(48,false),(17,false),(88,false),(83,false),(77,true),(70,false),(76,false)]
theorem der_27770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27770 :=
  CNF.rup_sound cl_27770 [cl_6163,cl_6161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6163 v h) (hints_cons _ _ _ (inp_6161 v h) (by intro d hd; cases hd)))
def cl_27771 : CNF.NClause := [(48,false),(17,true),(70,false),(88,false),(77,true),(76,false),(83,false)]
theorem der_27771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27771 :=
  CNF.rup_sound cl_27771 [cl_6164,cl_26760] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6164 v h) (hints_cons _ _ _ (der_26760 v h) (by intro d hd; cases hd)))
def cl_27772 : CNF.NClause := [(48,false),(17,false),(64,false),(76,false),(70,true),(83,false),(88,false)]
theorem der_27772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27772 :=
  CNF.rup_sound cl_27772 [cl_6165,cl_6149] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6165 v h) (hints_cons _ _ _ (inp_6149 v h) (by intro d hd; cases hd)))
def cl_27773 : CNF.NClause := [(48,false),(77,true),(64,false),(76,false),(70,true),(83,false),(88,false)]
theorem der_27773 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27773 :=
  CNF.rup_sound cl_27773 [cl_6166,cl_27772] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6166 v h) (hints_cons _ _ _ (der_27772 v h) (by intro d hd; cases hd)))
def cl_27774 : CNF.NClause := [(48,false),(77,true),(17,false),(76,false),(70,true),(83,false),(88,false)]
theorem der_27774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27774 :=
  CNF.rup_sound cl_27774 [cl_6167,cl_27773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6167 v h) (hints_cons _ _ _ (der_27773 v h) (by intro d hd; cases hd)))
def cl_27775 : CNF.NClause := [(48,false),(77,true),(17,true),(76,false),(70,true),(83,false),(88,false)]
theorem der_27775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27775 :=
  CNF.rup_sound cl_27775 [cl_6168,cl_27773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6168 v h) (hints_cons _ _ _ (der_27773 v h) (by intro d hd; cases hd)))
def cl_27776 : CNF.NClause := [(48,false),(17,false),(70,false),(64,false),(76,true),(83,false),(88,false)]
theorem der_27776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27776 :=
  CNF.rup_sound cl_27776 [cl_6169,cl_27764] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6169 v h) (hints_cons _ _ _ (der_27764 v h) (by intro d hd; cases hd)))
def cl_27777 : CNF.NClause := [(48,false),(88,false),(17,false),(64,true),(83,false),(76,true),(70,false)]
theorem der_27777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27777 :=
  CNF.rup_sound cl_27777 [cl_6171,cl_27764] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6171 v h) (hints_cons _ _ _ (der_27764 v h) (by intro d hd; cases hd)))
def cl_27778 : CNF.NClause := [(48,false),(17,true),(70,false),(64,true),(83,false),(77,true),(88,false)]
theorem der_27778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27778 :=
  CNF.rup_sound cl_27778 [cl_6172,cl_27771] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6172 v h) (hints_cons _ _ _ (der_27771 v h) (by intro d hd; cases hd)))
def cl_27779 : CNF.NClause := [(48,false),(77,true),(17,false),(64,false),(70,true),(83,false),(88,false)]
theorem der_27779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27779 :=
  CNF.rup_sound cl_27779 [cl_6173,cl_27773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6173 v h) (hints_cons _ _ _ (der_27773 v h) (by intro d hd; cases hd)))
def cl_27780 : CNF.NClause := [(48,false),(77,true),(17,true),(64,false),(70,true),(83,false),(88,false)]
theorem der_27780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27780 :=
  CNF.rup_sound cl_27780 [cl_6174,cl_27773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6174 v h) (hints_cons _ _ _ (der_27773 v h) (by intro d hd; cases hd)))
def cl_27781 : CNF.NClause := [(48,false),(77,true),(17,false),(76,true),(70,true),(83,false),(88,false)]
theorem der_27781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27781 :=
  CNF.rup_sound cl_27781 [cl_6175,cl_27779] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6175 v h) (hints_cons _ _ _ (der_27779 v h) (by intro d hd; cases hd)))
def cl_27782 : CNF.NClause := [(48,false),(77,true),(64,true),(76,true),(70,true),(83,false),(88,false)]
theorem der_27782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27782 :=
  CNF.rup_sound cl_27782 [cl_6176,cl_27781] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6176 v h) (hints_cons _ _ _ (der_27781 v h) (by intro d hd; cases hd)))
def cl_27783 : CNF.NClause := [(48,false),(83,true),(70,false),(64,false),(77,false),(76,false),(88,false)]
theorem der_27783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27783 :=
  CNF.rup_sound cl_27783 [cl_6177,cl_26340] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6177 v h) (hints_cons _ _ _ (der_26340 v h) (by intro d hd; cases hd)))
def cl_27784 : CNF.NClause := [(48,false),(83,true),(17,false),(76,false),(77,false),(70,false),(88,false)]
theorem der_27784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27784 :=
  CNF.rup_sound cl_27784 [cl_6179,cl_27783] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6179 v h) (hints_cons _ _ _ (der_27783 v h) (by intro d hd; cases hd)))
def cl_27785 : CNF.NClause := [(48,false),(83,true),(70,false),(64,true),(77,false),(76,false),(88,false)]
theorem der_27785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27785 :=
  CNF.rup_sound cl_27785 [cl_6180,cl_27784] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6180 v h) (hints_cons _ _ _ (der_27784 v h) (by intro d hd; cases hd)))
def cl_27786 : CNF.NClause := [(48,false),(83,true),(17,false),(64,false),(76,false),(77,false),(88,false)]
theorem der_27786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27786 :=
  CNF.rup_sound cl_27786 [cl_6181,cl_27784] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6181 v h) (hints_cons _ _ _ (der_27784 v h) (by intro d hd; cases hd)))
def cl_27787 : CNF.NClause := [(48,false),(83,true),(64,false),(76,false),(77,false),(70,true),(88,false)]
theorem der_27787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27787 :=
  CNF.rup_sound cl_27787 [cl_6182,cl_27786] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6182 v h) (hints_cons _ _ _ (der_27786 v h) (by intro d hd; cases hd)))
def cl_27788 : CNF.NClause := [(48,false),(83,true),(17,false),(64,true),(76,false),(77,false),(88,false)]
theorem der_27788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27788 :=
  CNF.rup_sound cl_27788 [cl_6183,cl_27784] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6183 v h) (hints_cons _ _ _ (der_27784 v h) (by intro d hd; cases hd)))
def cl_27789 : CNF.NClause := [(48,false),(83,true),(17,true),(76,false),(77,false),(70,true),(88,false)]
theorem der_27789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27789 :=
  CNF.rup_sound cl_27789 [cl_6184,cl_27787] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6184 v h) (hints_cons _ _ _ (der_27787 v h) (by intro d hd; cases hd)))
def cl_27790 : CNF.NClause := [(48,false),(83,true),(17,false),(70,false),(64,false),(77,false),(88,false)]
theorem der_27790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27790 :=
  CNF.rup_sound cl_27790 [cl_6185,cl_27784] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6185 v h) (hints_cons _ _ _ (der_27784 v h) (by intro d hd; cases hd)))
def cl_27791 : CNF.NClause := [(48,false),(83,true),(17,false),(64,true),(77,false),(70,false),(88,false)]
theorem der_27791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27791 :=
  CNF.rup_sound cl_27791 [cl_6187,cl_27784] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6187 v h) (hints_cons _ _ _ (der_27784 v h) (by intro d hd; cases hd)))
def cl_27792 : CNF.NClause := [(48,false),(83,true),(17,true),(70,false),(77,false),(76,true),(88,false)]
theorem der_27792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27792 :=
  CNF.rup_sound cl_27792 [cl_6188,cl_26340] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6188 v h) (hints_cons _ _ _ (der_26340 v h) (by intro d hd; cases hd)))
def cl_27793 : CNF.NClause := [(48,false),(83,true),(17,false),(64,false),(76,true),(77,false),(88,false)]
theorem der_27793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27793 :=
  CNF.rup_sound cl_27793 [cl_6189,cl_27790] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6189 v h) (hints_cons _ _ _ (der_27790 v h) (by intro d hd; cases hd)))
def cl_27794 : CNF.NClause := [(48,false),(83,true),(64,false),(76,true),(77,false),(70,true),(88,false)]
theorem der_27794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27794 :=
  CNF.rup_sound cl_27794 [cl_6190,cl_27793] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6190 v h) (hints_cons _ _ _ (der_27793 v h) (by intro d hd; cases hd)))
def cl_27795 : CNF.NClause := [(48,false),(83,true),(17,false),(76,true),(77,false),(70,true),(88,false)]
theorem der_27795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27795 :=
  CNF.rup_sound cl_27795 [cl_6191,cl_27793] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6191 v h) (hints_cons _ _ _ (der_27793 v h) (by intro d hd; cases hd)))
def cl_27796 : CNF.NClause := [(48,false),(83,true),(64,true),(76,true),(77,false),(70,true),(88,false)]
theorem der_27796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27796 :=
  CNF.rup_sound cl_27796 [cl_6192,cl_27795] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6192 v h) (hints_cons _ _ _ (der_27795 v h) (by intro d hd; cases hd)))
def cl_27797 : CNF.NClause := [(48,false),(83,true),(17,false),(70,false),(64,false),(76,false),(88,false)]
theorem der_27797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27797 :=
  CNF.rup_sound cl_27797 [cl_6193,cl_27784] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6193 v h) (hints_cons _ _ _ (der_27784 v h) (by intro d hd; cases hd)))
def cl_27798 : CNF.NClause := [(48,false),(83,true),(17,false),(64,true),(76,false),(70,false),(88,false)]
theorem der_27798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27798 :=
  CNF.rup_sound cl_27798 [cl_6195,cl_27784] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6195 v h) (hints_cons _ _ _ (der_27784 v h) (by intro d hd; cases hd)))
def cl_27799 : CNF.NClause := [(48,false),(17,true),(70,false),(64,true),(77,true),(76,false),(88,false)]
theorem der_27799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27799 :=
  CNF.rup_sound cl_27799 [cl_6196,cl_27771] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6196 v h) (hints_cons _ _ _ (der_27771 v h) (by intro d hd; cases hd)))
def cl_27800 : CNF.NClause := [(48,false),(77,true),(17,false),(64,false),(76,false),(70,true),(88,false)]
theorem der_27800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27800 :=
  CNF.rup_sound cl_27800 [cl_6197,cl_27773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6197 v h) (hints_cons _ _ _ (der_27773 v h) (by intro d hd; cases hd)))
def cl_27801 : CNF.NClause := [(48,false),(77,true),(17,true),(64,false),(76,false),(70,true),(88,false)]
theorem der_27801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27801 :=
  CNF.rup_sound cl_27801 [cl_6198,cl_27773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6198 v h) (hints_cons _ _ _ (der_27773 v h) (by intro d hd; cases hd)))
def cl_27802 : CNF.NClause := [(48,false),(77,true),(17,false),(64,true),(76,false),(70,true),(88,false)]
theorem der_27802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27802 :=
  CNF.rup_sound cl_27802 [cl_6199,cl_27774] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6199 v h) (hints_cons _ _ _ (der_27774 v h) (by intro d hd; cases hd)))
def cl_27803 : CNF.NClause := [(48,false),(77,true),(17,true),(64,true),(76,false),(70,true),(88,false)]
theorem der_27803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27803 :=
  CNF.rup_sound cl_27803 [cl_6200,cl_27775] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6200 v h) (hints_cons _ _ _ (der_27775 v h) (by intro d hd; cases hd)))
def cl_27804 : CNF.NClause := [(48,false),(83,true),(17,false),(70,false),(64,false),(76,true),(88,false)]
theorem der_27804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27804 :=
  CNF.rup_sound cl_27804 [cl_6201,cl_27790] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6201 v h) (hints_cons _ _ _ (der_27790 v h) (by intro d hd; cases hd)))
def cl_27805 : CNF.NClause := [(48,false),(17,false),(64,true),(76,true),(77,true),(70,false),(88,false)]
theorem der_27805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27805 :=
  CNF.rup_sound cl_27805 [cl_6203,cl_27777] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6203 v h) (hints_cons _ _ _ (der_27777 v h) (by intro d hd; cases hd)))
def cl_27806 : CNF.NClause := [(48,false),(83,true),(17,true),(70,false),(64,true),(76,true),(88,false)]
theorem der_27806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27806 :=
  CNF.rup_sound cl_27806 [cl_6204,cl_27792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6204 v h) (hints_cons _ _ _ (der_27792 v h) (by intro d hd; cases hd)))
def cl_27807 : CNF.NClause := [(48,false),(77,true),(17,false),(64,false),(76,true),(70,true),(88,false)]
theorem der_27807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27807 :=
  CNF.rup_sound cl_27807 [cl_6205,cl_27779] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6205 v h) (hints_cons _ _ _ (der_27779 v h) (by intro d hd; cases hd)))
def cl_27808 : CNF.NClause := [(48,false),(77,true),(64,false),(76,true),(70,true),(83,true),(88,false)]
theorem der_27808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27808 :=
  CNF.rup_sound cl_27808 [cl_6206,cl_27807] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6206 v h) (hints_cons _ _ _ (der_27807 v h) (by intro d hd; cases hd)))
def cl_27809 : CNF.NClause := [(48,false),(17,false),(64,true),(76,true),(70,true),(83,true),(88,false)]
theorem der_27809 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27809 :=
  CNF.rup_sound cl_27809 [cl_6207,cl_27795] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6207 v h) (hints_cons _ _ _ (der_27795 v h) (by intro d hd; cases hd)))
def cl_27810 : CNF.NClause := [(48,false),(77,true),(17,true),(64,true),(76,true),(83,true),(88,false)]
theorem der_27810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27810 :=
  CNF.rup_sound cl_27810 [cl_6208,cl_27806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6208 v h) (hints_cons _ _ _ (der_27806 v h) (by intro d hd; cases hd)))
def cl_27811 : CNF.NClause := [(48,false),(17,true),(83,false),(76,false),(70,false),(64,false),(77,false)]
theorem der_27811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27811 :=
  CNF.rup_sound cl_27811 [cl_6210,cl_26759] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6210 v h) (hints_cons _ _ _ (der_26759 v h) (by intro d hd; cases hd)))
def cl_27812 : CNF.NClause := [(48,false),(64,true),(17,false),(76,false),(77,false),(70,false),(83,false)]
theorem der_27812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27812 :=
  CNF.rup_sound cl_27812 [cl_6211,cl_6147] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6211 v h) (hints_cons _ _ _ (inp_6147 v h) (by intro d hd; cases hd)))
def cl_27813 : CNF.NClause := [(48,false),(88,true),(17,true),(70,false),(77,false),(83,false),(76,false)]
theorem der_27813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27813 :=
  CNF.rup_sound cl_27813 [cl_6212,cl_27811] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6212 v h) (hints_cons _ _ _ (der_27811 v h) (by intro d hd; cases hd)))
def cl_27814 : CNF.NClause := [(48,false),(17,false),(64,false),(76,false),(77,false),(83,false),(70,true)]
theorem der_27814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27814 :=
  CNF.rup_sound cl_27814 [cl_6213,cl_6149] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6213 v h) (hints_cons _ _ _ (inp_6149 v h) (by intro d hd; cases hd)))
def cl_27815 : CNF.NClause := [(48,false),(88,true),(17,true),(64,false),(76,false),(77,false),(83,false)]
theorem der_27815 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27815 :=
  CNF.rup_sound cl_27815 [cl_6214,cl_27813] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6214 v h) (hints_cons _ _ _ (der_27813 v h) (by intro d hd; cases hd)))
def chunk010 : List CNF.NClause := [cl_27304,cl_27305,cl_27306,cl_27307,cl_27308,cl_27309,cl_27310,cl_27311,cl_27312,cl_27313,cl_27314,cl_27315,cl_27316,cl_27317,cl_27318,cl_27319,cl_27320,cl_27321,cl_27322,cl_27323,cl_27324,cl_27325,cl_27326,cl_27327,cl_27328,cl_27329,cl_27330,cl_27331,cl_27332,cl_27333,cl_27334,cl_27335,cl_27336,cl_27337,cl_27338,cl_27339,cl_27340,cl_27341,cl_27342,cl_27343,cl_27344,cl_27345,cl_27346,cl_27347,cl_27348,cl_27349,cl_27350,cl_27351,cl_27352,cl_27353,cl_27354,cl_27355,cl_27356,cl_27357,cl_27358,cl_27359,cl_27360,cl_27361,cl_27362,cl_27363,cl_27364,cl_27365,cl_27366,cl_27367,cl_27368,cl_27369,cl_27370,cl_27371,cl_27372,cl_27373,cl_27374,cl_27375,cl_27376,cl_27377,cl_27379,cl_27380,cl_27381,cl_27382,cl_27383,cl_27384,cl_27385,cl_27386,cl_27387,cl_27388,cl_27389,cl_27391,cl_27393,cl_27394,cl_27395,cl_27396,cl_27397,cl_27398,cl_27399,cl_27401,cl_27402,cl_27403,cl_27404,cl_27405,cl_27406,cl_27407,cl_27408,cl_27409,cl_27410,cl_27411,cl_27412,cl_27413,cl_27414,cl_27415,cl_27416,cl_27417,cl_27418,cl_27419,cl_27420,cl_27421,cl_27422,cl_27423,cl_27424,cl_27425,cl_27426,cl_27427,cl_27428,cl_27429,cl_27430,cl_27431,cl_27432,cl_27433,cl_27434,cl_27435,cl_27436,cl_27437,cl_27438,cl_27439,cl_27440,cl_27441,cl_27442,cl_27443,cl_27444,cl_27445,cl_27446,cl_27447,cl_27448,cl_27449,cl_27450,cl_27451,cl_27452,cl_27453,cl_27454,cl_27455,cl_27456,cl_27457,cl_27458,cl_27459,cl_27460,cl_27461,cl_27462,cl_27463,cl_27464,cl_27465,cl_27466,cl_27467,cl_27468,cl_27469,cl_27470,cl_27471,cl_27472,cl_27473,cl_27474,cl_27475,cl_27476,cl_27477,cl_27478,cl_27479,cl_27480,cl_27481,cl_27482,cl_27483,cl_27484,cl_27485,cl_27486,cl_27487,cl_27488,cl_27489,cl_27490,cl_27491,cl_27492,cl_27493,cl_27494,cl_27495,cl_27496,cl_27497,cl_27498,cl_27499,cl_27500,cl_27501,cl_27502,cl_27503,cl_27504,cl_27505,cl_27506,cl_27507,cl_27508,cl_27509,cl_27510,cl_27511,cl_27512,cl_27513,cl_27514,cl_27515,cl_27516,cl_27517,cl_27518,cl_27519,cl_27520,cl_27521,cl_27522,cl_27523,cl_27524,cl_27525,cl_27526,cl_27527,cl_27528,cl_27529,cl_27530,cl_27531,cl_27532,cl_27533,cl_27534,cl_27535,cl_27536,cl_27537,cl_27538,cl_27539,cl_27540,cl_27541,cl_27542,cl_27543,cl_27544,cl_27545,cl_27546,cl_27547,cl_27548,cl_27549,cl_27550,cl_27551,cl_27552,cl_27553,cl_27554,cl_27555,cl_27556,cl_27557,cl_27558,cl_27559,cl_27560,cl_27561,cl_27562,cl_27563,cl_27564,cl_27565,cl_27566,cl_27567,cl_27568,cl_27569,cl_27570,cl_27571,cl_27572,cl_27573,cl_27574,cl_27575,cl_27576,cl_27577,cl_27578,cl_27579,cl_27580,cl_27581,cl_27582,cl_27583,cl_27584,cl_27585,cl_27586,cl_27587,cl_27588,cl_27589,cl_27590,cl_27591,cl_27592,cl_27593,cl_27594,cl_27595,cl_27596,cl_27598,cl_27599,cl_27600,cl_27601,cl_27602,cl_27603,cl_27604,cl_27606,cl_27607,cl_27608,cl_27609,cl_27610,cl_27611,cl_27612,cl_27614,cl_27615,cl_27616,cl_27617,cl_27618,cl_27619,cl_27620,cl_27621,cl_27622,cl_27623,cl_27624,cl_27625,cl_27626,cl_27627,cl_27628,cl_27631,cl_27632,cl_27634,cl_27635,cl_27636,cl_27638,cl_27639,cl_27640,cl_27641,cl_27642,cl_27643,cl_27644,cl_27645,cl_27646,cl_27647,cl_27648,cl_27649,cl_27650,cl_27651,cl_27652,cl_27653,cl_27654,cl_27655,cl_27656,cl_27657,cl_27658,cl_27659,cl_27660,cl_27661,cl_27662,cl_27663,cl_27664,cl_27665,cl_27666,cl_27667,cl_27668,cl_27669,cl_27670,cl_27671,cl_27672,cl_27673,cl_27674,cl_27675,cl_27676,cl_27677,cl_27678,cl_27679,cl_27680,cl_27681,cl_27682,cl_27683,cl_27684,cl_27685,cl_27686,cl_27687,cl_27688,cl_27689,cl_27690,cl_27691,cl_27692,cl_27693,cl_27694,cl_27695,cl_27696,cl_27697,cl_27698,cl_27699,cl_27700,cl_27702,cl_27703,cl_27704,cl_27705,cl_27706,cl_27707,cl_27708,cl_27709,cl_27710,cl_27711,cl_27712,cl_27713,cl_27714,cl_27715,cl_27716,cl_27717,cl_27718,cl_27719,cl_27720,cl_27721,cl_27722,cl_27723,cl_27724,cl_27725,cl_27726,cl_27727,cl_27728,cl_27729,cl_27730,cl_27731,cl_27732,cl_27733,cl_27734,cl_27735,cl_27736,cl_27737,cl_27738,cl_27739,cl_27740,cl_27741,cl_27742,cl_27743,cl_27744,cl_27745,cl_27746,cl_27747,cl_27748,cl_27749,cl_27750,cl_27751,cl_27752,cl_27753,cl_27754,cl_27755,cl_27756,cl_27757,cl_27758,cl_27759,cl_27760,cl_27761,cl_27762,cl_27763,cl_27764,cl_27765,cl_27766,cl_27767,cl_27768,cl_27769,cl_27770,cl_27771,cl_27772,cl_27773,cl_27774,cl_27775,cl_27776,cl_27777,cl_27778,cl_27779,cl_27780,cl_27781,cl_27782,cl_27783,cl_27784,cl_27785,cl_27786,cl_27787,cl_27788,cl_27789,cl_27790,cl_27791,cl_27792,cl_27793,cl_27794,cl_27795,cl_27796,cl_27797,cl_27798,cl_27799,cl_27800,cl_27801,cl_27802,cl_27803,cl_27804,cl_27805,cl_27806,cl_27807,cl_27808,cl_27809,cl_27810,cl_27811,cl_27812,cl_27813,cl_27814,cl_27815]
theorem chunk_sound010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk010, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_27304 v h) (hints_cons _ _ _ (der_27305 v h) (hints_cons _ _ _ (der_27306 v h) (hints_cons _ _ _ (der_27307 v h) (hints_cons _ _ _ (der_27308 v h) (hints_cons _ _ _ (der_27309 v h) (hints_cons _ _ _ (der_27310 v h) (hints_cons _ _ _ (der_27311 v h) (hints_cons _ _ _ (der_27312 v h) (hints_cons _ _ _ (der_27313 v h) (hints_cons _ _ _ (der_27314 v h) (hints_cons _ _ _ (der_27315 v h) (hints_cons _ _ _ (der_27316 v h) (hints_cons _ _ _ (der_27317 v h) (hints_cons _ _ _ (der_27318 v h) (hints_cons _ _ _ (der_27319 v h) (hints_cons _ _ _ (der_27320 v h) (hints_cons _ _ _ (der_27321 v h) (hints_cons _ _ _ (der_27322 v h) (hints_cons _ _ _ (der_27323 v h) (hints_cons _ _ _ (der_27324 v h) (hints_cons _ _ _ (der_27325 v h) (hints_cons _ _ _ (der_27326 v h) (hints_cons _ _ _ (der_27327 v h) (hints_cons _ _ _ (der_27328 v h) (hints_cons _ _ _ (der_27329 v h) (hints_cons _ _ _ (der_27330 v h) (hints_cons _ _ _ (der_27331 v h) (hints_cons _ _ _ (der_27332 v h) (hints_cons _ _ _ (der_27333 v h) (hints_cons _ _ _ (der_27334 v h) (hints_cons _ _ _ (der_27335 v h) (hints_cons _ _ _ (der_27336 v h) (hints_cons _ _ _ (der_27337 v h) (hints_cons _ _ _ (der_27338 v h) (hints_cons _ _ _ (der_27339 v h) (hints_cons _ _ _ (der_27340 v h) (hints_cons _ _ _ (der_27341 v h) (hints_cons _ _ _ (der_27342 v h) (hints_cons _ _ _ (der_27343 v h) (hints_cons _ _ _ (der_27344 v h) (hints_cons _ _ _ (der_27345 v h) (hints_cons _ _ _ (der_27346 v h) (hints_cons _ _ _ (der_27347 v h) (hints_cons _ _ _ (der_27348 v h) (hints_cons _ _ _ (der_27349 v h) (hints_cons _ _ _ (der_27350 v h) (hints_cons _ _ _ (der_27351 v h) (hints_cons _ _ _ (der_27352 v h) (hints_cons _ _ _ (der_27353 v h) (hints_cons _ _ _ (der_27354 v h) (hints_cons _ _ _ (der_27355 v h) (hints_cons _ _ _ (der_27356 v h) (hints_cons _ _ _ (der_27357 v h) (hints_cons _ _ _ (der_27358 v h) (hints_cons _ _ _ (der_27359 v h) (hints_cons _ _ _ (der_27360 v h) (hints_cons _ _ _ (der_27361 v h) (hints_cons _ _ _ (der_27362 v h) (hints_cons _ _ _ (der_27363 v h) (hints_cons _ _ _ (der_27364 v h) (hints_cons _ _ _ (der_27365 v h) (hints_cons _ _ _ (der_27366 v h) (hints_cons _ _ _ (der_27367 v h) (hints_cons _ _ _ (der_27368 v h) (hints_cons _ _ _ (der_27369 v h) (hints_cons _ _ _ (der_27370 v h) (hints_cons _ _ _ (der_27371 v h) (hints_cons _ _ _ (der_27372 v h) (hints_cons _ _ _ (der_27373 v h) (hints_cons _ _ _ (der_27374 v h) (hints_cons _ _ _ (der_27375 v h) (hints_cons _ _ _ (der_27376 v h) (hints_cons _ _ _ (der_27377 v h) (hints_cons _ _ _ (der_27379 v h) (hints_cons _ _ _ (der_27380 v h) (hints_cons _ _ _ (der_27381 v h) (hints_cons _ _ _ (der_27382 v h) (hints_cons _ _ _ (der_27383 v h) (hints_cons _ _ _ (der_27384 v h) (hints_cons _ _ _ (der_27385 v h) (hints_cons _ _ _ (der_27386 v h) (hints_cons _ _ _ (der_27387 v h) (hints_cons _ _ _ (der_27388 v h) (hints_cons _ _ _ (der_27389 v h) (hints_cons _ _ _ (der_27391 v h) (hints_cons _ _ _ (der_27393 v h) (hints_cons _ _ _ (der_27394 v h) (hints_cons _ _ _ (der_27395 v h) (hints_cons _ _ _ (der_27396 v h) (hints_cons _ _ _ (der_27397 v h) (hints_cons _ _ _ (der_27398 v h) (hints_cons _ _ _ (der_27399 v h) (hints_cons _ _ _ (der_27401 v h) (hints_cons _ _ _ (der_27402 v h) (hints_cons _ _ _ (der_27403 v h) (hints_cons _ _ _ (der_27404 v h) (hints_cons _ _ _ (der_27405 v h) (hints_cons _ _ _ (der_27406 v h) (hints_cons _ _ _ (der_27407 v h) (hints_cons _ _ _ (der_27408 v h) (hints_cons _ _ _ (der_27409 v h) (hints_cons _ _ _ (der_27410 v h) (hints_cons _ _ _ (der_27411 v h) (hints_cons _ _ _ (der_27412 v h) (hints_cons _ _ _ (der_27413 v h) (hints_cons _ _ _ (der_27414 v h) (hints_cons _ _ _ (der_27415 v h) (hints_cons _ _ _ (der_27416 v h) (hints_cons _ _ _ (der_27417 v h) (hints_cons _ _ _ (der_27418 v h) (hints_cons _ _ _ (der_27419 v h) (hints_cons _ _ _ (der_27420 v h) (hints_cons _ _ _ (der_27421 v h) (hints_cons _ _ _ (der_27422 v h) (hints_cons _ _ _ (der_27423 v h) (hints_cons _ _ _ (der_27424 v h) (hints_cons _ _ _ (der_27425 v h) (hints_cons _ _ _ (der_27426 v h) (hints_cons _ _ _ (der_27427 v h) (hints_cons _ _ _ (der_27428 v h) (hints_cons _ _ _ (der_27429 v h) (hints_cons _ _ _ (der_27430 v h) (hints_cons _ _ _ (der_27431 v h) (hints_cons _ _ _ (der_27432 v h) (hints_cons _ _ _ (der_27433 v h) (hints_cons _ _ _ (der_27434 v h) (hints_cons _ _ _ (der_27435 v h) (hints_cons _ _ _ (der_27436 v h) (hints_cons _ _ _ (der_27437 v h) (hints_cons _ _ _ (der_27438 v h) (hints_cons _ _ _ (der_27439 v h) (hints_cons _ _ _ (der_27440 v h) (hints_cons _ _ _ (der_27441 v h) (hints_cons _ _ _ (der_27442 v h) (hints_cons _ _ _ (der_27443 v h) (hints_cons _ _ _ (der_27444 v h) (hints_cons _ _ _ (der_27445 v h) (hints_cons _ _ _ (der_27446 v h) (hints_cons _ _ _ (der_27447 v h) (hints_cons _ _ _ (der_27448 v h) (hints_cons _ _ _ (der_27449 v h) (hints_cons _ _ _ (der_27450 v h) (hints_cons _ _ _ (der_27451 v h) (hints_cons _ _ _ (der_27452 v h) (hints_cons _ _ _ (der_27453 v h) (hints_cons _ _ _ (der_27454 v h) (hints_cons _ _ _ (der_27455 v h) (hints_cons _ _ _ (der_27456 v h) (hints_cons _ _ _ (der_27457 v h) (hints_cons _ _ _ (der_27458 v h) (hints_cons _ _ _ (der_27459 v h) (hints_cons _ _ _ (der_27460 v h) (hints_cons _ _ _ (der_27461 v h) (hints_cons _ _ _ (der_27462 v h) (hints_cons _ _ _ (der_27463 v h) (hints_cons _ _ _ (der_27464 v h) (hints_cons _ _ _ (der_27465 v h) (hints_cons _ _ _ (der_27466 v h) (hints_cons _ _ _ (der_27467 v h) (hints_cons _ _ _ (der_27468 v h) (hints_cons _ _ _ (der_27469 v h) (hints_cons _ _ _ (der_27470 v h) (hints_cons _ _ _ (der_27471 v h) (hints_cons _ _ _ (der_27472 v h) (hints_cons _ _ _ (der_27473 v h) (hints_cons _ _ _ (der_27474 v h) (hints_cons _ _ _ (der_27475 v h) (hints_cons _ _ _ (der_27476 v h) (hints_cons _ _ _ (der_27477 v h) (hints_cons _ _ _ (der_27478 v h) (hints_cons _ _ _ (der_27479 v h) (hints_cons _ _ _ (der_27480 v h) (hints_cons _ _ _ (der_27481 v h) (hints_cons _ _ _ (der_27482 v h) (hints_cons _ _ _ (der_27483 v h) (hints_cons _ _ _ (der_27484 v h) (hints_cons _ _ _ (der_27485 v h) (hints_cons _ _ _ (der_27486 v h) (hints_cons _ _ _ (der_27487 v h) (hints_cons _ _ _ (der_27488 v h) (hints_cons _ _ _ (der_27489 v h) (hints_cons _ _ _ (der_27490 v h) (hints_cons _ _ _ (der_27491 v h) (hints_cons _ _ _ (der_27492 v h) (hints_cons _ _ _ (der_27493 v h) (hints_cons _ _ _ (der_27494 v h) (hints_cons _ _ _ (der_27495 v h) (hints_cons _ _ _ (der_27496 v h) (hints_cons _ _ _ (der_27497 v h) (hints_cons _ _ _ (der_27498 v h) (hints_cons _ _ _ (der_27499 v h) (hints_cons _ _ _ (der_27500 v h) (hints_cons _ _ _ (der_27501 v h) (hints_cons _ _ _ (der_27502 v h) (hints_cons _ _ _ (der_27503 v h) (hints_cons _ _ _ (der_27504 v h) (hints_cons _ _ _ (der_27505 v h) (hints_cons _ _ _ (der_27506 v h) (hints_cons _ _ _ (der_27507 v h) (hints_cons _ _ _ (der_27508 v h) (hints_cons _ _ _ (der_27509 v h) (hints_cons _ _ _ (der_27510 v h) (hints_cons _ _ _ (der_27511 v h) (hints_cons _ _ _ (der_27512 v h) (hints_cons _ _ _ (der_27513 v h) (hints_cons _ _ _ (der_27514 v h) (hints_cons _ _ _ (der_27515 v h) (hints_cons _ _ _ (der_27516 v h) (hints_cons _ _ _ (der_27517 v h) (hints_cons _ _ _ (der_27518 v h) (hints_cons _ _ _ (der_27519 v h) (hints_cons _ _ _ (der_27520 v h) (hints_cons _ _ _ (der_27521 v h) (hints_cons _ _ _ (der_27522 v h) (hints_cons _ _ _ (der_27523 v h) (hints_cons _ _ _ (der_27524 v h) (hints_cons _ _ _ (der_27525 v h) (hints_cons _ _ _ (der_27526 v h) (hints_cons _ _ _ (der_27527 v h) (hints_cons _ _ _ (der_27528 v h) (hints_cons _ _ _ (der_27529 v h) (hints_cons _ _ _ (der_27530 v h) (hints_cons _ _ _ (der_27531 v h) (hints_cons _ _ _ (der_27532 v h) (hints_cons _ _ _ (der_27533 v h) (hints_cons _ _ _ (der_27534 v h) (hints_cons _ _ _ (der_27535 v h) (hints_cons _ _ _ (der_27536 v h) (hints_cons _ _ _ (der_27537 v h) (hints_cons _ _ _ (der_27538 v h) (hints_cons _ _ _ (der_27539 v h) (hints_cons _ _ _ (der_27540 v h) (hints_cons _ _ _ (der_27541 v h) (hints_cons _ _ _ (der_27542 v h) (hints_cons _ _ _ (der_27543 v h) (hints_cons _ _ _ (der_27544 v h) (hints_cons _ _ _ (der_27545 v h) (hints_cons _ _ _ (der_27546 v h) (hints_cons _ _ _ (der_27547 v h) (hints_cons _ _ _ (der_27548 v h) (hints_cons _ _ _ (der_27549 v h) (hints_cons _ _ _ (der_27550 v h) (hints_cons _ _ _ (der_27551 v h) (hints_cons _ _ _ (der_27552 v h) (hints_cons _ _ _ (der_27553 v h) (hints_cons _ _ _ (der_27554 v h) (hints_cons _ _ _ (der_27555 v h) (hints_cons _ _ _ (der_27556 v h) (hints_cons _ _ _ (der_27557 v h) (hints_cons _ _ _ (der_27558 v h) (hints_cons _ _ _ (der_27559 v h) (hints_cons _ _ _ (der_27560 v h) (hints_cons _ _ _ (der_27561 v h) (hints_cons _ _ _ (der_27562 v h) (hints_cons _ _ _ (der_27563 v h) (hints_cons _ _ _ (der_27564 v h) (hints_cons _ _ _ (der_27565 v h) (hints_cons _ _ _ (der_27566 v h) (hints_cons _ _ _ (der_27567 v h) (hints_cons _ _ _ (der_27568 v h) (hints_cons _ _ _ (der_27569 v h) (hints_cons _ _ _ (der_27570 v h) (hints_cons _ _ _ (der_27571 v h) (hints_cons _ _ _ (der_27572 v h) (hints_cons _ _ _ (der_27573 v h) (hints_cons _ _ _ (der_27574 v h) (hints_cons _ _ _ (der_27575 v h) (hints_cons _ _ _ (der_27576 v h) (hints_cons _ _ _ (der_27577 v h) (hints_cons _ _ _ (der_27578 v h) (hints_cons _ _ _ (der_27579 v h) (hints_cons _ _ _ (der_27580 v h) (hints_cons _ _ _ (der_27581 v h) (hints_cons _ _ _ (der_27582 v h) (hints_cons _ _ _ (der_27583 v h) (hints_cons _ _ _ (der_27584 v h) (hints_cons _ _ _ (der_27585 v h) (hints_cons _ _ _ (der_27586 v h) (hints_cons _ _ _ (der_27587 v h) (hints_cons _ _ _ (der_27588 v h) (hints_cons _ _ _ (der_27589 v h) (hints_cons _ _ _ (der_27590 v h) (hints_cons _ _ _ (der_27591 v h) (hints_cons _ _ _ (der_27592 v h) (hints_cons _ _ _ (der_27593 v h) (hints_cons _ _ _ (der_27594 v h) (hints_cons _ _ _ (der_27595 v h) (hints_cons _ _ _ (der_27596 v h) (hints_cons _ _ _ (der_27598 v h) (hints_cons _ _ _ (der_27599 v h) (hints_cons _ _ _ (der_27600 v h) (hints_cons _ _ _ (der_27601 v h) (hints_cons _ _ _ (der_27602 v h) (hints_cons _ _ _ (der_27603 v h) (hints_cons _ _ _ (der_27604 v h) (hints_cons _ _ _ (der_27606 v h) (hints_cons _ _ _ (der_27607 v h) (hints_cons _ _ _ (der_27608 v h) (hints_cons _ _ _ (der_27609 v h) (hints_cons _ _ _ (der_27610 v h) (hints_cons _ _ _ (der_27611 v h) (hints_cons _ _ _ (der_27612 v h) (hints_cons _ _ _ (der_27614 v h) (hints_cons _ _ _ (der_27615 v h) (hints_cons _ _ _ (der_27616 v h) (hints_cons _ _ _ (der_27617 v h) (hints_cons _ _ _ (der_27618 v h) (hints_cons _ _ _ (der_27619 v h) (hints_cons _ _ _ (der_27620 v h) (hints_cons _ _ _ (der_27621 v h) (hints_cons _ _ _ (der_27622 v h) (hints_cons _ _ _ (der_27623 v h) (hints_cons _ _ _ (der_27624 v h) (hints_cons _ _ _ (der_27625 v h) (hints_cons _ _ _ (der_27626 v h) (hints_cons _ _ _ (der_27627 v h) (hints_cons _ _ _ (der_27628 v h) (hints_cons _ _ _ (der_27631 v h) (hints_cons _ _ _ (der_27632 v h) (hints_cons _ _ _ (der_27634 v h) (hints_cons _ _ _ (der_27635 v h) (hints_cons _ _ _ (der_27636 v h) (hints_cons _ _ _ (der_27638 v h) (hints_cons _ _ _ (der_27639 v h) (hints_cons _ _ _ (der_27640 v h) (hints_cons _ _ _ (der_27641 v h) (hints_cons _ _ _ (der_27642 v h) (hints_cons _ _ _ (der_27643 v h) (hints_cons _ _ _ (der_27644 v h) (hints_cons _ _ _ (der_27645 v h) (hints_cons _ _ _ (der_27646 v h) (hints_cons _ _ _ (der_27647 v h) (hints_cons _ _ _ (der_27648 v h) (hints_cons _ _ _ (der_27649 v h) (hints_cons _ _ _ (der_27650 v h) (hints_cons _ _ _ (der_27651 v h) (hints_cons _ _ _ (der_27652 v h) (hints_cons _ _ _ (der_27653 v h) (hints_cons _ _ _ (der_27654 v h) (hints_cons _ _ _ (der_27655 v h) (hints_cons _ _ _ (der_27656 v h) (hints_cons _ _ _ (der_27657 v h) (hints_cons _ _ _ (der_27658 v h) (hints_cons _ _ _ (der_27659 v h) (hints_cons _ _ _ (der_27660 v h) (hints_cons _ _ _ (der_27661 v h) (hints_cons _ _ _ (der_27662 v h) (hints_cons _ _ _ (der_27663 v h) (hints_cons _ _ _ (der_27664 v h) (hints_cons _ _ _ (der_27665 v h) (hints_cons _ _ _ (der_27666 v h) (hints_cons _ _ _ (der_27667 v h) (hints_cons _ _ _ (der_27668 v h) (hints_cons _ _ _ (der_27669 v h) (hints_cons _ _ _ (der_27670 v h) (hints_cons _ _ _ (der_27671 v h) (hints_cons _ _ _ (der_27672 v h) (hints_cons _ _ _ (der_27673 v h) (hints_cons _ _ _ (der_27674 v h) (hints_cons _ _ _ (der_27675 v h) (hints_cons _ _ _ (der_27676 v h) (hints_cons _ _ _ (der_27677 v h) (hints_cons _ _ _ (der_27678 v h) (hints_cons _ _ _ (der_27679 v h) (hints_cons _ _ _ (der_27680 v h) (hints_cons _ _ _ (der_27681 v h) (hints_cons _ _ _ (der_27682 v h) (hints_cons _ _ _ (der_27683 v h) (hints_cons _ _ _ (der_27684 v h) (hints_cons _ _ _ (der_27685 v h) (hints_cons _ _ _ (der_27686 v h) (hints_cons _ _ _ (der_27687 v h) (hints_cons _ _ _ (der_27688 v h) (hints_cons _ _ _ (der_27689 v h) (hints_cons _ _ _ (der_27690 v h) (hints_cons _ _ _ (der_27691 v h) (hints_cons _ _ _ (der_27692 v h) (hints_cons _ _ _ (der_27693 v h) (hints_cons _ _ _ (der_27694 v h) (hints_cons _ _ _ (der_27695 v h) (hints_cons _ _ _ (der_27696 v h) (hints_cons _ _ _ (der_27697 v h) (hints_cons _ _ _ (der_27698 v h) (hints_cons _ _ _ (der_27699 v h) (hints_cons _ _ _ (der_27700 v h) (hints_cons _ _ _ (der_27702 v h) (hints_cons _ _ _ (der_27703 v h) (hints_cons _ _ _ (der_27704 v h) (hints_cons _ _ _ (der_27705 v h) (hints_cons _ _ _ (der_27706 v h) (hints_cons _ _ _ (der_27707 v h) (hints_cons _ _ _ (der_27708 v h) (hints_cons _ _ _ (der_27709 v h) (hints_cons _ _ _ (der_27710 v h) (hints_cons _ _ _ (der_27711 v h) (hints_cons _ _ _ (der_27712 v h) (hints_cons _ _ _ (der_27713 v h) (hints_cons _ _ _ (der_27714 v h) (hints_cons _ _ _ (der_27715 v h) (hints_cons _ _ _ (der_27716 v h) (hints_cons _ _ _ (der_27717 v h) (hints_cons _ _ _ (der_27718 v h) (hints_cons _ _ _ (der_27719 v h) (hints_cons _ _ _ (der_27720 v h) (hints_cons _ _ _ (der_27721 v h) (hints_cons _ _ _ (der_27722 v h) (hints_cons _ _ _ (der_27723 v h) (hints_cons _ _ _ (der_27724 v h) (hints_cons _ _ _ (der_27725 v h) (hints_cons _ _ _ (der_27726 v h) (hints_cons _ _ _ (der_27727 v h) (hints_cons _ _ _ (der_27728 v h) (hints_cons _ _ _ (der_27729 v h) (hints_cons _ _ _ (der_27730 v h) (hints_cons _ _ _ (der_27731 v h) (hints_cons _ _ _ (der_27732 v h) (hints_cons _ _ _ (der_27733 v h) (hints_cons _ _ _ (der_27734 v h) (hints_cons _ _ _ (der_27735 v h) (hints_cons _ _ _ (der_27736 v h) (hints_cons _ _ _ (der_27737 v h) (hints_cons _ _ _ (der_27738 v h) (hints_cons _ _ _ (der_27739 v h) (hints_cons _ _ _ (der_27740 v h) (hints_cons _ _ _ (der_27741 v h) (hints_cons _ _ _ (der_27742 v h) (hints_cons _ _ _ (der_27743 v h) (hints_cons _ _ _ (der_27744 v h) (hints_cons _ _ _ (der_27745 v h) (hints_cons _ _ _ (der_27746 v h) (hints_cons _ _ _ (der_27747 v h) (hints_cons _ _ _ (der_27748 v h) (hints_cons _ _ _ (der_27749 v h) (hints_cons _ _ _ (der_27750 v h) (hints_cons _ _ _ (der_27751 v h) (hints_cons _ _ _ (der_27752 v h) (hints_cons _ _ _ (der_27753 v h) (hints_cons _ _ _ (der_27754 v h) (hints_cons _ _ _ (der_27755 v h) (hints_cons _ _ _ (der_27756 v h) (hints_cons _ _ _ (der_27757 v h) (hints_cons _ _ _ (der_27758 v h) (hints_cons _ _ _ (der_27759 v h) (hints_cons _ _ _ (der_27760 v h) (hints_cons _ _ _ (der_27761 v h) (hints_cons _ _ _ (der_27762 v h) (hints_cons _ _ _ (der_27763 v h) (hints_cons _ _ _ (der_27764 v h) (hints_cons _ _ _ (der_27765 v h) (hints_cons _ _ _ (der_27766 v h) (hints_cons _ _ _ (der_27767 v h) (hints_cons _ _ _ (der_27768 v h) (hints_cons _ _ _ (der_27769 v h) (hints_cons _ _ _ (der_27770 v h) (hints_cons _ _ _ (der_27771 v h) (hints_cons _ _ _ (der_27772 v h) (hints_cons _ _ _ (der_27773 v h) (hints_cons _ _ _ (der_27774 v h) (hints_cons _ _ _ (der_27775 v h) (hints_cons _ _ _ (der_27776 v h) (hints_cons _ _ _ (der_27777 v h) (hints_cons _ _ _ (der_27778 v h) (hints_cons _ _ _ (der_27779 v h) (hints_cons _ _ _ (der_27780 v h) (hints_cons _ _ _ (der_27781 v h) (hints_cons _ _ _ (der_27782 v h) (hints_cons _ _ _ (der_27783 v h) (hints_cons _ _ _ (der_27784 v h) (hints_cons _ _ _ (der_27785 v h) (hints_cons _ _ _ (der_27786 v h) (hints_cons _ _ _ (der_27787 v h) (hints_cons _ _ _ (der_27788 v h) (hints_cons _ _ _ (der_27789 v h) (hints_cons _ _ _ (der_27790 v h) (hints_cons _ _ _ (der_27791 v h) (hints_cons _ _ _ (der_27792 v h) (hints_cons _ _ _ (der_27793 v h) (hints_cons _ _ _ (der_27794 v h) (hints_cons _ _ _ (der_27795 v h) (hints_cons _ _ _ (der_27796 v h) (hints_cons _ _ _ (der_27797 v h) (hints_cons _ _ _ (der_27798 v h) (hints_cons _ _ _ (der_27799 v h) (hints_cons _ _ _ (der_27800 v h) (hints_cons _ _ _ (der_27801 v h) (hints_cons _ _ _ (der_27802 v h) (hints_cons _ _ _ (der_27803 v h) (hints_cons _ _ _ (der_27804 v h) (hints_cons _ _ _ (der_27805 v h) (hints_cons _ _ _ (der_27806 v h) (hints_cons _ _ _ (der_27807 v h) (hints_cons _ _ _ (der_27808 v h) (hints_cons _ _ _ (der_27809 v h) (hints_cons _ _ _ (der_27810 v h) (hints_cons _ _ _ (der_27811 v h) (hints_cons _ _ _ (der_27812 v h) (hints_cons _ _ _ (der_27813 v h) (hints_cons _ _ _ (der_27814 v h) (hints_cons _ _ _ (der_27815 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix010 := prefix009 ++ chunk010
theorem prefix_sound010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix010, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound009 v h c hc
  · exact chunk_sound010 v h c hc
end Percolation.NReplay
