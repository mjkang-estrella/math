import NReplay007
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_26275 : CNF.NClause := [(117,true),(36,false),(45,false),(49,false),(53,false),(60,false)]
theorem der_26275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26275 :=
  CNF.rup_sound cl_26275 [cl_3522,cl_25830] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3522 v h) (hints_cons _ _ _ (der_25830 v h) (by intro d hd; cases hd)))
def cl_26276 : CNF.NClause := [(117,true),(45,false),(36,true),(49,false),(60,false),(53,false)]
theorem der_26276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26276 :=
  CNF.rup_sound cl_26276 [cl_3524,cl_3523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3524 v h) (hints_cons _ _ _ (inp_3523 v h) (by intro d hd; cases hd)))
def cl_26277 : CNF.NClause := [(117,true),(49,false),(36,false),(45,true),(53,false),(60,false)]
theorem der_26277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26277 :=
  CNF.rup_sound cl_26277 [cl_3526,cl_25824] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3526 v h) (hints_cons _ _ _ (der_25824 v h) (by intro d hd; cases hd)))
def cl_26278 : CNF.NClause := [(117,true),(49,false),(53,false),(36,true),(45,true),(60,false)]
theorem der_26278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26278 :=
  CNF.rup_sound cl_26278 [cl_3528,cl_24881] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3528 v h) (hints_cons _ _ _ (der_24881 v h) (by intro d hd; cases hd)))
def cl_26279 : CNF.NClause := [(117,true),(36,false),(45,false),(49,true),(53,false),(60,false)]
theorem der_26279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26279 :=
  CNF.rup_sound cl_26279 [cl_3530,cl_23904] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3530 v h) (hints_cons _ _ _ (der_23904 v h) (by intro d hd; cases hd)))
def cl_26280 : CNF.NClause := [(117,true),(36,true),(45,false),(32,true),(53,false),(60,false)]
theorem der_26280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26280 :=
  CNF.rup_sound cl_26280 [cl_3532,cl_26276] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3532 v h) (hints_cons _ _ _ (der_26276 v h) (by intro d hd; cases hd)))
def cl_26281 : CNF.NClause := [(117,true),(36,false),(45,true),(32,true),(53,false),(60,false)]
theorem der_26281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26281 :=
  CNF.rup_sound cl_26281 [cl_3534,cl_26277] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3534 v h) (hints_cons _ _ _ (der_26277 v h) (by intro d hd; cases hd)))
def cl_26282 : CNF.NClause := [(117,true),(49,true),(36,true),(45,true),(53,false),(60,false)]
theorem der_26282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26282 :=
  CNF.rup_sound cl_26282 [cl_3536,cl_24883] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3536 v h) (hints_cons _ _ _ (der_24883 v h) (by intro d hd; cases hd)))
def cl_26283 : CNF.NClause := [(117,true),(36,false),(45,false),(49,false),(53,true),(60,false)]
theorem der_26283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26283 :=
  CNF.rup_sound cl_26283 [cl_3538,cl_3537] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3538 v h) (hints_cons _ _ _ (inp_3537 v h) (by intro d hd; cases hd)))
def cl_26284 : CNF.NClause := [(117,true),(49,false),(45,false),(32,true),(60,false),(36,true)]
theorem der_26284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26284 :=
  CNF.rup_sound cl_26284 [cl_3540,cl_26276] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3540 v h) (hints_cons _ _ _ (der_26276 v h) (by intro d hd; cases hd)))
def cl_26285 : CNF.NClause := [(117,true),(49,false),(36,false),(45,true),(60,false),(53,true)]
theorem der_26285 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26285 :=
  CNF.rup_sound cl_26285 [cl_3542,cl_25825] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3542 v h) (hints_cons _ _ _ (der_25825 v h) (by intro d hd; cases hd)))
def cl_26286 : CNF.NClause := [(117,true),(49,false),(45,true),(32,true),(36,true),(60,false)]
theorem der_26286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26286 :=
  CNF.rup_sound cl_26286 [cl_3544,cl_26278] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3544 v h) (hints_cons _ _ _ (der_26278 v h) (by intro d hd; cases hd)))
def cl_26287 : CNF.NClause := [(117,true),(36,false),(45,false),(49,true),(53,true),(60,false)]
theorem der_26287 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26287 :=
  CNF.rup_sound cl_26287 [cl_3546,cl_23752] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3546 v h) (hints_cons _ _ _ (der_23752 v h) (by intro d hd; cases hd)))
def cl_26288 : CNF.NClause := [(117,true),(60,false),(45,false),(32,true),(49,true),(36,true)]
theorem der_26288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26288 :=
  CNF.rup_sound cl_26288 [cl_3548,cl_26280] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3548 v h) (hints_cons _ _ _ (der_26280 v h) (by intro d hd; cases hd)))
def cl_26289 : CNF.NClause := [(117,true),(49,true),(36,false),(32,true),(53,true),(60,false)]
theorem der_26289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26289 :=
  CNF.rup_sound cl_26289 [cl_3550,cl_26287] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3550 v h) (hints_cons _ _ _ (der_26287 v h) (by intro d hd; cases hd)))
def cl_26290 : CNF.NClause := [(117,true),(36,false),(45,false),(49,false),(53,false),(60,true)]
theorem der_26290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26290 :=
  CNF.rup_sound cl_26290 [cl_3554,cl_25831] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3554 v h) (hints_cons _ _ _ (der_25831 v h) (by intro d hd; cases hd)))
def cl_26291 : CNF.NClause := [(117,true),(49,false),(45,false),(36,true),(32,true),(53,false)]
theorem der_26291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26291 :=
  CNF.rup_sound cl_26291 [cl_3556,cl_26276] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3556 v h) (hints_cons _ _ _ (der_26276 v h) (by intro d hd; cases hd)))
def cl_26292 : CNF.NClause := [(117,true),(49,false),(36,false),(45,true),(53,false),(60,true)]
theorem der_26292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26292 :=
  CNF.rup_sound cl_26292 [cl_3558,cl_25829] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3558 v h) (hints_cons _ _ _ (der_25829 v h) (by intro d hd; cases hd)))
def cl_26293 : CNF.NClause := [(117,true),(49,false),(53,false),(32,true),(45,true),(36,true)]
theorem der_26293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26293 :=
  CNF.rup_sound cl_26293 [cl_3560,cl_26278] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3560 v h) (hints_cons _ _ _ (der_26278 v h) (by intro d hd; cases hd)))
def cl_26294 : CNF.NClause := [(117,true),(49,true),(36,false),(45,false),(53,false),(60,true)]
theorem der_26294 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26294 :=
  CNF.rup_sound cl_26294 [cl_3562,cl_23901] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3562 v h) (hints_cons _ _ _ (der_23901 v h) (by intro d hd; cases hd)))
def cl_26295 : CNF.NClause := [(117,true),(49,true),(36,true),(45,false),(32,true),(53,false)]
theorem der_26295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26295 :=
  CNF.rup_sound cl_26295 [cl_3564,cl_26280] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3564 v h) (hints_cons _ _ _ (der_26280 v h) (by intro d hd; cases hd)))
def cl_26296 : CNF.NClause := [(117,true),(36,false),(45,true),(32,true),(53,false),(60,true)]
theorem der_26296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26296 :=
  CNF.rup_sound cl_26296 [cl_3566,cl_26292] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3566 v h) (hints_cons _ _ _ (der_26292 v h) (by intro d hd; cases hd)))
def cl_26297 : CNF.NClause := [(117,true),(32,true),(36,false),(45,false),(49,false),(60,true)]
theorem der_26297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26297 :=
  CNF.rup_sound cl_26297 [cl_3570,cl_26290] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3570 v h) (hints_cons _ _ _ (der_26290 v h) (by intro d hd; cases hd)))
def cl_26298 : CNF.NClause := [(117,true),(49,false),(32,true),(36,true),(53,true),(45,false)]
theorem der_26298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26298 :=
  CNF.rup_sound cl_26298 [cl_3572,cl_26284] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3572 v h) (hints_cons _ _ _ (der_26284 v h) (by intro d hd; cases hd)))
def cl_26299 : CNF.NClause := [(117,true),(45,true),(36,false),(49,false),(53,true),(60,true)]
theorem der_26299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26299 :=
  CNF.rup_sound cl_26299 [cl_3574,cl_25826] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3574 v h) (hints_cons _ _ _ (der_25826 v h) (by intro d hd; cases hd)))
def cl_26300 : CNF.NClause := [(117,true),(36,false),(45,false),(49,true),(53,true),(60,true)]
theorem der_26300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26300 :=
  CNF.rup_sound cl_26300 [cl_3578,cl_23901] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3578 v h) (hints_cons _ _ _ (der_23901 v h) (by intro d hd; cases hd)))
def cl_26301 : CNF.NClause := [(118,true),(34,false),(35,false),(33,true),(31,true),(61,true)]
theorem der_26301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26301 :=
  CNF.rup_sound cl_26301 [cl_3624,cl_25776] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3624 v h) (hints_cons _ _ _ (der_25776 v h) (by intro d hd; cases hd)))
def cl_26302 : CNF.NClause := [(118,true),(33,false),(31,true),(34,false),(35,false),(61,true)]
theorem der_26302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26302 :=
  CNF.rup_sound cl_26302 [cl_3620,cl_3618] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3620 v h) (hints_cons _ _ _ (inp_3618 v h) (by intro d hd; cases hd)))
def cl_26303 : CNF.NClause := [(47,false),(66,false),(16,true),(68,true),(77,false),(84,false),(89,false)]
theorem der_26303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26303 :=
  CNF.rup_sound cl_26303 [cl_6030,cl_6022] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6030 v h) (hints_cons _ _ _ (inp_6022 v h) (by intro d hd; cases hd)))
def cl_26304 : CNF.NClause := [(47,false),(84,false),(16,true),(68,true),(66,false),(75,false),(89,false)]
theorem der_26304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26304 :=
  CNF.rup_sound cl_26304 [cl_6038,cl_26303] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6038 v h) (hints_cons _ _ _ (der_26303 v h) (by intro d hd; cases hd)))
def cl_26305 : CNF.NClause := [(47,false),(75,true),(66,false),(16,true),(68,true),(84,false),(89,false)]
theorem der_26305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26305 :=
  CNF.rup_sound cl_26305 [cl_6046,cl_26303] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6046 v h) (hints_cons _ _ _ (der_26303 v h) (by intro d hd; cases hd)))
def cl_26306 : CNF.NClause := [(47,false),(66,false),(16,true),(68,true),(77,false),(75,false),(89,false)]
theorem der_26306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26306 :=
  CNF.rup_sound cl_26306 [cl_6054,cl_26303] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6054 v h) (hints_cons _ _ _ (der_26303 v h) (by intro d hd; cases hd)))
def cl_26307 : CNF.NClause := [(47,false),(66,false),(16,true),(68,true),(77,false),(75,true),(89,false)]
theorem der_26307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26307 :=
  CNF.rup_sound cl_26307 [cl_6062,cl_26303] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6062 v h) (hints_cons _ _ _ (der_26303 v h) (by intro d hd; cases hd)))
def cl_26308 : CNF.NClause := [(47,false),(66,false),(16,true),(68,true),(75,false),(77,true),(89,false)]
theorem der_26308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26308 :=
  CNF.rup_sound cl_26308 [cl_6070,cl_26304] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6070 v h) (hints_cons _ _ _ (der_26304 v h) (by intro d hd; cases hd)))
def cl_26309 : CNF.NClause := [(47,false),(66,false),(16,true),(68,true),(77,true),(84,true),(89,false)]
theorem der_26309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26309 :=
  CNF.rup_sound cl_26309 [cl_6078,cl_26308] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6078 v h) (hints_cons _ _ _ (der_26308 v h) (by intro d hd; cases hd)))
def cl_26310 : CNF.NClause := [(47,false),(68,true),(66,false),(16,true),(77,false),(84,false),(75,false)]
theorem der_26310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26310 :=
  CNF.rup_sound cl_26310 [cl_6086,cl_26303] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6086 v h) (hints_cons _ _ _ (der_26303 v h) (by intro d hd; cases hd)))
def cl_26311 : CNF.NClause := [(47,false),(66,false),(16,true),(68,true),(77,false),(84,false),(89,true)]
theorem der_26311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26311 :=
  CNF.rup_sound cl_26311 [cl_6094,cl_26310] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6094 v h) (hints_cons _ _ _ (der_26310 v h) (by intro d hd; cases hd)))
def cl_26312 : CNF.NClause := [(47,false),(68,true),(66,false),(16,true),(89,true),(84,false),(75,false)]
theorem der_26312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26312 :=
  CNF.rup_sound cl_26312 [cl_6102,cl_26311] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6102 v h) (hints_cons _ _ _ (der_26311 v h) (by intro d hd; cases hd)))
def cl_26313 : CNF.NClause := [(47,false),(75,true),(66,false),(16,true),(68,true),(77,true),(84,false)]
theorem der_26313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26313 :=
  CNF.rup_sound cl_26313 [cl_6110,cl_26305] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6110 v h) (hints_cons _ _ _ (der_26305 v h) (by intro d hd; cases hd)))
def cl_26314 : CNF.NClause := [(47,false),(68,true),(66,false),(16,true),(89,true),(77,false),(75,false)]
theorem der_26314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26314 :=
  CNF.rup_sound cl_26314 [cl_6118,cl_26311] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6118 v h) (hints_cons _ _ _ (der_26311 v h) (by intro d hd; cases hd)))
def cl_26315 : CNF.NClause := [(47,false),(84,true),(66,false),(16,true),(68,true),(77,false),(89,true)]
theorem der_26315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26315 :=
  CNF.rup_sound cl_26315 [cl_6126,cl_26314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6126 v h) (hints_cons _ _ _ (der_26314 v h) (by intro d hd; cases hd)))
def cl_26316 : CNF.NClause := [(47,false),(68,true),(66,false),(16,true),(77,true),(84,true),(75,false)]
theorem der_26316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26316 :=
  CNF.rup_sound cl_26316 [cl_6134,cl_26309] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6134 v h) (hints_cons _ _ _ (der_26309 v h) (by intro d hd; cases hd)))
def cl_26317 : CNF.NClause := [(47,false),(75,true),(66,false),(16,true),(68,true),(77,true),(84,true)]
theorem der_26317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26317 :=
  CNF.rup_sound cl_26317 [cl_6142,cl_26309] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6142 v h) (hints_cons _ _ _ (der_26309 v h) (by intro d hd; cases hd)))
def cl_26318 : CNF.NClause := [(49,false),(18,true),(86,false),(65,false),(69,false),(73,false),(91,true)]
theorem der_26318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26318 :=
  CNF.rup_sound cl_26318 [cl_6354,cl_6338] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6354 v h) (hints_cons _ _ _ (inp_6338 v h) (by intro d hd; cases hd)))
def cl_26319 : CNF.NClause := [(49,false),(77,true),(86,false),(73,false),(69,false),(65,false),(91,true)]
theorem der_26319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26319 :=
  CNF.rup_sound cl_26319 [cl_6353,cl_26318] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6353 v h) (hints_cons _ _ _ (der_26318 v h) (by intro d hd; cases hd)))
def cl_26320 : CNF.NClause := [(50,false),(74,false),(19,true),(63,false),(85,false),(90,false),(71,false)]
theorem der_26320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26320 :=
  CNF.rup_sound cl_26320 [cl_6418,cl_6402] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6418 v h) (hints_cons _ _ _ (inp_6402 v h) (by intro d hd; cases hd)))
def cl_26321 : CNF.NClause := [(50,false),(77,true),(63,false),(71,false),(85,false),(74,false),(90,false)]
theorem der_26321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26321 :=
  CNF.rup_sound cl_26321 [cl_6417,cl_26320] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6417 v h) (hints_cons _ _ _ (der_26320 v h) (by intro d hd; cases hd)))
def cl_26322 : CNF.NClause := [(33,false),(79,false),(2,true),(64,true),(84,false),(69,false),(74,false)]
theorem der_26322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26322 :=
  CNF.rup_sound cl_26322 [cl_4292,cl_4228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4292 v h) (hints_cons _ _ _ (inp_4228 v h) (by intro d hd; cases hd)))
def cl_26323 : CNF.NClause := [(33,false),(2,true),(84,false),(79,false),(87,false),(69,false),(74,false)]
theorem der_26323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26323 :=
  CNF.rup_sound cl_26323 [cl_4226,cl_4228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4226 v h) (hints_cons _ _ _ (inp_4228 v h) (by intro d hd; cases hd)))
def cl_26324 : CNF.NClause := [(35,false),(63,true),(4,true),(78,false),(83,false),(73,false),(68,false)]
theorem der_26324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26324 :=
  CNF.rup_sound cl_26324 [cl_4548,cl_4484] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4548 v h) (hints_cons _ _ _ (inp_4484 v h) (by intro d hd; cases hd)))
def cl_26325 : CNF.NClause := [(46,false),(15,false),(92,false),(79,false),(77,true),(78,false),(81,false)]
theorem der_26325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26325 :=
  CNF.rup_sound cl_26325 [cl_5907,cl_5891] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5907 v h) (hints_cons _ _ _ (inp_5891 v h) (by intro d hd; cases hd)))
def cl_26326 : CNF.NClause := [(46,false),(15,false),(77,true),(79,false),(78,false),(80,true),(92,false)]
theorem der_26326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26326 :=
  CNF.rup_sound cl_26326 [cl_5939,cl_26325] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5939 v h) (hints_cons _ _ _ (der_26325 v h) (by intro d hd; cases hd)))
def cl_26327 : CNF.NClause := [(46,false),(77,true),(15,false),(81,false),(79,false),(78,false),(80,false)]
theorem der_26327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26327 :=
  CNF.rup_sound cl_26327 [cl_5955,cl_5891] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5955 v h) (hints_cons _ _ _ (inp_5891 v h) (by intro d hd; cases hd)))
def cl_26328 : CNF.NClause := [(46,false),(77,true),(15,false),(79,false),(78,false),(81,false),(92,true)]
theorem der_26328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26328 :=
  CNF.rup_sound cl_26328 [cl_5971,cl_26327] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5971 v h) (hints_cons _ _ _ (der_26327 v h) (by intro d hd; cases hd)))
def cl_26329 : CNF.NClause := [(46,false),(15,false),(77,true),(79,false),(78,false),(80,true),(92,true)]
theorem der_26329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26329 :=
  CNF.rup_sound cl_26329 [cl_6003,cl_26328] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6003 v h) (hints_cons _ _ _ (der_26328 v h) (by intro d hd; cases hd)))
def cl_26330 : CNF.NClause := [(37,false),(66,true),(6,true),(74,false),(70,false),(78,false),(91,false)]
theorem der_26330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26330 :=
  CNF.rup_sound cl_26330 [cl_4772,cl_4740] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4772 v h) (hints_cons _ _ _ (inp_4740 v h) (by intro d hd; cases hd)))
def cl_26331 : CNF.NClause := [(59,false),(28,true),(81,false),(73,false),(84,false),(62,true),(70,false)]
theorem der_26331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26331 :=
  CNF.rup_sound cl_26331 [cl_7620,cl_7556] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7620 v h) (hints_cons _ _ _ (inp_7556 v h) (by intro d hd; cases hd)))
def cl_26332 : CNF.NClause := [(59,false),(90,true),(28,true),(70,false),(62,true),(84,false),(81,false)]
theorem der_26332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26332 :=
  CNF.rup_sound cl_26332 [cl_7628,cl_26331] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7628 v h) (hints_cons _ _ _ (der_26331 v h) (by intro d hd; cases hd)))
def cl_26333 : CNF.NClause := [(59,false),(28,true),(70,false),(73,false),(62,true),(84,false),(90,true)]
theorem der_26333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26333 :=
  CNF.rup_sound cl_26333 [cl_7636,cl_26331] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7636 v h) (hints_cons _ _ _ (der_26331 v h) (by intro d hd; cases hd)))
def cl_26334 : CNF.NClause := [(59,false),(81,true),(28,true),(70,false),(62,true),(84,false),(90,true)]
theorem der_26334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26334 :=
  CNF.rup_sound cl_26334 [cl_7644,cl_26333] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7644 v h) (hints_cons _ _ _ (der_26333 v h) (by intro d hd; cases hd)))
def cl_26335 : CNF.NClause := [(59,false),(28,true),(70,false),(73,false),(81,false),(62,true),(90,true)]
theorem der_26335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26335 :=
  CNF.rup_sound cl_26335 [cl_7652,cl_26331] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7652 v h) (hints_cons _ _ _ (der_26331 v h) (by intro d hd; cases hd)))
def cl_26336 : CNF.NClause := [(59,false),(84,true),(28,true),(70,false),(62,true),(81,false),(90,true)]
theorem der_26336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26336 :=
  CNF.rup_sound cl_26336 [cl_7660,cl_26335] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7660 v h) (hints_cons _ _ _ (der_26335 v h) (by intro d hd; cases hd)))
def cl_26337 : CNF.NClause := [(59,false),(28,true),(70,false),(73,false),(62,true),(81,true),(90,true)]
theorem der_26337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26337 :=
  CNF.rup_sound cl_26337 [cl_7668,cl_26334] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7668 v h) (hints_cons _ _ _ (der_26334 v h) (by intro d hd; cases hd)))
def cl_26338 : CNF.NClause := [(59,false),(81,true),(28,true),(70,false),(73,true),(62,true),(90,true)]
theorem der_26338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26338 :=
  CNF.rup_sound cl_26338 [cl_7676,cl_26334] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7676 v h) (hints_cons _ _ _ (der_26334 v h) (by intro d hd; cases hd)))
def cl_26339 : CNF.NClause := [(48,false),(17,true),(64,false),(88,false),(76,true),(70,false),(83,false)]
theorem der_26339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26339 :=
  CNF.rup_sound cl_26339 [cl_6170,cl_6154] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6170 v h) (hints_cons _ _ _ (inp_6154 v h) (by intro d hd; cases hd)))
def cl_26340 : CNF.NClause := [(48,false),(83,true),(17,true),(64,false),(77,false),(70,false),(88,false)]
theorem der_26340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26340 :=
  CNF.rup_sound cl_26340 [cl_6186,cl_6178] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6186 v h) (hints_cons _ _ _ (inp_6178 v h) (by intro d hd; cases hd)))
def cl_26341 : CNF.NClause := [(48,false),(83,true),(17,true),(64,false),(76,false),(70,false),(88,false)]
theorem der_26341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26341 :=
  CNF.rup_sound cl_26341 [cl_6194,cl_26340] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6194 v h) (hints_cons _ _ _ (der_26340 v h) (by intro d hd; cases hd)))
def cl_26342 : CNF.NClause := [(48,false),(83,true),(17,true),(64,false),(76,true),(70,false),(88,false)]
theorem der_26342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26342 :=
  CNF.rup_sound cl_26342 [cl_6202,cl_26340] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6202 v h) (hints_cons _ _ _ (der_26340 v h) (by intro d hd; cases hd)))
def cl_26343 : CNF.NClause := [(48,false),(17,true),(64,false),(76,true),(77,false),(70,false),(83,false)]
theorem der_26343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26343 :=
  CNF.rup_sound cl_26343 [cl_6218,cl_6154] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6218 v h) (hints_cons _ _ _ (inp_6154 v h) (by intro d hd; cases hd)))
def cl_26344 : CNF.NClause := [(48,false),(17,true),(83,false),(76,true),(64,false),(70,false),(77,true)]
theorem der_26344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26344 :=
  CNF.rup_sound cl_26344 [cl_6234,cl_26339] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6234 v h) (hints_cons _ _ _ (der_26339 v h) (by intro d hd; cases hd)))
def cl_26345 : CNF.NClause := [(48,false),(83,true),(17,true),(64,false),(76,false),(77,false),(70,false)]
theorem der_26345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26345 :=
  CNF.rup_sound cl_26345 [cl_6242,cl_26340] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6242 v h) (hints_cons _ _ _ (der_26340 v h) (by intro d hd; cases hd)))
def cl_26346 : CNF.NClause := [(48,false),(17,true),(64,false),(76,true),(77,false),(70,false),(88,true)]
theorem der_26346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26346 :=
  CNF.rup_sound cl_26346 [cl_6250,cl_26343] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6250 v h) (hints_cons _ _ _ (der_26343 v h) (by intro d hd; cases hd)))
def cl_26347 : CNF.NClause := [(48,false),(83,true),(17,true),(64,false),(76,false),(70,false),(88,true)]
theorem der_26347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26347 :=
  CNF.rup_sound cl_26347 [cl_6258,cl_26345] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6258 v h) (hints_cons _ _ _ (der_26345 v h) (by intro d hd; cases hd)))
def cl_26348 : CNF.NClause := [(48,false),(17,true),(64,false),(76,true),(77,true),(70,false),(88,true)]
theorem der_26348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26348 :=
  CNF.rup_sound cl_26348 [cl_6266,cl_26344] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6266 v h) (hints_cons _ _ _ (der_26344 v h) (by intro d hd; cases hd)))
def cl_26349 : CNF.NClause := [(52,false),(67,true),(21,true),(66,false),(88,false),(79,false),(85,false)]
theorem der_26349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26349 :=
  CNF.rup_sound cl_26349 [cl_6670,cl_6662] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6670 v h) (hints_cons _ _ _ (inp_6662 v h) (by intro d hd; cases hd)))
def cl_26350 : CNF.NClause := [(52,false),(21,true),(66,false),(73,false),(67,true),(85,false),(88,false)]
theorem der_26350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26350 :=
  CNF.rup_sound cl_26350 [cl_6678,cl_6662] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6678 v h) (hints_cons _ _ _ (inp_6662 v h) (by intro d hd; cases hd)))
def cl_26351 : CNF.NClause := [(52,false),(79,true),(21,true),(66,false),(67,true),(85,false),(88,false)]
theorem der_26351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26351 :=
  CNF.rup_sound cl_26351 [cl_6686,cl_26350] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6686 v h) (hints_cons _ _ _ (der_26350 v h) (by intro d hd; cases hd)))
def cl_26352 : CNF.NClause := [(52,false),(21,true),(67,true),(73,false),(79,false),(66,false),(88,false)]
theorem der_26352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26352 :=
  CNF.rup_sound cl_26352 [cl_6694,cl_6662] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6694 v h) (hints_cons _ _ _ (inp_6662 v h) (by intro d hd; cases hd)))
def cl_26353 : CNF.NClause := [(52,false),(67,true),(21,true),(66,false),(88,false),(79,false),(85,true)]
theorem der_26353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26353 :=
  CNF.rup_sound cl_26353 [cl_6702,cl_26352] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6702 v h) (hints_cons _ _ _ (der_26352 v h) (by intro d hd; cases hd)))
def cl_26354 : CNF.NClause := [(52,false),(79,true),(21,true),(66,false),(73,false),(67,true),(88,false)]
theorem der_26354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26354 :=
  CNF.rup_sound cl_26354 [cl_6710,cl_26350] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6710 v h) (hints_cons _ _ _ (der_26350 v h) (by intro d hd; cases hd)))
def cl_26355 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,true),(85,true),(88,false)]
theorem der_26355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26355 :=
  CNF.rup_sound cl_26355 [cl_6718,cl_26353] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6718 v h) (hints_cons _ _ _ (der_26353 v h) (by intro d hd; cases hd)))
def cl_26356 : CNF.NClause := [(52,false),(21,true),(85,false),(73,false),(66,false),(79,false),(67,true)]
theorem der_26356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26356 :=
  CNF.rup_sound cl_26356 [cl_6726,cl_26352] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6726 v h) (hints_cons _ _ _ (der_26352 v h) (by intro d hd; cases hd)))
def cl_26357 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,true),(85,false),(79,false)]
theorem der_26357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26357 :=
  CNF.rup_sound cl_26357 [cl_6734,cl_26349] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6734 v h) (hints_cons _ _ _ (der_26349 v h) (by intro d hd; cases hd)))
def cl_26358 : CNF.NClause := [(52,false),(79,true),(21,true),(66,false),(73,false),(67,true),(85,false)]
theorem der_26358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26358 :=
  CNF.rup_sound cl_26358 [cl_6742,cl_26354] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6742 v h) (hints_cons _ _ _ (der_26354 v h) (by intro d hd; cases hd)))
def cl_26359 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,true),(85,false),(88,true)]
theorem der_26359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26359 :=
  CNF.rup_sound cl_26359 [cl_6750,cl_26357] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6750 v h) (hints_cons _ _ _ (der_26357 v h) (by intro d hd; cases hd)))
def cl_26360 : CNF.NClause := [(52,false),(21,true),(88,true),(73,false),(79,false),(66,false),(67,true)]
theorem der_26360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26360 :=
  CNF.rup_sound cl_26360 [cl_6758,cl_26356] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6758 v h) (hints_cons _ _ _ (der_26356 v h) (by intro d hd; cases hd)))
def cl_26361 : CNF.NClause := [(52,false),(21,true),(66,false),(67,true),(73,true),(79,false),(85,true)]
theorem der_26361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26361 :=
  CNF.rup_sound cl_26361 [cl_6766,cl_26355] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6766 v h) (hints_cons _ _ _ (der_26355 v h) (by intro d hd; cases hd)))
def cl_26362 : CNF.NClause := [(52,false),(79,true),(21,true),(66,false),(73,false),(67,true),(85,true)]
theorem der_26362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26362 :=
  CNF.rup_sound cl_26362 [cl_6774,cl_26354] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6774 v h) (hints_cons _ _ _ (der_26354 v h) (by intro d hd; cases hd)))
def cl_26363 : CNF.NClause := [(52,false),(79,true),(21,true),(66,false),(67,true),(85,true),(88,true)]
theorem der_26363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26363 :=
  CNF.rup_sound cl_26363 [cl_6782,cl_26362] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6782 v h) (hints_cons _ _ _ (der_26362 v h) (by intro d hd; cases hd)))
def cl_26364 : CNF.NClause := [(47,false),(77,false),(89,false),(16,true),(66,false),(84,false),(75,false)]
theorem der_26364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26364 :=
  CNF.rup_sound cl_26364 [cl_6018,cl_26310] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6018 v h) (hints_cons _ _ _ (der_26310 v h) (by intro d hd; cases hd)))
def cl_26365 : CNF.NClause := [(47,false),(77,true),(66,false),(16,true),(75,false),(89,false),(84,false)]
theorem der_26365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26365 :=
  CNF.rup_sound cl_26365 [cl_6034,cl_26308] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6034 v h) (hints_cons _ _ _ (der_26308 v h) (by intro d hd; cases hd)))
def cl_26366 : CNF.NClause := [(39,false),(8,true),(90,false),(76,false),(68,false),(82,false),(79,false)]
theorem der_26366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26366 :=
  CNF.rup_sound cl_26366 [cl_4996,cl_4994] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4996 v h) (hints_cons _ _ _ (inp_4994 v h) (by intro d hd; cases hd)))
def cl_26367 : CNF.NClause := [(39,false),(76,false),(8,true),(65,false),(79,false),(82,false),(90,false)]
theorem der_26367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26367 :=
  CNF.rup_sound cl_26367 [cl_4998,cl_4994] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4998 v h) (hints_cons _ _ _ (inp_4994 v h) (by intro d hd; cases hd)))
def cl_26368 : CNF.NClause := [(39,false),(8,false),(65,true),(76,false),(79,false),(82,false),(90,false)]
theorem der_26368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26368 :=
  CNF.rup_sound cl_26368 [cl_4999,cl_4995] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4999 v h) (hints_cons _ _ _ (inp_4995 v h) (by intro d hd; cases hd)))
def cl_26369 : CNF.NClause := [(39,false),(68,true),(8,true),(76,false),(79,false),(82,false),(90,false)]
theorem der_26369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26369 :=
  CNF.rup_sound cl_26369 [cl_5000,cl_26367] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5000 v h) (hints_cons _ _ _ (der_26367 v h) (by intro d hd; cases hd)))
def cl_26370 : CNF.NClause := [(39,false),(68,false),(82,false),(90,false),(79,false),(76,true),(65,false)]
theorem der_26370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26370 :=
  CNF.rup_sound cl_26370 [cl_5002,cl_5001] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5002 v h) (hints_cons _ _ _ (inp_5001 v h) (by intro d hd; cases hd)))
def cl_26371 : CNF.NClause := [(39,false),(65,true),(8,false),(68,false),(79,false),(82,false),(90,false)]
theorem der_26371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26371 :=
  CNF.rup_sound cl_26371 [cl_5003,cl_4995] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5003 v h) (hints_cons _ _ _ (inp_4995 v h) (by intro d hd; cases hd)))
def cl_26372 : CNF.NClause := [(39,false),(65,true),(90,false),(79,false),(76,true),(82,false),(68,false)]
theorem der_26372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26372 :=
  CNF.rup_sound cl_26372 [cl_5004,cl_26371] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5004 v h) (hints_cons _ _ _ (der_26371 v h) (by intro d hd; cases hd)))
def cl_26373 : CNF.NClause := [(39,false),(8,false),(82,false),(76,true),(65,false),(79,false),(90,false)]
theorem der_26373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26373 :=
  CNF.rup_sound cl_26373 [cl_5005,cl_5001] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5005 v h) (hints_cons _ _ _ (inp_5001 v h) (by intro d hd; cases hd)))
def cl_26374 : CNF.NClause := [(39,false),(8,true),(65,false),(76,true),(79,false),(82,false),(90,false)]
theorem der_26374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26374 :=
  CNF.rup_sound cl_26374 [cl_5006,cl_26370] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5006 v h) (hints_cons _ _ _ (der_26370 v h) (by intro d hd; cases hd)))
def cl_26375 : CNF.NClause := [(39,false),(8,false),(65,true),(76,true),(79,false),(82,false),(90,false)]
theorem der_26375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26375 :=
  CNF.rup_sound cl_26375 [cl_5007,cl_26371] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5007 v h) (hints_cons _ _ _ (der_26371 v h) (by intro d hd; cases hd)))
def cl_26376 : CNF.NClause := [(39,false),(68,true),(8,true),(76,true),(79,false),(82,false),(90,false)]
theorem der_26376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26376 :=
  CNF.rup_sound cl_26376 [cl_5008,cl_26374] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5008 v h) (hints_cons _ _ _ (der_26374 v h) (by intro d hd; cases hd)))
def cl_26377 : CNF.NClause := [(39,false),(8,true),(68,false),(76,false),(65,false),(82,false),(90,false)]
theorem der_26377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26377 :=
  CNF.rup_sound cl_26377 [cl_5010,cl_4994] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5010 v h) (hints_cons _ _ _ (inp_4994 v h) (by intro d hd; cases hd)))
def cl_26378 : CNF.NClause := [(39,false),(79,true),(8,false),(76,false),(68,false),(82,false),(90,false)]
theorem der_26378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26378 :=
  CNF.rup_sound cl_26378 [cl_5011,cl_5009] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5011 v h) (hints_cons _ _ _ (inp_5009 v h) (by intro d hd; cases hd)))
def cl_26379 : CNF.NClause := [(39,false),(79,true),(65,true),(76,false),(68,false),(82,false),(90,false)]
theorem der_26379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26379 :=
  CNF.rup_sound cl_26379 [cl_5012,cl_26378] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5012 v h) (hints_cons _ _ _ (der_26378 v h) (by intro d hd; cases hd)))
def cl_26380 : CNF.NClause := [(39,false),(79,true),(8,false),(76,false),(65,false),(82,false),(90,false)]
theorem der_26380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26380 :=
  CNF.rup_sound cl_26380 [cl_5013,cl_26378] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5013 v h) (hints_cons _ _ _ (der_26378 v h) (by intro d hd; cases hd)))
def cl_26381 : CNF.NClause := [(39,false),(79,true),(8,true),(76,false),(65,false),(82,false),(90,false)]
theorem der_26381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26381 :=
  CNF.rup_sound cl_26381 [cl_5014,cl_26377] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5014 v h) (hints_cons _ _ _ (der_26377 v h) (by intro d hd; cases hd)))
def cl_26382 : CNF.NClause := [(39,false),(8,false),(65,true),(76,false),(79,true),(82,false),(90,false)]
theorem der_26382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26382 :=
  CNF.rup_sound cl_26382 [cl_5015,cl_26378] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5015 v h) (hints_cons _ _ _ (der_26378 v h) (by intro d hd; cases hd)))
def cl_26383 : CNF.NClause := [(39,false),(68,true),(65,true),(76,false),(79,true),(82,false),(90,false)]
theorem der_26383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26383 :=
  CNF.rup_sound cl_26383 [cl_5016,cl_26382] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5016 v h) (hints_cons _ _ _ (der_26382 v h) (by intro d hd; cases hd)))
def cl_26384 : CNF.NClause := [(39,false),(79,true),(8,false),(65,false),(68,false),(82,false),(90,false)]
theorem der_26384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26384 :=
  CNF.rup_sound cl_26384 [cl_5017,cl_5009] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5017 v h) (hints_cons _ _ _ (inp_5009 v h) (by intro d hd; cases hd)))
def cl_26385 : CNF.NClause := [(39,false),(8,true),(68,false),(65,false),(76,true),(82,false),(90,false)]
theorem der_26385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26385 :=
  CNF.rup_sound cl_26385 [cl_5018,cl_26370] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5018 v h) (hints_cons _ _ _ (der_26370 v h) (by intro d hd; cases hd)))
def cl_26386 : CNF.NClause := [(39,false),(79,true),(8,false),(76,true),(68,false),(82,false),(90,false)]
theorem der_26386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26386 :=
  CNF.rup_sound cl_26386 [cl_5019,cl_26384] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5019 v h) (hints_cons _ _ _ (der_26384 v h) (by intro d hd; cases hd)))
def cl_26387 : CNF.NClause := [(39,false),(79,true),(8,true),(76,true),(68,false),(82,false),(90,false)]
theorem der_26387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26387 :=
  CNF.rup_sound cl_26387 [cl_5020,cl_26385] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5020 v h) (hints_cons _ _ _ (der_26385 v h) (by intro d hd; cases hd)))
def cl_26388 : CNF.NClause := [(39,false),(79,true),(8,false),(76,true),(65,false),(82,false),(90,false)]
theorem der_26388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26388 :=
  CNF.rup_sound cl_26388 [cl_5021,cl_26384] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5021 v h) (hints_cons _ _ _ (der_26384 v h) (by intro d hd; cases hd)))
def cl_26389 : CNF.NClause := [(39,false),(8,true),(68,true),(76,true),(65,false),(82,false),(90,false)]
theorem der_26389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26389 :=
  CNF.rup_sound cl_26389 [cl_5022,cl_26376] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5022 v h) (hints_cons _ _ _ (der_26376 v h) (by intro d hd; cases hd)))
def cl_26390 : CNF.NClause := [(39,false),(68,true),(8,false),(76,true),(79,true),(82,false),(90,false)]
theorem der_26390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26390 :=
  CNF.rup_sound cl_26390 [cl_5023,cl_26388] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5023 v h) (hints_cons _ _ _ (der_26388 v h) (by intro d hd; cases hd)))
def cl_26391 : CNF.NClause := [(39,false),(8,true),(65,true),(76,true),(79,true),(82,false),(90,false)]
theorem der_26391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26391 :=
  CNF.rup_sound cl_26391 [cl_5024,cl_26387] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5024 v h) (hints_cons _ _ _ (der_26387 v h) (by intro d hd; cases hd)))
def cl_26392 : CNF.NClause := [(39,false),(82,true),(79,false),(65,false),(68,false),(76,false),(90,false)]
theorem der_26392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26392 :=
  CNF.rup_sound cl_26392 [cl_5026,cl_5025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5026 v h) (hints_cons _ _ _ (inp_5025 v h) (by intro d hd; cases hd)))
def cl_26393 : CNF.NClause := [(39,false),(79,false),(8,false),(65,true),(76,false),(68,false),(90,false)]
theorem der_26393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26393 :=
  CNF.rup_sound cl_26393 [cl_5027,cl_26371] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5027 v h) (hints_cons _ _ _ (der_26371 v h) (by intro d hd; cases hd)))
def cl_26394 : CNF.NClause := [(39,false),(68,false),(8,true),(65,true),(90,false),(79,false),(76,false)]
theorem der_26394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26394 :=
  CNF.rup_sound cl_26394 [cl_5028,cl_26366] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5028 v h) (hints_cons _ _ _ (der_26366 v h) (by intro d hd; cases hd)))
def cl_26395 : CNF.NClause := [(39,false),(8,false),(68,true),(76,false),(65,false),(90,false),(79,false)]
theorem der_26395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26395 :=
  CNF.rup_sound cl_26395 [cl_5029,cl_4997] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5029 v h) (hints_cons _ _ _ (inp_4997 v h) (by intro d hd; cases hd)))
def cl_26396 : CNF.NClause := [(39,false),(82,true),(8,true),(76,false),(65,false),(90,false),(79,false)]
theorem der_26396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26396 :=
  CNF.rup_sound cl_26396 [cl_5030,cl_26392] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5030 v h) (hints_cons _ _ _ (der_26392 v h) (by intro d hd; cases hd)))
def cl_26397 : CNF.NClause := [(39,false),(68,true),(8,false),(76,false),(79,false),(82,true),(90,false)]
theorem der_26397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26397 :=
  CNF.rup_sound cl_26397 [cl_5031,cl_26395] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5031 v h) (hints_cons _ _ _ (der_26395 v h) (by intro d hd; cases hd)))
def cl_26398 : CNF.NClause := [(39,false),(68,true),(8,true),(65,true),(76,false),(79,false),(90,false)]
theorem der_26398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26398 :=
  CNF.rup_sound cl_26398 [cl_5032,cl_26369] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5032 v h) (hints_cons _ _ _ (der_26369 v h) (by intro d hd; cases hd)))
def cl_26399 : CNF.NClause := [(39,false),(8,false),(68,false),(76,true),(65,false),(90,false),(79,false)]
theorem der_26399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26399 :=
  CNF.rup_sound cl_26399 [cl_5033,cl_26373] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5033 v h) (hints_cons _ _ _ (der_26373 v h) (by intro d hd; cases hd)))
def cl_26400 : CNF.NClause := [(39,false),(82,true),(8,true),(65,false),(68,false),(90,false),(79,false)]
theorem der_26400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26400 :=
  CNF.rup_sound cl_26400 [cl_5034,cl_26392] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5034 v h) (hints_cons _ _ _ (der_26392 v h) (by intro d hd; cases hd)))
def cl_26401 : CNF.NClause := [(39,false),(68,false),(8,false),(76,true),(79,false),(82,true),(90,false)]
theorem der_26401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26401 :=
  CNF.rup_sound cl_26401 [cl_5035,cl_26399] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5035 v h) (hints_cons _ _ _ (der_26399 v h) (by intro d hd; cases hd)))
def cl_26402 : CNF.NClause := [(39,false),(65,true),(8,true),(76,true),(68,false),(90,false),(79,false)]
theorem der_26402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26402 :=
  CNF.rup_sound cl_26402 [cl_5036,cl_26372] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5036 v h) (hints_cons _ _ _ (der_26372 v h) (by intro d hd; cases hd)))
def cl_26403 : CNF.NClause := [(39,false),(8,false),(68,true),(76,true),(65,false),(90,false),(79,false)]
theorem der_26403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26403 :=
  CNF.rup_sound cl_26403 [cl_5037,cl_26373] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5037 v h) (hints_cons _ _ _ (der_26373 v h) (by intro d hd; cases hd)))
def cl_26404 : CNF.NClause := [(39,false),(8,true),(68,true),(76,true),(65,false),(90,false),(79,false)]
theorem der_26404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26404 :=
  CNF.rup_sound cl_26404 [cl_5038,cl_26389] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5038 v h) (hints_cons _ _ _ (der_26389 v h) (by intro d hd; cases hd)))
def cl_26405 : CNF.NClause := [(39,false),(68,true),(8,false),(76,true),(79,false),(82,true),(90,false)]
theorem der_26405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26405 :=
  CNF.rup_sound cl_26405 [cl_5039,cl_26403] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5039 v h) (hints_cons _ _ _ (der_26403 v h) (by intro d hd; cases hd)))
def cl_26406 : CNF.NClause := [(39,false),(68,true),(8,true),(76,true),(79,false),(82,true),(90,false)]
theorem der_26406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26406 :=
  CNF.rup_sound cl_26406 [cl_5040,cl_26404] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5040 v h) (hints_cons _ _ _ (der_26404 v h) (by intro d hd; cases hd)))
def cl_26407 : CNF.NClause := [(39,false),(79,true),(8,false),(90,false),(76,false),(68,false),(65,false)]
theorem der_26407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26407 :=
  CNF.rup_sound cl_26407 [cl_5041,cl_26380] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5041 v h) (hints_cons _ _ _ (der_26380 v h) (by intro d hd; cases hd)))
def cl_26408 : CNF.NClause := [(39,false),(79,true),(8,true),(68,false),(90,false),(65,false),(76,false)]
theorem der_26408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26408 :=
  CNF.rup_sound cl_26408 [cl_5042,cl_26377] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5042 v h) (hints_cons _ _ _ (der_26377 v h) (by intro d hd; cases hd)))
def cl_26409 : CNF.NClause := [(39,false),(8,false),(65,true),(76,false),(68,false),(82,true),(90,false)]
theorem der_26409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26409 :=
  CNF.rup_sound cl_26409 [cl_5043,cl_26393] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5043 v h) (hints_cons _ _ _ (der_26393 v h) (by intro d hd; cases hd)))
def cl_26410 : CNF.NClause := [(39,false),(65,true),(68,false),(90,false),(76,false),(82,true),(79,true)]
theorem der_26410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26410 :=
  CNF.rup_sound cl_26410 [cl_5044,cl_26409] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5044 v h) (hints_cons _ _ _ (der_26409 v h) (by intro d hd; cases hd)))
def cl_26411 : CNF.NClause := [(39,false),(8,false),(68,true),(76,false),(65,false),(82,true),(90,false)]
theorem der_26411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26411 :=
  CNF.rup_sound cl_26411 [cl_5045,cl_26395] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5045 v h) (hints_cons _ _ _ (der_26395 v h) (by intro d hd; cases hd)))
def cl_26412 : CNF.NClause := [(39,false),(79,true),(8,true),(76,false),(65,false),(82,true),(90,false)]
theorem der_26412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26412 :=
  CNF.rup_sound cl_26412 [cl_5046,cl_26408] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5046 v h) (hints_cons _ _ _ (der_26408 v h) (by intro d hd; cases hd)))
def cl_26414 : CNF.NClause := [(39,false),(68,true),(8,true),(76,false),(79,true),(82,true),(90,false)]
theorem der_26414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26414 :=
  CNF.rup_sound cl_26414 [cl_5048,cl_26412] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5048 v h) (hints_cons _ _ _ (der_26412 v h) (by intro d hd; cases hd)))
def cl_26415 : CNF.NClause := [(39,false),(8,false),(90,false),(76,true),(65,false),(82,true),(68,false)]
theorem der_26415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26415 :=
  CNF.rup_sound cl_26415 [cl_5049,cl_26401] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5049 v h) (hints_cons _ _ _ (der_26401 v h) (by intro d hd; cases hd)))
def cl_26416 : CNF.NClause := [(39,false),(79,true),(8,true),(68,false),(65,false),(82,true),(90,false)]
theorem der_26416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26416 :=
  CNF.rup_sound cl_26416 [cl_5050,cl_26408] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5050 v h) (hints_cons _ _ _ (der_26408 v h) (by intro d hd; cases hd)))
def cl_26417 : CNF.NClause := [(39,false),(8,false),(65,true),(76,true),(68,false),(82,true),(90,false)]
theorem der_26417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26417 :=
  CNF.rup_sound cl_26417 [cl_5051,cl_26401] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5051 v h) (hints_cons _ _ _ (der_26401 v h) (by intro d hd; cases hd)))
def cl_26418 : CNF.NClause := [(39,false),(79,true),(8,true),(76,true),(90,false),(82,true),(68,false)]
theorem der_26418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26418 :=
  CNF.rup_sound cl_26418 [cl_5052,cl_26416] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5052 v h) (hints_cons _ _ _ (der_26416 v h) (by intro d hd; cases hd)))
def cl_26419 : CNF.NClause := [(39,false),(79,true),(8,false),(76,true),(65,false),(82,true),(90,false)]
theorem der_26419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26419 :=
  CNF.rup_sound cl_26419 [cl_5053,cl_26415] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5053 v h) (hints_cons _ _ _ (der_26415 v h) (by intro d hd; cases hd)))
def cl_26420 : CNF.NClause := [(39,false),(79,true),(8,true),(76,true),(65,false),(82,true),(90,false)]
theorem der_26420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26420 :=
  CNF.rup_sound cl_26420 [cl_5054,cl_26416] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5054 v h) (hints_cons _ _ _ (der_26416 v h) (by intro d hd; cases hd)))
def cl_26421 : CNF.NClause := [(39,false),(8,false),(65,true),(76,true),(79,true),(82,true),(90,false)]
theorem der_26421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26421 :=
  CNF.rup_sound cl_26421 [cl_5055,cl_26417] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5055 v h) (hints_cons _ _ _ (der_26417 v h) (by intro d hd; cases hd)))
def cl_26422 : CNF.NClause := [(39,false),(68,true),(8,true),(65,true),(76,true),(82,true),(90,false)]
theorem der_26422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26422 :=
  CNF.rup_sound cl_26422 [cl_5056,cl_26406] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5056 v h) (hints_cons _ _ _ (der_26406 v h) (by intro d hd; cases hd)))
def cl_26423 : CNF.NClause := [(39,false),(8,true),(82,false),(76,false),(65,false),(79,false),(68,false)]
theorem der_26423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26423 :=
  CNF.rup_sound cl_26423 [cl_5058,cl_26366] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5058 v h) (hints_cons _ _ _ (der_26366 v h) (by intro d hd; cases hd)))
def cl_26424 : CNF.NClause := [(39,false),(8,false),(65,true),(76,false),(68,false),(82,false),(79,false)]
theorem der_26424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26424 :=
  CNF.rup_sound cl_26424 [cl_5059,cl_26368] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5059 v h) (hints_cons _ _ _ (der_26368 v h) (by intro d hd; cases hd)))
def cl_26425 : CNF.NClause := [(39,false),(65,true),(8,true),(76,false),(79,false),(82,false),(68,false)]
theorem der_26425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26425 :=
  CNF.rup_sound cl_26425 [cl_5060,cl_26366] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5060 v h) (hints_cons _ _ _ (der_26366 v h) (by intro d hd; cases hd)))
def cl_26426 : CNF.NClause := [(39,false),(8,false),(90,true),(76,false),(65,false),(82,false),(79,false)]
theorem der_26426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26426 :=
  CNF.rup_sound cl_26426 [cl_5061,cl_5057] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5061 v h) (hints_cons _ _ _ (inp_5057 v h) (by intro d hd; cases hd)))
def cl_26427 : CNF.NClause := [(39,false),(68,true),(90,true),(76,false),(65,false),(82,false),(79,false)]
theorem der_26427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26427 :=
  CNF.rup_sound cl_26427 [cl_5062,cl_26426] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5062 v h) (hints_cons _ _ _ (der_26426 v h) (by intro d hd; cases hd)))
def cl_26428 : CNF.NClause := [(39,false),(8,false),(65,true),(76,false),(79,false),(82,false),(90,true)]
theorem der_26428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26428 :=
  CNF.rup_sound cl_26428 [cl_5063,cl_26424] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5063 v h) (hints_cons _ _ _ (der_26424 v h) (by intro d hd; cases hd)))
def cl_26429 : CNF.NClause := [(39,false),(68,true),(8,true),(65,true),(76,false),(79,false),(82,false)]
theorem der_26429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26429 :=
  CNF.rup_sound cl_26429 [cl_5064,cl_26398] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5064 v h) (hints_cons _ _ _ (der_26398 v h) (by intro d hd; cases hd)))
def cl_26430 : CNF.NClause := [(39,false),(90,true),(8,false),(65,false),(82,false),(79,false),(68,false)]
theorem der_26430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26430 :=
  CNF.rup_sound cl_26430 [cl_5065,cl_5057] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5065 v h) (hints_cons _ _ _ (inp_5057 v h) (by intro d hd; cases hd)))
def cl_26431 : CNF.NClause := [(39,false),(90,true),(68,false),(79,false),(65,false),(76,true),(82,false)]
theorem der_26431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26431 :=
  CNF.rup_sound cl_26431 [cl_5066,cl_26430] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5066 v h) (hints_cons _ _ _ (der_26430 v h) (by intro d hd; cases hd)))
def cl_26432 : CNF.NClause := [(39,false),(8,false),(65,true),(76,true),(79,false),(82,false),(68,false)]
theorem der_26432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26432 :=
  CNF.rup_sound cl_26432 [cl_5067,cl_26372] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5067 v h) (hints_cons _ _ _ (der_26372 v h) (by intro d hd; cases hd)))
def cl_26433 : CNF.NClause := [(39,false),(65,true),(8,true),(76,true),(79,false),(82,false),(68,false)]
theorem der_26433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26433 :=
  CNF.rup_sound cl_26433 [cl_5068,cl_26372] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5068 v h) (hints_cons _ _ _ (der_26372 v h) (by intro d hd; cases hd)))
def cl_26434 : CNF.NClause := [(39,false),(68,true),(8,false),(90,true),(65,false),(82,false),(79,false)]
theorem der_26434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26434 :=
  CNF.rup_sound cl_26434 [cl_5069,cl_26426] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5069 v h) (hints_cons _ _ _ (der_26426 v h) (by intro d hd; cases hd)))
def cl_26435 : CNF.NClause := [(39,false),(68,true),(8,true),(76,true),(65,false),(82,false),(79,false)]
theorem der_26435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26435 :=
  CNF.rup_sound cl_26435 [cl_5070,cl_26404] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5070 v h) (hints_cons _ _ _ (der_26404 v h) (by intro d hd; cases hd)))
def cl_26436 : CNF.NClause := [(39,false),(68,true),(8,false),(65,true),(76,true),(79,false),(82,false)]
theorem der_26436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26436 :=
  CNF.rup_sound cl_26436 [cl_5071,cl_26375] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5071 v h) (hints_cons _ _ _ (der_26375 v h) (by intro d hd; cases hd)))
def cl_26437 : CNF.NClause := [(39,false),(68,true),(8,true),(76,true),(79,false),(82,false),(90,true)]
theorem der_26437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26437 :=
  CNF.rup_sound cl_26437 [cl_5072,cl_26435] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5072 v h) (hints_cons _ _ _ (der_26435 v h) (by intro d hd; cases hd)))
def cl_26438 : CNF.NClause := [(39,false),(79,true),(8,false),(65,false),(76,false),(68,false),(82,false)]
theorem der_26438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26438 :=
  CNF.rup_sound cl_26438 [cl_5073,cl_5009] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5073 v h) (hints_cons _ _ _ (inp_5009 v h) (by intro d hd; cases hd)))
def cl_26439 : CNF.NClause := [(39,false),(79,true),(8,true),(68,false),(76,false),(65,false),(82,false)]
theorem der_26439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26439 :=
  CNF.rup_sound cl_26439 [cl_5074,cl_26408] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5074 v h) (hints_cons _ _ _ (der_26408 v h) (by intro d hd; cases hd)))
def cl_26440 : CNF.NClause := [(39,false),(79,true),(8,false),(65,true),(76,false),(68,false),(82,false)]
theorem der_26440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26440 :=
  CNF.rup_sound cl_26440 [cl_5075,cl_26382] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5075 v h) (hints_cons _ _ _ (der_26382 v h) (by intro d hd; cases hd)))
def cl_26441 : CNF.NClause := [(39,false),(8,true),(65,true),(76,false),(68,false),(82,false),(90,true)]
theorem der_26441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26441 :=
  CNF.rup_sound cl_26441 [cl_5076,cl_26425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5076 v h) (hints_cons _ _ _ (der_26425 v h) (by intro d hd; cases hd)))
def cl_26442 : CNF.NClause := [(39,false),(79,true),(8,false),(76,false),(65,false),(82,false),(90,true)]
theorem der_26442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26442 :=
  CNF.rup_sound cl_26442 [cl_5077,cl_26438] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5077 v h) (hints_cons _ _ _ (der_26438 v h) (by intro d hd; cases hd)))
def cl_26443 : CNF.NClause := [(39,false),(79,true),(8,true),(76,false),(65,false),(82,false),(90,true)]
theorem der_26443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26443 :=
  CNF.rup_sound cl_26443 [cl_5078,cl_26439] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5078 v h) (hints_cons _ _ _ (der_26439 v h) (by intro d hd; cases hd)))
def cl_26445 : CNF.NClause := [(39,false),(68,true),(8,true),(65,true),(76,false),(82,false),(90,true)]
theorem der_26445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26445 :=
  CNF.rup_sound cl_26445 [cl_5080,cl_26429] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5080 v h) (hints_cons _ _ _ (der_26429 v h) (by intro d hd; cases hd)))
def cl_26446 : CNF.NClause := [(39,false),(79,true),(8,false),(65,false),(76,true),(68,false),(82,false)]
theorem der_26446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26446 :=
  CNF.rup_sound cl_26446 [cl_5081,cl_26384] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5081 v h) (hints_cons _ _ _ (der_26384 v h) (by intro d hd; cases hd)))
def cl_26447 : CNF.NClause := [(39,false),(79,true),(8,true),(68,false),(65,false),(82,false),(90,true)]
theorem der_26447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26447 :=
  CNF.rup_sound cl_26447 [cl_5082,cl_26439] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5082 v h) (hints_cons _ _ _ (der_26439 v h) (by intro d hd; cases hd)))
def cl_26448 : CNF.NClause := [(39,false),(8,false),(65,true),(76,true),(68,false),(82,false),(90,true)]
theorem der_26448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26448 :=
  CNF.rup_sound cl_26448 [cl_5083,cl_26432] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5083 v h) (hints_cons _ _ _ (der_26432 v h) (by intro d hd; cases hd)))
def cl_26449 : CNF.NClause := [(39,false),(79,true),(65,true),(76,true),(68,false),(82,false),(90,true)]
theorem der_26449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26449 :=
  CNF.rup_sound cl_26449 [cl_5084,cl_26448] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5084 v h) (hints_cons _ _ _ (der_26448 v h) (by intro d hd; cases hd)))
def cl_26450 : CNF.NClause := [(39,false),(79,true),(8,false),(76,true),(65,false),(82,false),(90,true)]
theorem der_26450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26450 :=
  CNF.rup_sound cl_26450 [cl_5085,cl_26446] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5085 v h) (hints_cons _ _ _ (der_26446 v h) (by intro d hd; cases hd)))
def cl_26451 : CNF.NClause := [(39,false),(8,true),(68,true),(76,true),(65,false),(82,false),(90,true)]
theorem der_26451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26451 :=
  CNF.rup_sound cl_26451 [cl_5086,cl_26437] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5086 v h) (hints_cons _ _ _ (der_26437 v h) (by intro d hd; cases hd)))
def cl_26453 : CNF.NClause := [(39,false),(68,true),(8,true),(65,true),(79,true),(82,false),(90,true)]
theorem der_26453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26453 :=
  CNF.rup_sound cl_26453 [cl_5088,cl_26445] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5088 v h) (hints_cons _ _ _ (der_26445 v h) (by intro d hd; cases hd)))
def cl_26454 : CNF.NClause := [(39,false),(82,true),(8,false),(68,false),(76,false),(65,false),(79,false)]
theorem der_26454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26454 :=
  CNF.rup_sound cl_26454 [cl_5089,cl_5025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5089 v h) (hints_cons _ _ _ (inp_5025 v h) (by intro d hd; cases hd)))
def cl_26455 : CNF.NClause := [(39,false),(8,true),(79,false),(90,true),(76,false),(68,false),(65,false)]
theorem der_26455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26455 :=
  CNF.rup_sound cl_26455 [cl_5090,cl_26423] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5090 v h) (hints_cons _ _ _ (der_26423 v h) (by intro d hd; cases hd)))
def cl_26456 : CNF.NClause := [(39,false),(79,false),(8,false),(65,true),(76,false),(68,false),(82,true)]
theorem der_26456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26456 :=
  CNF.rup_sound cl_26456 [cl_5091,cl_26393] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5091 v h) (hints_cons _ _ _ (der_26393 v h) (by intro d hd; cases hd)))
def cl_26457 : CNF.NClause := [(39,false),(65,true),(8,true),(68,false),(79,false),(82,true),(76,false)]
theorem der_26457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26457 :=
  CNF.rup_sound cl_26457 [cl_5092,cl_26394] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5092 v h) (hints_cons _ _ _ (der_26394 v h) (by intro d hd; cases hd)))
def cl_26458 : CNF.NClause := [(39,false),(68,true),(8,false),(90,true),(76,false),(65,false),(79,false)]
theorem der_26458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26458 :=
  CNF.rup_sound cl_26458 [cl_5093,cl_26426] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5093 v h) (hints_cons _ _ _ (der_26426 v h) (by intro d hd; cases hd)))
def cl_26459 : CNF.NClause := [(39,false),(68,true),(8,true),(90,true),(76,false),(65,false),(79,false)]
theorem der_26459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26459 :=
  CNF.rup_sound cl_26459 [cl_5094,cl_26427] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5094 v h) (hints_cons _ _ _ (der_26427 v h) (by intro d hd; cases hd)))
def cl_26460 : CNF.NClause := [(39,false),(68,true),(8,false),(65,true),(76,false),(79,false),(82,true)]
theorem der_26460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26460 :=
  CNF.rup_sound cl_26460 [cl_5095,cl_26397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5095 v h) (hints_cons _ _ _ (der_26397 v h) (by intro d hd; cases hd)))
def cl_26461 : CNF.NClause := [(39,false),(8,true),(65,true),(76,false),(79,false),(82,true),(90,true)]
theorem der_26461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26461 :=
  CNF.rup_sound cl_26461 [cl_5096,cl_26457] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5096 v h) (hints_cons _ _ _ (der_26457 v h) (by intro d hd; cases hd)))
def cl_26462 : CNF.NClause := [(39,false),(82,true),(8,false),(90,true),(65,false),(68,false),(79,false)]
theorem der_26462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26462 :=
  CNF.rup_sound cl_26462 [cl_5097,cl_26454] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5097 v h) (hints_cons _ _ _ (der_26454 v h) (by intro d hd; cases hd)))
def cl_26463 : CNF.NClause := [(39,false),(82,true),(8,true),(68,false),(65,false),(79,false),(76,true)]
theorem der_26463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26463 :=
  CNF.rup_sound cl_26463 [cl_5098,cl_26400] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5098 v h) (hints_cons _ _ _ (der_26400 v h) (by intro d hd; cases hd)))
def cl_26464 : CNF.NClause := [(39,false),(68,false),(8,false),(65,true),(76,true),(79,false),(82,true)]
theorem der_26464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26464 :=
  CNF.rup_sound cl_26464 [cl_5099,cl_26417] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5099 v h) (hints_cons _ _ _ (der_26417 v h) (by intro d hd; cases hd)))
def cl_26465 : CNF.NClause := [(39,false),(65,true),(8,true),(68,false),(79,false),(82,true),(76,true)]
theorem der_26465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26465 :=
  CNF.rup_sound cl_26465 [cl_5100,cl_26402] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5100 v h) (hints_cons _ _ _ (der_26402 v h) (by intro d hd; cases hd)))
def cl_26466 : CNF.NClause := [(39,false),(68,true),(8,false),(90,true),(76,true),(65,false),(79,false)]
theorem der_26466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26466 :=
  CNF.rup_sound cl_26466 [cl_5101,cl_26434] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5101 v h) (hints_cons _ _ _ (der_26434 v h) (by intro d hd; cases hd)))
def cl_26467 : CNF.NClause := [(39,false),(68,true),(8,true),(76,true),(65,false),(82,true),(79,false)]
theorem der_26467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26467 :=
  CNF.rup_sound cl_26467 [cl_5102,cl_26406] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5102 v h) (hints_cons _ _ _ (der_26406 v h) (by intro d hd; cases hd)))
def cl_26469 : CNF.NClause := [(39,false),(68,true),(8,true),(65,true),(76,true),(79,false),(82,true)]
theorem der_26469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26469 :=
  CNF.rup_sound cl_26469 [cl_5104,cl_26406] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5104 v h) (hints_cons _ _ _ (der_26406 v h) (by intro d hd; cases hd)))
def cl_26470 : CNF.NClause := [(39,false),(79,true),(8,false),(65,false),(76,false),(68,false),(90,true)]
theorem der_26470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26470 :=
  CNF.rup_sound cl_26470 [cl_5105,cl_26442] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5105 v h) (hints_cons _ _ _ (der_26442 v h) (by intro d hd; cases hd)))
def cl_26471 : CNF.NClause := [(39,false),(8,true),(68,false),(76,false),(65,false),(82,true),(90,true)]
theorem der_26471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26471 :=
  CNF.rup_sound cl_26471 [cl_5106,cl_26455] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5106 v h) (hints_cons _ _ _ (der_26455 v h) (by intro d hd; cases hd)))
def cl_26472 : CNF.NClause := [(39,false),(79,true),(8,false),(76,false),(68,false),(82,true),(90,true)]
theorem der_26472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26472 :=
  CNF.rup_sound cl_26472 [cl_5107,cl_26470] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5107 v h) (hints_cons _ _ _ (der_26470 v h) (by intro d hd; cases hd)))
def cl_26473 : CNF.NClause := [(39,false),(79,true),(8,true),(65,true),(76,false),(68,false),(82,true)]
theorem der_26473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26473 :=
  CNF.rup_sound cl_26473 [cl_5108,cl_26410] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5108 v h) (hints_cons _ _ _ (der_26410 v h) (by intro d hd; cases hd)))
def cl_26474 : CNF.NClause := [(39,false),(79,true),(8,false),(76,false),(65,false),(82,true),(90,true)]
theorem der_26474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26474 :=
  CNF.rup_sound cl_26474 [cl_5109,cl_26470] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5109 v h) (hints_cons _ _ _ (der_26470 v h) (by intro d hd; cases hd)))
def cl_26475 : CNF.NClause := [(39,false),(8,true),(68,true),(76,false),(65,false),(82,true),(90,true)]
theorem der_26475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26475 :=
  CNF.rup_sound cl_26475 [cl_5110,cl_26459] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5110 v h) (hints_cons _ _ _ (der_26459 v h) (by intro d hd; cases hd)))
def cl_26477 : CNF.NClause := [(39,false),(68,true),(8,true),(65,true),(76,false),(79,true),(90,true)]
theorem der_26477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26477 :=
  CNF.rup_sound cl_26477 [cl_5112,cl_26445] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5112 v h) (hints_cons _ _ _ (der_26445 v h) (by intro d hd; cases hd)))
def cl_26478 : CNF.NClause := [(39,false),(79,true),(8,false),(65,false),(68,false),(82,true),(90,true)]
theorem der_26478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26478 :=
  CNF.rup_sound cl_26478 [cl_5113,cl_26470] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5113 v h) (hints_cons _ _ _ (der_26470 v h) (by intro d hd; cases hd)))
def cl_26479 : CNF.NClause := [(39,false),(79,true),(8,true),(68,false),(65,false),(76,true),(82,true)]
theorem der_26479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26479 :=
  CNF.rup_sound cl_26479 [cl_5114,cl_26416] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5114 v h) (hints_cons _ _ _ (der_26416 v h) (by intro d hd; cases hd)))
def cl_26480 : CNF.NClause := [(39,false),(79,true),(8,false),(65,true),(76,true),(68,false),(90,true)]
theorem der_26480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26480 :=
  CNF.rup_sound cl_26480 [cl_5115,cl_26449] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5115 v h) (hints_cons _ _ _ (der_26449 v h) (by intro d hd; cases hd)))
def cl_26481 : CNF.NClause := [(39,false),(79,true),(8,true),(65,true),(76,true),(68,false),(90,true)]
theorem der_26481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26481 :=
  CNF.rup_sound cl_26481 [cl_5116,cl_26449] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5116 v h) (hints_cons _ _ _ (der_26449 v h) (by intro d hd; cases hd)))
def cl_26482 : CNF.NClause := [(39,false),(79,true),(8,false),(76,true),(65,false),(82,true),(90,true)]
theorem der_26482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26482 :=
  CNF.rup_sound cl_26482 [cl_5117,cl_26478] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5117 v h) (hints_cons _ _ _ (der_26478 v h) (by intro d hd; cases hd)))
def cl_26483 : CNF.NClause := [(39,false),(79,true),(8,true),(68,true),(76,true),(65,false),(90,true)]
theorem der_26483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26483 :=
  CNF.rup_sound cl_26483 [cl_5118,cl_26451] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5118 v h) (hints_cons _ _ _ (der_26451 v h) (by intro d hd; cases hd)))
def cl_26485 : CNF.NClause := [(39,false),(68,true),(8,true),(76,true),(79,true),(82,true),(90,true)]
theorem der_26485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26485 :=
  CNF.rup_sound cl_26485 [cl_5120,cl_26483] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5120 v h) (hints_cons _ _ _ (der_26483 v h) (by intro d hd; cases hd)))
def cl_26486 : CNF.NClause := [(37,false),(6,true),(74,false),(91,false),(78,false),(82,false),(70,false)]
theorem der_26486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26486 :=
  CNF.rup_sound cl_26486 [cl_4738,cl_26330] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4738 v h) (hints_cons _ _ _ (der_26330 v h) (by intro d hd; cases hd)))
def cl_26487 : CNF.NClause := [(37,false),(66,true),(70,false),(74,false),(78,false),(82,false),(91,false)]
theorem der_26487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26487 :=
  CNF.rup_sound cl_26487 [cl_4739,cl_4740] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4739 v h) (hints_cons _ _ _ (inp_4740 v h) (by intro d hd; cases hd)))
def cl_26488 : CNF.NClause := [(37,false),(78,false),(6,true),(66,false),(74,false),(91,false),(82,false)]
theorem der_26488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26488 :=
  CNF.rup_sound cl_26488 [cl_4742,cl_26486] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4742 v h) (hints_cons _ _ _ (der_26486 v h) (by intro d hd; cases hd)))
def cl_26489 : CNF.NClause := [(37,false),(66,true),(6,false),(74,false),(78,false),(82,false),(91,false)]
theorem der_26489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26489 :=
  CNF.rup_sound cl_26489 [cl_4743,cl_26487] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4743 v h) (hints_cons _ _ _ (der_26487 v h) (by intro d hd; cases hd)))
def cl_26490 : CNF.NClause := [(37,false),(66,true),(74,false),(70,true),(78,false),(82,false),(91,false)]
theorem der_26490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26490 :=
  CNF.rup_sound cl_26490 [cl_4744,cl_26489] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4744 v h) (hints_cons _ _ _ (der_26489 v h) (by intro d hd; cases hd)))
def cl_26491 : CNF.NClause := [(37,false),(6,true),(91,false),(66,false),(70,false),(82,false),(78,false)]
theorem der_26491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26491 :=
  CNF.rup_sound cl_26491 [cl_4746,cl_26486] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4746 v h) (hints_cons _ _ _ (der_26486 v h) (by intro d hd; cases hd)))
def cl_26492 : CNF.NClause := [(37,false),(66,true),(6,false),(70,false),(78,false),(82,false),(91,false)]
theorem der_26492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26492 :=
  CNF.rup_sound cl_26492 [cl_4747,cl_26489] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4747 v h) (hints_cons _ _ _ (der_26489 v h) (by intro d hd; cases hd)))
def cl_26493 : CNF.NClause := [(37,false),(66,true),(91,false),(70,false),(78,false),(82,false),(74,true)]
theorem der_26493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26493 :=
  CNF.rup_sound cl_26493 [cl_4748,cl_26492] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4748 v h) (hints_cons _ _ _ (der_26492 v h) (by intro d hd; cases hd)))
def cl_26494 : CNF.NClause := [(37,false),(6,false),(70,true),(91,false),(66,false),(82,false),(78,false)]
theorem der_26494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26494 :=
  CNF.rup_sound cl_26494 [cl_4749,cl_4741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4749 v h) (hints_cons _ _ _ (inp_4741 v h) (by intro d hd; cases hd)))
def cl_26495 : CNF.NClause := [(37,false),(74,true),(6,true),(66,false),(91,false),(82,false),(78,false)]
theorem der_26495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26495 :=
  CNF.rup_sound cl_26495 [cl_4750,cl_26491] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4750 v h) (hints_cons _ _ _ (der_26491 v h) (by intro d hd; cases hd)))
def cl_26496 : CNF.NClause := [(37,false),(66,true),(6,false),(70,true),(78,false),(82,false),(91,false)]
theorem der_26496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26496 :=
  CNF.rup_sound cl_26496 [cl_4751,cl_26489] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4751 v h) (hints_cons _ _ _ (der_26489 v h) (by intro d hd; cases hd)))
def cl_26497 : CNF.NClause := [(37,false),(66,true),(91,false),(74,true),(70,true),(82,false),(78,false)]
theorem der_26497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26497 :=
  CNF.rup_sound cl_26497 [cl_4752,cl_26496] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4752 v h) (hints_cons _ _ _ (der_26496 v h) (by intro d hd; cases hd)))
def cl_26498 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,false),(82,false),(91,false)]
theorem der_26498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26498 :=
  CNF.rup_sound cl_26498 [cl_4754,cl_26488] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4754 v h) (hints_cons _ _ _ (der_26488 v h) (by intro d hd; cases hd)))
def cl_26499 : CNF.NClause := [(37,false),(66,true),(6,false),(70,false),(74,false),(82,false),(91,false)]
theorem der_26499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26499 :=
  CNF.rup_sound cl_26499 [cl_4755,cl_26489] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4755 v h) (hints_cons _ _ _ (der_26489 v h) (by intro d hd; cases hd)))
def cl_26500 : CNF.NClause := [(37,false),(66,true),(6,true),(74,false),(70,false),(82,false),(91,false)]
theorem der_26500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26500 :=
  CNF.rup_sound cl_26500 [cl_4756,cl_26487] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4756 v h) (hints_cons _ _ _ (der_26487 v h) (by intro d hd; cases hd)))
def cl_26501 : CNF.NClause := [(37,false),(6,false),(82,false),(66,false),(74,false),(70,true),(91,false)]
theorem der_26501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26501 :=
  CNF.rup_sound cl_26501 [cl_4757,cl_26494] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4757 v h) (hints_cons _ _ _ (der_26494 v h) (by intro d hd; cases hd)))
def cl_26502 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,false),(82,false),(91,false)]
theorem der_26502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26502 :=
  CNF.rup_sound cl_26502 [cl_4758,cl_26488] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4758 v h) (hints_cons _ _ _ (der_26488 v h) (by intro d hd; cases hd)))
def cl_26503 : CNF.NClause := [(37,false),(6,false),(70,true),(74,false),(78,true),(82,false),(91,false)]
theorem der_26503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26503 :=
  CNF.rup_sound cl_26503 [cl_4759,cl_26501] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4759 v h) (hints_cons _ _ _ (der_26501 v h) (by intro d hd; cases hd)))
def cl_26504 : CNF.NClause := [(37,false),(66,true),(6,true),(78,true),(74,false),(82,false),(91,false)]
theorem der_26504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26504 :=
  CNF.rup_sound cl_26504 [cl_4760,cl_26500] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4760 v h) (hints_cons _ _ _ (der_26500 v h) (by intro d hd; cases hd)))
def cl_26505 : CNF.NClause := [(37,false),(78,true),(6,false),(66,false),(70,false),(82,false),(91,false)]
theorem der_26505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26505 :=
  CNF.rup_sound cl_26505 [cl_4761,cl_4753] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4761 v h) (hints_cons _ _ _ (inp_4753 v h) (by intro d hd; cases hd)))
def cl_26506 : CNF.NClause := [(37,false),(78,true),(6,true),(66,false),(70,false),(82,false),(91,false)]
theorem der_26506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26506 :=
  CNF.rup_sound cl_26506 [cl_4762,cl_26498] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4762 v h) (hints_cons _ _ _ (der_26498 v h) (by intro d hd; cases hd)))
def cl_26507 : CNF.NClause := [(37,false),(66,true),(6,false),(70,false),(74,true),(82,false),(91,false)]
theorem der_26507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26507 :=
  CNF.rup_sound cl_26507 [cl_4763,cl_26492] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4763 v h) (hints_cons _ _ _ (der_26492 v h) (by intro d hd; cases hd)))
def cl_26508 : CNF.NClause := [(37,false),(78,true),(6,true),(70,false),(74,true),(82,false),(91,false)]
theorem der_26508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26508 :=
  CNF.rup_sound cl_26508 [cl_4764,cl_26506] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4764 v h) (hints_cons _ _ _ (der_26506 v h) (by intro d hd; cases hd)))
def cl_26509 : CNF.NClause := [(37,false),(6,false),(66,false),(74,true),(70,true),(82,false),(91,false)]
theorem der_26509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26509 :=
  CNF.rup_sound cl_26509 [cl_4765,cl_26494] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4765 v h) (hints_cons _ _ _ (der_26494 v h) (by intro d hd; cases hd)))
def cl_26510 : CNF.NClause := [(37,false),(78,true),(6,true),(66,false),(74,true),(82,false),(91,false)]
theorem der_26510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26510 :=
  CNF.rup_sound cl_26510 [cl_4766,cl_26506] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4766 v h) (hints_cons _ _ _ (der_26506 v h) (by intro d hd; cases hd)))
def cl_26511 : CNF.NClause := [(37,false),(6,false),(70,true),(74,true),(78,true),(82,false),(91,false)]
theorem der_26511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26511 :=
  CNF.rup_sound cl_26511 [cl_4767,cl_26509] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4767 v h) (hints_cons _ _ _ (der_26509 v h) (by intro d hd; cases hd)))
def cl_26512 : CNF.NClause := [(37,false),(6,true),(66,true),(74,true),(70,true),(82,false),(91,false)]
theorem der_26512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26512 :=
  CNF.rup_sound cl_26512 [cl_4768,cl_26497] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4768 v h) (hints_cons _ _ _ (der_26497 v h) (by intro d hd; cases hd)))
def cl_26513 : CNF.NClause := [(37,false),(6,true),(70,false),(91,false),(66,false),(78,false),(74,false)]
theorem der_26513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26513 :=
  CNF.rup_sound cl_26513 [cl_4770,cl_26498] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4770 v h) (hints_cons _ _ _ (der_26498 v h) (by intro d hd; cases hd)))
def cl_26514 : CNF.NClause := [(37,false),(66,true),(6,false),(70,false),(74,false),(78,false),(91,false)]
theorem der_26514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26514 :=
  CNF.rup_sound cl_26514 [cl_4771,cl_26489] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4771 v h) (hints_cons _ _ _ (der_26489 v h) (by intro d hd; cases hd)))
def cl_26515 : CNF.NClause := [(37,false),(6,false),(74,false),(70,true),(66,false),(78,false),(91,false)]
theorem der_26515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26515 :=
  CNF.rup_sound cl_26515 [cl_4773,cl_26501] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4773 v h) (hints_cons _ _ _ (der_26501 v h) (by intro d hd; cases hd)))
def cl_26516 : CNF.NClause := [(37,false),(6,true),(66,false),(74,false),(78,false),(70,true),(91,false)]
theorem der_26516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26516 :=
  CNF.rup_sound cl_26516 [cl_4774,cl_26502] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4774 v h) (hints_cons _ _ _ (der_26502 v h) (by intro d hd; cases hd)))
def cl_26517 : CNF.NClause := [(37,false),(66,true),(6,false),(70,true),(74,false),(78,false),(91,false)]
theorem der_26517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26517 :=
  CNF.rup_sound cl_26517 [cl_4775,cl_26489] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4775 v h) (hints_cons _ _ _ (der_26489 v h) (by intro d hd; cases hd)))
def cl_26518 : CNF.NClause := [(37,false),(82,true),(6,true),(66,true),(74,false),(78,false),(91,false)]
theorem der_26518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26518 :=
  CNF.rup_sound cl_26518 [cl_4776,cl_26330] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4776 v h) (hints_cons _ _ _ (der_26330 v h) (by intro d hd; cases hd)))
def cl_26519 : CNF.NClause := [(37,false),(6,false),(82,true),(66,false),(78,false),(70,false),(91,false)]
theorem der_26519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26519 :=
  CNF.rup_sound cl_26519 [cl_4777,cl_4769] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4777 v h) (hints_cons _ _ _ (inp_4769 v h) (by intro d hd; cases hd)))
def cl_26520 : CNF.NClause := [(37,false),(82,true),(6,true),(66,false),(78,false),(91,false),(70,false)]
theorem der_26520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26520 :=
  CNF.rup_sound cl_26520 [cl_4778,cl_26513] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4778 v h) (hints_cons _ _ _ (der_26513 v h) (by intro d hd; cases hd)))
def cl_26521 : CNF.NClause := [(37,false),(66,true),(6,false),(70,false),(74,true),(78,false),(91,false)]
theorem der_26521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26521 :=
  CNF.rup_sound cl_26521 [cl_4779,cl_26492] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4779 v h) (hints_cons _ _ _ (der_26492 v h) (by intro d hd; cases hd)))
def cl_26522 : CNF.NClause := [(37,false),(6,true),(74,true),(70,false),(78,false),(82,true),(91,false)]
theorem der_26522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26522 :=
  CNF.rup_sound cl_26522 [cl_4780,cl_26520] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4780 v h) (hints_cons _ _ _ (der_26520 v h) (by intro d hd; cases hd)))
def cl_26523 : CNF.NClause := [(37,false),(6,false),(66,false),(74,true),(70,true),(78,false),(91,false)]
theorem der_26523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26523 :=
  CNF.rup_sound cl_26523 [cl_4781,cl_26509] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4781 v h) (hints_cons _ _ _ (der_26509 v h) (by intro d hd; cases hd)))
def cl_26524 : CNF.NClause := [(37,false),(82,true),(66,false),(74,true),(70,true),(78,false),(91,false)]
theorem der_26524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26524 :=
  CNF.rup_sound cl_26524 [cl_4782,cl_26523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4782 v h) (hints_cons _ _ _ (der_26523 v h) (by intro d hd; cases hd)))
def cl_26525 : CNF.NClause := [(37,false),(66,true),(6,false),(70,true),(74,true),(78,false),(91,false)]
theorem der_26525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26525 :=
  CNF.rup_sound cl_26525 [cl_4783,cl_26496] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4783 v h) (hints_cons _ _ _ (der_26496 v h) (by intro d hd; cases hd)))
def cl_26526 : CNF.NClause := [(37,false),(66,true),(6,true),(74,true),(70,true),(78,false),(91,false)]
theorem der_26526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26526 :=
  CNF.rup_sound cl_26526 [cl_4784,cl_26512] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4784 v h) (hints_cons _ _ _ (der_26512 v h) (by intro d hd; cases hd)))
def cl_26527 : CNF.NClause := [(37,false),(6,false),(66,false),(70,false),(74,false),(78,true),(91,false)]
theorem der_26527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26527 :=
  CNF.rup_sound cl_26527 [cl_4785,cl_26505] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4785 v h) (hints_cons _ _ _ (der_26505 v h) (by intro d hd; cases hd)))
def cl_26528 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,false),(78,true),(91,false)]
theorem der_26528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26528 :=
  CNF.rup_sound cl_26528 [cl_4786,cl_26506] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4786 v h) (hints_cons _ _ _ (der_26506 v h) (by intro d hd; cases hd)))
def cl_26529 : CNF.NClause := [(37,false),(6,false),(70,false),(74,false),(78,true),(82,true),(91,false)]
theorem der_26529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26529 :=
  CNF.rup_sound cl_26529 [cl_4787,cl_26527] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4787 v h) (hints_cons _ _ _ (der_26527 v h) (by intro d hd; cases hd)))
def cl_26530 : CNF.NClause := [(37,false),(82,true),(66,true),(74,false),(70,false),(78,true),(91,false)]
theorem der_26530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26530 :=
  CNF.rup_sound cl_26530 [cl_4788,cl_26529] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4788 v h) (hints_cons _ _ _ (der_26529 v h) (by intro d hd; cases hd)))
def cl_26531 : CNF.NClause := [(37,false),(82,true),(6,false),(66,false),(74,false),(78,true),(91,false)]
theorem der_26531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26531 :=
  CNF.rup_sound cl_26531 [cl_4789,cl_26529] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4789 v h) (hints_cons _ _ _ (der_26529 v h) (by intro d hd; cases hd)))
def cl_26532 : CNF.NClause := [(37,false),(82,true),(66,false),(70,true),(74,false),(78,true),(91,false)]
theorem der_26532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26532 :=
  CNF.rup_sound cl_26532 [cl_4790,cl_26531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4790 v h) (hints_cons _ _ _ (der_26531 v h) (by intro d hd; cases hd)))
def cl_26533 : CNF.NClause := [(37,false),(6,false),(70,true),(74,false),(78,true),(82,true),(91,false)]
theorem der_26533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26533 :=
  CNF.rup_sound cl_26533 [cl_4791,cl_26531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4791 v h) (hints_cons _ _ _ (der_26531 v h) (by intro d hd; cases hd)))
def cl_26534 : CNF.NClause := [(37,false),(82,true),(6,true),(66,true),(70,true),(74,false),(91,false)]
theorem der_26534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26534 :=
  CNF.rup_sound cl_26534 [cl_4792,cl_26518] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4792 v h) (hints_cons _ _ _ (der_26518 v h) (by intro d hd; cases hd)))
def cl_26535 : CNF.NClause := [(37,false),(78,true),(6,false),(66,false),(70,false),(82,true),(91,false)]
theorem der_26535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26535 :=
  CNF.rup_sound cl_26535 [cl_4793,cl_26529] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4793 v h) (hints_cons _ _ _ (der_26529 v h) (by intro d hd; cases hd)))
def cl_26536 : CNF.NClause := [(37,false),(78,true),(66,false),(70,false),(74,true),(82,true),(91,false)]
theorem der_26536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26536 :=
  CNF.rup_sound cl_26536 [cl_4794,cl_26535] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4794 v h) (hints_cons _ _ _ (der_26535 v h) (by intro d hd; cases hd)))
def cl_26537 : CNF.NClause := [(37,false),(66,true),(6,false),(70,false),(74,true),(82,true),(91,false)]
theorem der_26537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26537 :=
  CNF.rup_sound cl_26537 [cl_4795,cl_26521] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4795 v h) (hints_cons _ _ _ (der_26521 v h) (by intro d hd; cases hd)))
def cl_26538 : CNF.NClause := [(37,false),(78,true),(6,true),(66,true),(70,false),(82,true),(91,false)]
theorem der_26538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26538 :=
  CNF.rup_sound cl_26538 [cl_4796,cl_26530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4796 v h) (hints_cons _ _ _ (der_26530 v h) (by intro d hd; cases hd)))
def cl_26539 : CNF.NClause := [(37,false),(78,true),(6,false),(66,false),(74,true),(82,true),(91,false)]
theorem der_26539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26539 :=
  CNF.rup_sound cl_26539 [cl_4797,cl_26535] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4797 v h) (hints_cons _ _ _ (der_26535 v h) (by intro d hd; cases hd)))
def cl_26540 : CNF.NClause := [(37,false),(78,true),(66,false),(74,true),(70,true),(82,true),(91,false)]
theorem der_26540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26540 :=
  CNF.rup_sound cl_26540 [cl_4798,cl_26539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4798 v h) (hints_cons _ _ _ (der_26539 v h) (by intro d hd; cases hd)))
def cl_26541 : CNF.NClause := [(37,false),(6,false),(70,true),(74,true),(78,true),(82,true),(91,false)]
theorem der_26541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26541 :=
  CNF.rup_sound cl_26541 [cl_4799,cl_26540] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4799 v h) (hints_cons _ _ _ (der_26540 v h) (by intro d hd; cases hd)))
def cl_26542 : CNF.NClause := [(37,false),(78,true),(66,true),(74,true),(70,true),(82,true),(91,false)]
theorem der_26542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26542 :=
  CNF.rup_sound cl_26542 [cl_4800,cl_26541] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4800 v h) (hints_cons _ _ _ (der_26541 v h) (by intro d hd; cases hd)))
def cl_26543 : CNF.NClause := [(37,false),(74,false),(6,true),(66,false),(70,false),(82,false),(78,false)]
theorem der_26543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26543 :=
  CNF.rup_sound cl_26543 [cl_4802,cl_26486] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4802 v h) (hints_cons _ _ _ (der_26486 v h) (by intro d hd; cases hd)))
def cl_26544 : CNF.NClause := [(37,false),(66,true),(6,false),(70,false),(74,false),(78,false),(82,false)]
theorem der_26544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26544 :=
  CNF.rup_sound cl_26544 [cl_4803,cl_26489] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4803 v h) (hints_cons _ _ _ (der_26489 v h) (by intro d hd; cases hd)))
def cl_26545 : CNF.NClause := [(37,false),(66,true),(6,true),(74,false),(70,false),(78,false),(82,false)]
theorem der_26545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26545 :=
  CNF.rup_sound cl_26545 [cl_4804,cl_26500] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4804 v h) (hints_cons _ _ _ (der_26500 v h) (by intro d hd; cases hd)))
def cl_26546 : CNF.NClause := [(37,false),(70,true),(6,false),(66,false),(78,false),(82,false),(74,false)]
theorem der_26546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26546 :=
  CNF.rup_sound cl_26546 [cl_4805,cl_26501] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4805 v h) (hints_cons _ _ _ (der_26501 v h) (by intro d hd; cases hd)))
def cl_26547 : CNF.NClause := [(37,false),(70,true),(66,false),(74,false),(78,false),(82,false),(91,true)]
theorem der_26547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26547 :=
  CNF.rup_sound cl_26547 [cl_4806,cl_26546] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4806 v h) (hints_cons _ _ _ (der_26546 v h) (by intro d hd; cases hd)))
def cl_26548 : CNF.NClause := [(37,false),(66,true),(6,false),(70,true),(74,false),(78,false),(82,false)]
theorem der_26548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26548 :=
  CNF.rup_sound cl_26548 [cl_4807,cl_26489] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4807 v h) (hints_cons _ _ _ (der_26489 v h) (by intro d hd; cases hd)))
def cl_26549 : CNF.NClause := [(37,false),(66,true),(6,true),(74,false),(78,false),(82,false),(91,true)]
theorem der_26549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26549 :=
  CNF.rup_sound cl_26549 [cl_4808,cl_26545] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4808 v h) (hints_cons _ _ _ (der_26545 v h) (by intro d hd; cases hd)))
def cl_26550 : CNF.NClause := [(37,false),(74,true),(6,false),(78,false),(66,false),(82,false),(70,false)]
theorem der_26550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26550 :=
  CNF.rup_sound cl_26550 [cl_4809,cl_4745] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4809 v h) (hints_cons _ _ _ (inp_4745 v h) (by intro d hd; cases hd)))
def cl_26551 : CNF.NClause := [(37,false),(74,true),(91,true),(78,false),(66,false),(82,false),(70,false)]
theorem der_26551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26551 :=
  CNF.rup_sound cl_26551 [cl_4810,cl_26550] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4810 v h) (hints_cons _ _ _ (der_26550 v h) (by intro d hd; cases hd)))
def cl_26552 : CNF.NClause := [(37,false),(66,true),(6,false),(70,false),(74,true),(78,false),(82,false)]
theorem der_26552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26552 :=
  CNF.rup_sound cl_26552 [cl_4811,cl_26492] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4811 v h) (hints_cons _ _ _ (der_26492 v h) (by intro d hd; cases hd)))
def cl_26553 : CNF.NClause := [(37,false),(66,true),(6,true),(70,false),(78,false),(82,false),(91,true)]
theorem der_26553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26553 :=
  CNF.rup_sound cl_26553 [cl_4812,cl_26545] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4812 v h) (hints_cons _ _ _ (der_26545 v h) (by intro d hd; cases hd)))
def cl_26555 : CNF.NClause := [(37,false),(74,true),(6,true),(66,false),(70,true),(82,false),(78,false)]
theorem der_26555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26555 :=
  CNF.rup_sound cl_26555 [cl_4814,cl_26495] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4814 v h) (hints_cons _ _ _ (der_26495 v h) (by intro d hd; cases hd)))
def cl_26556 : CNF.NClause := [(37,false),(66,true),(6,false),(70,true),(74,true),(78,false),(82,false)]
theorem der_26556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26556 :=
  CNF.rup_sound cl_26556 [cl_4815,cl_26496] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4815 v h) (hints_cons _ _ _ (der_26496 v h) (by intro d hd; cases hd)))
def cl_26557 : CNF.NClause := [(37,false),(66,true),(6,true),(74,true),(70,true),(82,false),(78,false)]
theorem der_26557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26557 :=
  CNF.rup_sound cl_26557 [cl_4816,cl_26512] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4816 v h) (hints_cons _ _ _ (der_26512 v h) (by intro d hd; cases hd)))
def cl_26558 : CNF.NClause := [(37,false),(78,true),(6,false),(66,false),(70,false),(74,false),(82,false)]
theorem der_26558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26558 :=
  CNF.rup_sound cl_26558 [cl_4817,cl_26505] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4817 v h) (hints_cons _ _ _ (der_26505 v h) (by intro d hd; cases hd)))
def cl_26559 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,false),(82,false),(91,true)]
theorem der_26559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26559 :=
  CNF.rup_sound cl_26559 [cl_4818,cl_26543] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4818 v h) (hints_cons _ _ _ (der_26543 v h) (by intro d hd; cases hd)))
def cl_26560 : CNF.NClause := [(37,false),(66,true),(6,false),(70,false),(74,false),(82,false),(91,true)]
theorem der_26560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26560 :=
  CNF.rup_sound cl_26560 [cl_4819,cl_26544] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4819 v h) (hints_cons _ _ _ (der_26544 v h) (by intro d hd; cases hd)))
def cl_26561 : CNF.NClause := [(37,false),(6,true),(66,true),(74,false),(70,false),(82,false),(91,true)]
theorem der_26561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26561 :=
  CNF.rup_sound cl_26561 [cl_4820,cl_26545] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4820 v h) (hints_cons _ _ _ (der_26545 v h) (by intro d hd; cases hd)))
def cl_26562 : CNF.NClause := [(37,false),(78,true),(6,false),(66,false),(74,false),(82,false),(91,true)]
theorem der_26562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26562 :=
  CNF.rup_sound cl_26562 [cl_4821,cl_26558] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4821 v h) (hints_cons _ _ _ (der_26558 v h) (by intro d hd; cases hd)))
def cl_26563 : CNF.NClause := [(37,false),(78,true),(6,true),(66,false),(70,true),(74,false),(82,false)]
theorem der_26563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26563 :=
  CNF.rup_sound cl_26563 [cl_4822,cl_26502] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4822 v h) (hints_cons _ _ _ (der_26502 v h) (by intro d hd; cases hd)))
def cl_26565 : CNF.NClause := [(37,false),(78,true),(6,true),(70,true),(74,false),(82,false),(91,true)]
theorem der_26565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26565 :=
  CNF.rup_sound cl_26565 [cl_4824,cl_26563] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4824 v h) (hints_cons _ _ _ (der_26563 v h) (by intro d hd; cases hd)))
def cl_26566 : CNF.NClause := [(37,false),(78,true),(6,false),(66,false),(70,false),(82,false),(91,true)]
theorem der_26566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26566 :=
  CNF.rup_sound cl_26566 [cl_4825,cl_26558] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4825 v h) (hints_cons _ _ _ (der_26558 v h) (by intro d hd; cases hd)))
def cl_26567 : CNF.NClause := [(37,false),(78,true),(66,false),(70,false),(74,true),(82,false),(91,true)]
theorem der_26567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26567 :=
  CNF.rup_sound cl_26567 [cl_4826,cl_26566] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4826 v h) (hints_cons _ _ _ (der_26566 v h) (by intro d hd; cases hd)))
def cl_26568 : CNF.NClause := [(37,false),(6,false),(70,false),(74,true),(78,true),(82,false),(91,true)]
theorem der_26568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26568 :=
  CNF.rup_sound cl_26568 [cl_4827,cl_26566] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4827 v h) (hints_cons _ _ _ (der_26566 v h) (by intro d hd; cases hd)))
def cl_26569 : CNF.NClause := [(37,false),(78,true),(6,true),(70,false),(74,true),(82,false),(91,true)]
theorem der_26569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26569 :=
  CNF.rup_sound cl_26569 [cl_4828,cl_26567] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4828 v h) (hints_cons _ _ _ (der_26567 v h) (by intro d hd; cases hd)))
def cl_26570 : CNF.NClause := [(37,false),(78,true),(6,false),(66,false),(74,true),(82,false),(91,true)]
theorem der_26570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26570 :=
  CNF.rup_sound cl_26570 [cl_4829,cl_26566] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4829 v h) (hints_cons _ _ _ (der_26566 v h) (by intro d hd; cases hd)))
def cl_26571 : CNF.NClause := [(37,false),(78,true),(66,false),(74,true),(70,true),(82,false),(91,true)]
theorem der_26571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26571 :=
  CNF.rup_sound cl_26571 [cl_4830,cl_26570] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4830 v h) (hints_cons _ _ _ (der_26570 v h) (by intro d hd; cases hd)))
def cl_26573 : CNF.NClause := [(37,false),(78,true),(6,true),(74,true),(70,true),(82,false),(91,true)]
theorem der_26573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26573 :=
  CNF.rup_sound cl_26573 [cl_4832,cl_26571] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4832 v h) (hints_cons _ _ _ (der_26571 v h) (by intro d hd; cases hd)))
def cl_26574 : CNF.NClause := [(37,false),(82,true),(6,false),(74,false),(70,false),(66,false),(78,false)]
theorem der_26574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26574 :=
  CNF.rup_sound cl_26574 [cl_4833,cl_26519] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4833 v h) (hints_cons _ _ _ (der_26519 v h) (by intro d hd; cases hd)))
def cl_26575 : CNF.NClause := [(37,false),(82,true),(6,true),(66,false),(70,false),(78,false),(74,false)]
theorem der_26575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26575 :=
  CNF.rup_sound cl_26575 [cl_4834,cl_26520] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4834 v h) (hints_cons _ _ _ (der_26520 v h) (by intro d hd; cases hd)))
def cl_26576 : CNF.NClause := [(37,false),(66,true),(6,false),(70,false),(74,false),(78,false),(91,true)]
theorem der_26576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26576 :=
  CNF.rup_sound cl_26576 [cl_4835,cl_26544] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4835 v h) (hints_cons _ _ _ (der_26544 v h) (by intro d hd; cases hd)))
def cl_26577 : CNF.NClause := [(37,false),(66,true),(74,false),(78,false),(70,false),(82,true),(91,true)]
theorem der_26577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26577 :=
  CNF.rup_sound cl_26577 [cl_4836,cl_26576] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4836 v h) (hints_cons _ _ _ (der_26576 v h) (by intro d hd; cases hd)))
def cl_26578 : CNF.NClause := [(37,false),(6,false),(66,false),(70,true),(78,false),(74,false),(91,true)]
theorem der_26578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26578 :=
  CNF.rup_sound cl_26578 [cl_4837,cl_26546] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4837 v h) (hints_cons _ _ _ (der_26546 v h) (by intro d hd; cases hd)))
def cl_26579 : CNF.NClause := [(37,false),(82,true),(66,false),(74,false),(78,false),(70,true),(91,true)]
theorem der_26579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26579 :=
  CNF.rup_sound cl_26579 [cl_4838,cl_26578] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4838 v h) (hints_cons _ _ _ (der_26578 v h) (by intro d hd; cases hd)))
def cl_26580 : CNF.NClause := [(37,false),(6,false),(70,true),(74,false),(78,false),(82,true),(91,true)]
theorem der_26580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26580 :=
  CNF.rup_sound cl_26580 [cl_4839,cl_26578] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4839 v h) (hints_cons _ _ _ (der_26578 v h) (by intro d hd; cases hd)))
def cl_26581 : CNF.NClause := [(37,false),(82,true),(6,true),(66,true),(74,false),(78,false),(70,true)]
theorem der_26581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26581 :=
  CNF.rup_sound cl_26581 [cl_4840,cl_26518] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4840 v h) (hints_cons _ _ _ (der_26518 v h) (by intro d hd; cases hd)))
def cl_26582 : CNF.NClause := [(37,false),(82,true),(6,false),(66,false),(78,false),(70,false),(91,true)]
theorem der_26582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26582 :=
  CNF.rup_sound cl_26582 [cl_4841,cl_26574] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4841 v h) (hints_cons _ _ _ (der_26574 v h) (by intro d hd; cases hd)))
def cl_26583 : CNF.NClause := [(37,false),(82,true),(6,true),(66,false),(70,false),(78,false),(74,true)]
theorem der_26583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26583 :=
  CNF.rup_sound cl_26583 [cl_4842,cl_26520] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4842 v h) (hints_cons _ _ _ (der_26520 v h) (by intro d hd; cases hd)))
def cl_26584 : CNF.NClause := [(37,false),(66,true),(6,false),(70,false),(74,true),(78,false),(82,true)]
theorem der_26584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26584 :=
  CNF.rup_sound cl_26584 [cl_4843,cl_26521] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4843 v h) (hints_cons _ _ _ (der_26521 v h) (by intro d hd; cases hd)))
def cl_26585 : CNF.NClause := [(37,false),(66,true),(74,true),(70,false),(78,false),(82,true),(91,true)]
theorem der_26585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26585 :=
  CNF.rup_sound cl_26585 [cl_4844,cl_26584] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4844 v h) (hints_cons _ _ _ (der_26584 v h) (by intro d hd; cases hd)))
def cl_26586 : CNF.NClause := [(37,false),(82,true),(6,false),(66,false),(74,true),(70,true),(78,false)]
theorem der_26586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26586 :=
  CNF.rup_sound cl_26586 [cl_4845,cl_26523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4845 v h) (hints_cons _ _ _ (der_26523 v h) (by intro d hd; cases hd)))
def cl_26587 : CNF.NClause := [(37,false),(82,true),(66,false),(74,true),(70,true),(78,false),(91,true)]
theorem der_26587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26587 :=
  CNF.rup_sound cl_26587 [cl_4846,cl_26586] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4846 v h) (hints_cons _ _ _ (der_26586 v h) (by intro d hd; cases hd)))
def cl_26588 : CNF.NClause := [(37,false),(6,false),(70,true),(74,true),(78,false),(82,true),(91,true)]
theorem der_26588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26588 :=
  CNF.rup_sound cl_26588 [cl_4847,cl_26587] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4847 v h) (hints_cons _ _ _ (der_26587 v h) (by intro d hd; cases hd)))
def cl_26589 : CNF.NClause := [(37,false),(82,true),(6,true),(66,true),(70,true),(78,false),(91,true)]
theorem der_26589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26589 :=
  CNF.rup_sound cl_26589 [cl_4848,cl_26581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4848 v h) (hints_cons _ _ _ (der_26581 v h) (by intro d hd; cases hd)))
def cl_26590 : CNF.NClause := [(37,false),(82,true),(6,false),(66,false),(70,false),(74,false),(78,true)]
theorem der_26590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26590 :=
  CNF.rup_sound cl_26590 [cl_4849,cl_26529] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4849 v h) (hints_cons _ _ _ (der_26529 v h) (by intro d hd; cases hd)))
def cl_26591 : CNF.NClause := [(37,false),(82,true),(66,false),(70,false),(74,false),(78,true),(91,true)]
theorem der_26591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26591 :=
  CNF.rup_sound cl_26591 [cl_4850,cl_26590] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4850 v h) (hints_cons _ _ _ (der_26590 v h) (by intro d hd; cases hd)))
def cl_26592 : CNF.NClause := [(37,false),(66,true),(6,false),(70,false),(74,false),(78,true),(82,true)]
theorem der_26592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26592 :=
  CNF.rup_sound cl_26592 [cl_4851,cl_26530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4851 v h) (hints_cons _ _ _ (der_26530 v h) (by intro d hd; cases hd)))
def cl_26593 : CNF.NClause := [(37,false),(82,true),(6,true),(66,true),(74,false),(70,false),(78,true)]
theorem der_26593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26593 :=
  CNF.rup_sound cl_26593 [cl_4852,cl_26530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4852 v h) (hints_cons _ _ _ (der_26530 v h) (by intro d hd; cases hd)))
def cl_26594 : CNF.NClause := [(37,false),(82,true),(6,false),(66,false),(70,true),(74,false),(78,true)]
theorem der_26594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26594 :=
  CNF.rup_sound cl_26594 [cl_4853,cl_26531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4853 v h) (hints_cons _ _ _ (der_26531 v h) (by intro d hd; cases hd)))
def cl_26595 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,false),(78,true),(91,true)]
theorem der_26595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26595 :=
  CNF.rup_sound cl_26595 [cl_4854,cl_26563] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4854 v h) (hints_cons _ _ _ (der_26563 v h) (by intro d hd; cases hd)))
def cl_26596 : CNF.NClause := [(37,false),(66,true),(6,false),(70,true),(74,false),(82,true),(91,true)]
theorem der_26596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26596 :=
  CNF.rup_sound cl_26596 [cl_4855,cl_26580] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4855 v h) (hints_cons _ _ _ (der_26580 v h) (by intro d hd; cases hd)))
def cl_26597 : CNF.NClause := [(37,false),(82,true),(6,true),(66,true),(70,true),(74,false),(91,true)]
theorem der_26597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26597 :=
  CNF.rup_sound cl_26597 [cl_4856,cl_26581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4856 v h) (hints_cons _ _ _ (der_26581 v h) (by intro d hd; cases hd)))
def cl_26598 : CNF.NClause := [(37,false),(78,true),(6,false),(66,false),(70,false),(74,true),(91,true)]
theorem der_26598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26598 :=
  CNF.rup_sound cl_26598 [cl_4857,cl_26570] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4857 v h) (hints_cons _ _ _ (der_26570 v h) (by intro d hd; cases hd)))
def cl_26599 : CNF.NClause := [(37,false),(78,true),(6,true),(66,false),(70,false),(74,true),(82,true)]
theorem der_26599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26599 :=
  CNF.rup_sound cl_26599 [cl_4858,cl_26536] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4858 v h) (hints_cons _ _ _ (der_26536 v h) (by intro d hd; cases hd)))
def cl_26600 : CNF.NClause := [(37,false),(66,true),(6,false),(70,false),(74,true),(82,true),(91,true)]
theorem der_26600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26600 :=
  CNF.rup_sound cl_26600 [cl_4859,cl_26584] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4859 v h) (hints_cons _ _ _ (der_26584 v h) (by intro d hd; cases hd)))
def cl_26601 : CNF.NClause := [(37,false),(78,true),(6,true),(66,true),(70,false),(82,true),(91,true)]
theorem der_26601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26601 :=
  CNF.rup_sound cl_26601 [cl_4860,cl_26593] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4860 v h) (hints_cons _ _ _ (der_26593 v h) (by intro d hd; cases hd)))
def cl_26602 : CNF.NClause := [(37,false),(78,true),(6,false),(66,false),(74,true),(70,true),(91,true)]
theorem der_26602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26602 :=
  CNF.rup_sound cl_26602 [cl_4861,cl_26570] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4861 v h) (hints_cons _ _ _ (der_26570 v h) (by intro d hd; cases hd)))
def cl_26603 : CNF.NClause := [(37,false),(78,true),(6,true),(66,false),(74,true),(70,true),(91,true)]
theorem der_26603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26603 :=
  CNF.rup_sound cl_26603 [cl_4862,cl_26571] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4862 v h) (hints_cons _ _ _ (der_26571 v h) (by intro d hd; cases hd)))
def cl_26605 : CNF.NClause := [(37,false),(78,true),(6,true),(66,true),(74,true),(70,true),(91,true)]
theorem der_26605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26605 :=
  CNF.rup_sound cl_26605 [cl_4864,cl_26573] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4864 v h) (hints_cons _ _ _ (der_26573 v h) (by intro d hd; cases hd)))
def cl_26606 : CNF.NClause := [(36,false),(92,false),(5,true),(86,false),(84,false),(83,false),(85,false)]
theorem der_26606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26606 :=
  CNF.rup_sound cl_26606 [cl_4610,cl_4612] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4610 v h) (hints_cons _ _ _ (inp_4612 v h) (by intro d hd; cases hd)))
def cl_26607 : CNF.NClause := [(36,false),(82,true),(83,false),(84,false),(85,false),(86,false),(92,false)]
theorem der_26607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26607 :=
  CNF.rup_sound cl_26607 [cl_4611,cl_4612] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4611 v h) (hints_cons _ _ _ (inp_4612 v h) (by intro d hd; cases hd)))
def cl_26608 : CNF.NClause := [(36,false),(83,true),(82,false),(84,false),(85,false),(86,false),(92,false)]
theorem der_26608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26608 :=
  CNF.rup_sound cl_26608 [cl_4614,cl_4613] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4614 v h) (hints_cons _ _ _ (inp_4613 v h) (by intro d hd; cases hd)))
def cl_26609 : CNF.NClause := [(36,false),(5,false),(83,true),(84,false),(85,false),(86,false),(92,false)]
theorem der_26609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26609 :=
  CNF.rup_sound cl_26609 [cl_4615,cl_4613] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4615 v h) (hints_cons _ _ _ (inp_4613 v h) (by intro d hd; cases hd)))
def cl_26610 : CNF.NClause := [(36,false),(5,true),(82,true),(84,false),(85,false),(86,false),(92,false)]
theorem der_26610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26610 :=
  CNF.rup_sound cl_26610 [cl_4616,cl_4612] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4616 v h) (hints_cons _ _ _ (inp_4612 v h) (by intro d hd; cases hd)))
def cl_26611 : CNF.NClause := [(36,false),(92,false),(5,true),(82,false),(83,false),(86,false),(85,false)]
theorem der_26611 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26611 :=
  CNF.rup_sound cl_26611 [cl_4618,cl_26606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4618 v h) (hints_cons _ _ _ (der_26606 v h) (by intro d hd; cases hd)))
def cl_26612 : CNF.NClause := [(36,false),(5,false),(83,false),(84,true),(85,false),(86,false),(92,false)]
theorem der_26612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26612 :=
  CNF.rup_sound cl_26612 [cl_4619,cl_4617] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4619 v h) (hints_cons _ _ _ (inp_4617 v h) (by intro d hd; cases hd)))
def cl_26613 : CNF.NClause := [(36,false),(82,true),(5,true),(85,false),(83,false),(86,false),(92,false)]
theorem der_26613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26613 :=
  CNF.rup_sound cl_26613 [cl_4620,cl_4612] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4620 v h) (hints_cons _ _ _ (inp_4612 v h) (by intro d hd; cases hd)))
def cl_26614 : CNF.NClause := [(36,false),(5,false),(82,false),(84,true),(85,false),(86,false),(92,false)]
theorem der_26614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26614 :=
  CNF.rup_sound cl_26614 [cl_4621,cl_4617] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4621 v h) (hints_cons _ _ _ (inp_4617 v h) (by intro d hd; cases hd)))
def cl_26615 : CNF.NClause := [(36,false),(83,true),(5,true),(82,false),(85,false),(86,false),(92,false)]
theorem der_26615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26615 :=
  CNF.rup_sound cl_26615 [cl_4622,cl_26608] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4622 v h) (hints_cons _ _ _ (der_26608 v h) (by intro d hd; cases hd)))
def cl_26616 : CNF.NClause := [(36,false),(82,true),(5,false),(84,true),(85,false),(86,false),(92,false)]
theorem der_26616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26616 :=
  CNF.rup_sound cl_26616 [cl_4623,cl_26612] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4623 v h) (hints_cons _ _ _ (der_26612 v h) (by intro d hd; cases hd)))
def cl_26617 : CNF.NClause := [(36,false),(83,true),(5,true),(82,true),(85,false),(86,false),(92,false)]
theorem der_26617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26617 :=
  CNF.rup_sound cl_26617 [cl_4624,cl_26610] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4624 v h) (hints_cons _ _ _ (der_26610 v h) (by intro d hd; cases hd)))
def cl_26618 : CNF.NClause := [(36,false),(85,true),(82,false),(83,false),(86,false),(84,false),(92,false)]
theorem der_26618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26618 :=
  CNF.rup_sound cl_26618 [cl_4626,cl_4625] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4626 v h) (hints_cons _ _ _ (inp_4625 v h) (by intro d hd; cases hd)))
def cl_26619 : CNF.NClause := [(36,false),(5,false),(83,false),(84,false),(85,true),(86,false),(92,false)]
theorem der_26619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26619 :=
  CNF.rup_sound cl_26619 [cl_4627,cl_4625] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4627 v h) (hints_cons _ _ _ (inp_4625 v h) (by intro d hd; cases hd)))
def cl_26620 : CNF.NClause := [(36,false),(92,false),(5,true),(86,false),(82,true),(84,false),(83,false)]
theorem der_26620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26620 :=
  CNF.rup_sound cl_26620 [cl_4628,cl_26606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4628 v h) (hints_cons _ _ _ (der_26606 v h) (by intro d hd; cases hd)))
def cl_26621 : CNF.NClause := [(36,false),(5,false),(82,false),(84,false),(85,true),(86,false),(92,false)]
theorem der_26621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26621 :=
  CNF.rup_sound cl_26621 [cl_4629,cl_4625] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4629 v h) (hints_cons _ _ _ (inp_4625 v h) (by intro d hd; cases hd)))
def cl_26622 : CNF.NClause := [(36,false),(5,true),(82,false),(84,false),(85,true),(86,false),(92,false)]
theorem der_26622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26622 :=
  CNF.rup_sound cl_26622 [cl_4630,cl_26618] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4630 v h) (hints_cons _ _ _ (der_26618 v h) (by intro d hd; cases hd)))
def cl_26623 : CNF.NClause := [(36,false),(82,true),(5,false),(84,false),(85,true),(86,false),(92,false)]
theorem der_26623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26623 :=
  CNF.rup_sound cl_26623 [cl_4631,cl_26619] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4631 v h) (hints_cons _ _ _ (der_26619 v h) (by intro d hd; cases hd)))
def cl_26624 : CNF.NClause := [(36,false),(83,true),(5,true),(82,true),(84,false),(86,false),(92,false)]
theorem der_26624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26624 :=
  CNF.rup_sound cl_26624 [cl_4632,cl_26610] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4632 v h) (hints_cons _ _ _ (der_26610 v h) (by intro d hd; cases hd)))
def cl_26625 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(85,true),(86,false),(92,false)]
theorem der_26625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26625 :=
  CNF.rup_sound cl_26625 [cl_4633,cl_26618] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4633 v h) (hints_cons _ _ _ (der_26618 v h) (by intro d hd; cases hd)))
def cl_26626 : CNF.NClause := [(36,false),(85,true),(5,true),(82,false),(86,false),(83,false),(92,false)]
theorem der_26626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26626 :=
  CNF.rup_sound cl_26626 [cl_4634,cl_26618] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4634 v h) (hints_cons _ _ _ (der_26618 v h) (by intro d hd; cases hd)))
def cl_26627 : CNF.NClause := [(36,false),(82,true),(5,false),(83,false),(84,true),(86,false),(92,false)]
theorem der_26627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26627 :=
  CNF.rup_sound cl_26627 [cl_4635,cl_26612] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4635 v h) (hints_cons _ _ _ (der_26612 v h) (by intro d hd; cases hd)))
def cl_26628 : CNF.NClause := [(36,false),(82,true),(84,true),(83,false),(85,true),(86,false),(92,false)]
theorem der_26628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26628 :=
  CNF.rup_sound cl_26628 [cl_4636,cl_26627] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4636 v h) (hints_cons _ _ _ (der_26627 v h) (by intro d hd; cases hd)))
def cl_26629 : CNF.NClause := [(36,false),(5,false),(82,false),(84,true),(85,true),(86,false),(92,false)]
theorem der_26629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26629 :=
  CNF.rup_sound cl_26629 [cl_4637,cl_26625] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4637 v h) (hints_cons _ _ _ (der_26625 v h) (by intro d hd; cases hd)))
def cl_26630 : CNF.NClause := [(36,false),(83,true),(5,true),(82,false),(84,true),(86,false),(92,false)]
theorem der_26630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26630 :=
  CNF.rup_sound cl_26630 [cl_4638,cl_26615] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4638 v h) (hints_cons _ _ _ (der_26615 v h) (by intro d hd; cases hd)))
def cl_26631 : CNF.NClause := [(36,false),(82,true),(5,false),(84,true),(85,true),(86,false),(92,false)]
theorem der_26631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26631 :=
  CNF.rup_sound cl_26631 [cl_4639,cl_26627] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4639 v h) (hints_cons _ _ _ (der_26627 v h) (by intro d hd; cases hd)))
def cl_26632 : CNF.NClause := [(36,false),(83,true),(82,true),(84,true),(85,true),(86,false),(92,false)]
theorem der_26632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26632 :=
  CNF.rup_sound cl_26632 [cl_4640,cl_26631] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4640 v h) (hints_cons _ _ _ (der_26631 v h) (by intro d hd; cases hd)))
def cl_26633 : CNF.NClause := [(36,false),(86,true),(82,false),(83,false),(84,false),(85,false),(92,false)]
theorem der_26633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26633 :=
  CNF.rup_sound cl_26633 [cl_4642,cl_4641] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4642 v h) (hints_cons _ _ _ (inp_4641 v h) (by intro d hd; cases hd)))
def cl_26634 : CNF.NClause := [(36,false),(5,false),(83,false),(84,false),(85,false),(86,true),(92,false)]
theorem der_26634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26634 :=
  CNF.rup_sound cl_26634 [cl_4643,cl_4641] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4643 v h) (hints_cons _ _ _ (inp_4641 v h) (by intro d hd; cases hd)))
def cl_26635 : CNF.NClause := [(36,false),(5,true),(82,true),(84,false),(85,false),(83,false),(92,false)]
theorem der_26635 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26635 :=
  CNF.rup_sound cl_26635 [cl_4644,cl_26607] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4644 v h) (hints_cons _ _ _ (der_26607 v h) (by intro d hd; cases hd)))
def cl_26636 : CNF.NClause := [(36,false),(83,true),(5,false),(82,false),(84,false),(85,false),(92,false)]
theorem der_26636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26636 :=
  CNF.rup_sound cl_26636 [cl_4645,cl_4613] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4645 v h) (hints_cons _ _ _ (inp_4613 v h) (by intro d hd; cases hd)))
def cl_26637 : CNF.NClause := [(36,false),(83,true),(82,false),(84,false),(85,false),(86,true),(92,false)]
theorem der_26637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26637 :=
  CNF.rup_sound cl_26637 [cl_4646,cl_26636] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4646 v h) (hints_cons _ _ _ (der_26636 v h) (by intro d hd; cases hd)))
def cl_26638 : CNF.NClause := [(36,false),(82,true),(5,false),(84,false),(85,false),(86,true),(92,false)]
theorem der_26638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26638 :=
  CNF.rup_sound cl_26638 [cl_4647,cl_26634] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4647 v h) (hints_cons _ _ _ (der_26634 v h) (by intro d hd; cases hd)))
def cl_26639 : CNF.NClause := [(36,false),(83,true),(5,true),(82,true),(84,false),(85,false),(92,false)]
theorem der_26639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26639 :=
  CNF.rup_sound cl_26639 [cl_4648,cl_26610] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4648 v h) (hints_cons _ _ _ (der_26610 v h) (by intro d hd; cases hd)))
def cl_26640 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(85,false),(86,true),(92,false)]
theorem der_26640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26640 :=
  CNF.rup_sound cl_26640 [cl_4649,cl_26634] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4649 v h) (hints_cons _ _ _ (der_26634 v h) (by intro d hd; cases hd)))
def cl_26641 : CNF.NClause := [(36,false),(86,true),(5,true),(82,false),(85,false),(83,false),(92,false)]
theorem der_26641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26641 :=
  CNF.rup_sound cl_26641 [cl_4650,cl_26633] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4650 v h) (hints_cons _ _ _ (der_26633 v h) (by intro d hd; cases hd)))
def cl_26642 : CNF.NClause := [(36,false),(82,true),(5,false),(83,false),(84,true),(85,false),(92,false)]
theorem der_26642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26642 :=
  CNF.rup_sound cl_26642 [cl_4651,cl_26612] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4651 v h) (hints_cons _ _ _ (der_26612 v h) (by intro d hd; cases hd)))
def cl_26643 : CNF.NClause := [(36,false),(84,true),(82,true),(83,false),(85,false),(86,true),(92,false)]
theorem der_26643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26643 :=
  CNF.rup_sound cl_26643 [cl_4652,cl_26642] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4652 v h) (hints_cons _ _ _ (der_26642 v h) (by intro d hd; cases hd)))
def cl_26644 : CNF.NClause := [(36,false),(5,false),(82,false),(84,true),(85,false),(86,true),(92,false)]
theorem der_26644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26644 :=
  CNF.rup_sound cl_26644 [cl_4653,cl_26640] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4653 v h) (hints_cons _ _ _ (der_26640 v h) (by intro d hd; cases hd)))
def cl_26645 : CNF.NClause := [(36,false),(83,true),(82,false),(84,true),(85,false),(86,true),(92,false)]
theorem der_26645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26645 :=
  CNF.rup_sound cl_26645 [cl_4654,cl_26644] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4654 v h) (hints_cons _ _ _ (der_26644 v h) (by intro d hd; cases hd)))
def cl_26646 : CNF.NClause := [(36,false),(5,false),(83,true),(84,true),(85,false),(86,true),(92,false)]
theorem der_26646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26646 :=
  CNF.rup_sound cl_26646 [cl_4655,cl_26644] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4655 v h) (hints_cons _ _ _ (der_26644 v h) (by intro d hd; cases hd)))
def cl_26647 : CNF.NClause := [(36,false),(83,true),(5,true),(84,true),(85,false),(86,true),(92,false)]
theorem der_26647 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26647 :=
  CNF.rup_sound cl_26647 [cl_4656,cl_26645] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4656 v h) (hints_cons _ _ _ (der_26645 v h) (by intro d hd; cases hd)))
def cl_26648 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(86,true),(84,false),(92,false)]
theorem der_26648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26648 :=
  CNF.rup_sound cl_26648 [cl_4657,cl_4641] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4657 v h) (hints_cons _ _ _ (inp_4641 v h) (by intro d hd; cases hd)))
def cl_26649 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(85,true),(84,false),(92,false)]
theorem der_26649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26649 :=
  CNF.rup_sound cl_26649 [cl_4658,cl_26622] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4658 v h) (hints_cons _ _ _ (der_26622 v h) (by intro d hd; cases hd)))
def cl_26650 : CNF.NClause := [(36,false),(82,true),(5,false),(83,false),(84,false),(85,true),(92,false)]
theorem der_26650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26650 :=
  CNF.rup_sound cl_26650 [cl_4659,cl_26619] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4659 v h) (hints_cons _ _ _ (der_26619 v h) (by intro d hd; cases hd)))
def cl_26651 : CNF.NClause := [(36,false),(5,true),(82,true),(84,false),(83,false),(86,true),(92,false)]
theorem der_26651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26651 :=
  CNF.rup_sound cl_26651 [cl_4660,cl_26635] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4660 v h) (hints_cons _ _ _ (der_26635 v h) (by intro d hd; cases hd)))
def cl_26652 : CNF.NClause := [(36,false),(5,false),(82,false),(84,false),(85,true),(86,true),(92,false)]
theorem der_26652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26652 :=
  CNF.rup_sound cl_26652 [cl_4661,cl_26648] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4661 v h) (hints_cons _ _ _ (der_26648 v h) (by intro d hd; cases hd)))
def cl_26653 : CNF.NClause := [(36,false),(83,true),(5,true),(82,false),(84,false),(86,true),(92,false)]
theorem der_26653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26653 :=
  CNF.rup_sound cl_26653 [cl_4662,cl_26637] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4662 v h) (hints_cons _ _ _ (der_26637 v h) (by intro d hd; cases hd)))
def cl_26654 : CNF.NClause := [(36,false),(82,true),(5,false),(83,true),(84,false),(85,true),(92,false)]
theorem der_26654 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26654 :=
  CNF.rup_sound cl_26654 [cl_4663,cl_26623] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4663 v h) (hints_cons _ _ _ (der_26623 v h) (by intro d hd; cases hd)))
def cl_26655 : CNF.NClause := [(36,false),(83,true),(5,true),(84,false),(85,true),(86,true),(92,false)]
theorem der_26655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26655 :=
  CNF.rup_sound cl_26655 [cl_4664,cl_26653] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4664 v h) (hints_cons _ _ _ (der_26653 v h) (by intro d hd; cases hd)))
def cl_26656 : CNF.NClause := [(36,false),(84,true),(5,false),(82,false),(83,false),(86,true),(92,false)]
theorem der_26656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26656 :=
  CNF.rup_sound cl_26656 [cl_4665,cl_26644] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4665 v h) (hints_cons _ _ _ (der_26644 v h) (by intro d hd; cases hd)))
def cl_26657 : CNF.NClause := [(36,false),(86,true),(82,false),(84,true),(85,true),(83,false),(92,false)]
theorem der_26657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26657 :=
  CNF.rup_sound cl_26657 [cl_4666,cl_26656] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4666 v h) (hints_cons _ _ _ (der_26656 v h) (by intro d hd; cases hd)))
def cl_26658 : CNF.NClause := [(36,false),(82,true),(5,false),(83,false),(84,true),(85,true),(92,false)]
theorem der_26658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26658 :=
  CNF.rup_sound cl_26658 [cl_4667,cl_26631] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4667 v h) (hints_cons _ _ _ (der_26631 v h) (by intro d hd; cases hd)))
def cl_26659 : CNF.NClause := [(36,false),(84,true),(5,true),(82,true),(83,false),(86,true),(92,false)]
theorem der_26659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26659 :=
  CNF.rup_sound cl_26659 [cl_4668,cl_26643] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4668 v h) (hints_cons _ _ _ (der_26643 v h) (by intro d hd; cases hd)))
def cl_26660 : CNF.NClause := [(36,false),(83,true),(5,false),(82,false),(84,true),(86,true),(92,false)]
theorem der_26660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26660 :=
  CNF.rup_sound cl_26660 [cl_4669,cl_26645] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4669 v h) (hints_cons _ _ _ (der_26645 v h) (by intro d hd; cases hd)))
def cl_26661 : CNF.NClause := [(36,false),(83,true),(5,true),(82,false),(84,true),(86,true),(92,false)]
theorem der_26661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26661 :=
  CNF.rup_sound cl_26661 [cl_4670,cl_26645] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4670 v h) (hints_cons _ _ _ (der_26645 v h) (by intro d hd; cases hd)))
def cl_26662 : CNF.NClause := [(36,false),(82,true),(5,false),(83,true),(84,true),(85,true),(92,false)]
theorem der_26662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26662 :=
  CNF.rup_sound cl_26662 [cl_4671,cl_26631] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4671 v h) (hints_cons _ _ _ (der_26631 v h) (by intro d hd; cases hd)))
def cl_26663 : CNF.NClause := [(36,false),(83,true),(5,true),(82,true),(84,true),(85,true),(92,false)]
theorem der_26663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26663 :=
  CNF.rup_sound cl_26663 [cl_4672,cl_26632] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4672 v h) (hints_cons _ _ _ (der_26632 v h) (by intro d hd; cases hd)))
def cl_26664 : CNF.NClause := [(36,false),(85,false),(5,true),(84,false),(86,false),(82,false),(83,false)]
theorem der_26664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26664 :=
  CNF.rup_sound cl_26664 [cl_4674,cl_26606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4674 v h) (hints_cons _ _ _ (der_26606 v h) (by intro d hd; cases hd)))
def cl_26665 : CNF.NClause := [(36,false),(5,false),(83,false),(84,false),(85,false),(86,false),(92,true)]
theorem der_26665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26665 :=
  CNF.rup_sound cl_26665 [cl_4675,cl_4673] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4675 v h) (hints_cons _ _ _ (inp_4673 v h) (by intro d hd; cases hd)))
def cl_26666 : CNF.NClause := [(36,false),(82,true),(5,true),(85,false),(83,false),(84,false),(86,false)]
theorem der_26666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26666 :=
  CNF.rup_sound cl_26666 [cl_4676,cl_26613] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4676 v h) (hints_cons _ _ _ (der_26613 v h) (by intro d hd; cases hd)))
def cl_26667 : CNF.NClause := [(36,false),(5,false),(82,false),(84,false),(85,false),(86,false),(92,true)]
theorem der_26667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26667 :=
  CNF.rup_sound cl_26667 [cl_4677,cl_4673] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4677 v h) (hints_cons _ _ _ (inp_4673 v h) (by intro d hd; cases hd)))
def cl_26668 : CNF.NClause := [(36,false),(83,true),(5,true),(82,false),(84,false),(85,false),(86,false)]
theorem der_26668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26668 :=
  CNF.rup_sound cl_26668 [cl_4678,cl_26615] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4678 v h) (hints_cons _ _ _ (der_26615 v h) (by intro d hd; cases hd)))
def cl_26669 : CNF.NClause := [(36,false),(82,true),(5,false),(83,true),(84,false),(85,false),(86,false)]
theorem der_26669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26669 :=
  CNF.rup_sound cl_26669 [cl_4679,cl_26609] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4679 v h) (hints_cons _ _ _ (der_26609 v h) (by intro d hd; cases hd)))
def cl_26670 : CNF.NClause := [(36,false),(83,true),(5,true),(82,true),(84,false),(85,false),(86,false)]
theorem der_26670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26670 :=
  CNF.rup_sound cl_26670 [cl_4680,cl_26639] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4680 v h) (hints_cons _ _ _ (der_26639 v h) (by intro d hd; cases hd)))
def cl_26671 : CNF.NClause := [(36,false),(5,false),(92,true),(86,false),(82,false),(83,false),(85,false)]
theorem der_26671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26671 :=
  CNF.rup_sound cl_26671 [cl_4681,cl_26665] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4681 v h) (hints_cons _ _ _ (der_26665 v h) (by intro d hd; cases hd)))
def cl_26672 : CNF.NClause := [(36,false),(5,true),(82,false),(85,false),(83,false),(86,false),(92,true)]
theorem der_26672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26672 :=
  CNF.rup_sound cl_26672 [cl_4682,cl_26664] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4682 v h) (hints_cons _ _ _ (der_26664 v h) (by intro d hd; cases hd)))
def cl_26673 : CNF.NClause := [(36,false),(82,true),(5,false),(83,false),(84,true),(85,false),(86,false)]
theorem der_26673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26673 :=
  CNF.rup_sound cl_26673 [cl_4683,cl_26612] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4683 v h) (hints_cons _ _ _ (der_26612 v h) (by intro d hd; cases hd)))
def cl_26674 : CNF.NClause := [(36,false),(82,true),(85,false),(92,true),(83,false),(84,true),(86,false)]
theorem der_26674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26674 :=
  CNF.rup_sound cl_26674 [cl_4684,cl_26673] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4684 v h) (hints_cons _ _ _ (der_26673 v h) (by intro d hd; cases hd)))
def cl_26675 : CNF.NClause := [(36,false),(83,true),(5,false),(82,false),(84,true),(85,false),(86,false)]
theorem der_26675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26675 :=
  CNF.rup_sound cl_26675 [cl_4685,cl_26614] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4685 v h) (hints_cons _ _ _ (der_26614 v h) (by intro d hd; cases hd)))
def cl_26676 : CNF.NClause := [(36,false),(83,true),(5,true),(82,false),(84,true),(85,false),(86,false)]
theorem der_26676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26676 :=
  CNF.rup_sound cl_26676 [cl_4686,cl_26630] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4686 v h) (hints_cons _ _ _ (der_26630 v h) (by intro d hd; cases hd)))
def cl_26677 : CNF.NClause := [(36,false),(82,true),(5,false),(84,true),(85,false),(86,false),(92,true)]
theorem der_26677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26677 :=
  CNF.rup_sound cl_26677 [cl_4687,cl_26673] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4687 v h) (hints_cons _ _ _ (der_26673 v h) (by intro d hd; cases hd)))
def cl_26678 : CNF.NClause := [(36,false),(83,true),(5,true),(82,true),(85,false),(86,false),(92,true)]
theorem der_26678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26678 :=
  CNF.rup_sound cl_26678 [cl_4688,cl_26670] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4688 v h) (hints_cons _ _ _ (der_26670 v h) (by intro d hd; cases hd)))
def cl_26679 : CNF.NClause := [(36,false),(92,true),(5,false),(82,false),(83,false),(84,false),(86,false)]
theorem der_26679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26679 :=
  CNF.rup_sound cl_26679 [cl_4689,cl_26665] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4689 v h) (hints_cons _ _ _ (der_26665 v h) (by intro d hd; cases hd)))
def cl_26680 : CNF.NClause := [(36,false),(85,true),(5,true),(83,false),(86,false),(82,false),(84,false)]
theorem der_26680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26680 :=
  CNF.rup_sound cl_26680 [cl_4690,cl_26649] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4690 v h) (hints_cons _ _ _ (der_26649 v h) (by intro d hd; cases hd)))
def cl_26681 : CNF.NClause := [(36,false),(82,true),(5,false),(83,false),(84,false),(85,true),(86,false)]
theorem der_26681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26681 :=
  CNF.rup_sound cl_26681 [cl_4691,cl_26619] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4691 v h) (hints_cons _ _ _ (der_26619 v h) (by intro d hd; cases hd)))
def cl_26682 : CNF.NClause := [(36,false),(82,true),(5,true),(86,false),(83,false),(84,false),(85,true)]
theorem der_26682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26682 :=
  CNF.rup_sound cl_26682 [cl_4692,cl_26620] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4692 v h) (hints_cons _ _ _ (der_26620 v h) (by intro d hd; cases hd)))
def cl_26683 : CNF.NClause := [(36,false),(83,true),(5,false),(82,false),(84,false),(85,true),(86,false)]
theorem der_26683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26683 :=
  CNF.rup_sound cl_26683 [cl_4693,cl_26621] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4693 v h) (hints_cons _ _ _ (der_26621 v h) (by intro d hd; cases hd)))
def cl_26684 : CNF.NClause := [(36,false),(83,true),(82,false),(84,false),(85,true),(86,false),(92,true)]
theorem der_26684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26684 :=
  CNF.rup_sound cl_26684 [cl_4694,cl_26683] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4694 v h) (hints_cons _ _ _ (der_26683 v h) (by intro d hd; cases hd)))
def cl_26685 : CNF.NClause := [(36,false),(82,true),(5,false),(83,true),(84,false),(85,true),(86,false)]
theorem der_26685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26685 :=
  CNF.rup_sound cl_26685 [cl_4695,cl_26654] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4695 v h) (hints_cons _ _ _ (der_26654 v h) (by intro d hd; cases hd)))
def cl_26686 : CNF.NClause := [(36,false),(83,true),(82,true),(84,false),(85,true),(86,false),(92,true)]
theorem der_26686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26686 :=
  CNF.rup_sound cl_26686 [cl_4696,cl_26685] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4696 v h) (hints_cons _ _ _ (der_26685 v h) (by intro d hd; cases hd)))
def cl_26687 : CNF.NClause := [(36,false),(84,true),(5,false),(82,false),(83,false),(85,true),(86,false)]
theorem der_26687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26687 :=
  CNF.rup_sound cl_26687 [cl_4697,cl_26625] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4697 v h) (hints_cons _ _ _ (der_26625 v h) (by intro d hd; cases hd)))
def cl_26688 : CNF.NClause := [(36,false),(84,true),(82,false),(86,false),(83,false),(85,true),(92,true)]
theorem der_26688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26688 :=
  CNF.rup_sound cl_26688 [cl_4698,cl_26687] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4698 v h) (hints_cons _ _ _ (der_26687 v h) (by intro d hd; cases hd)))
def cl_26689 : CNF.NClause := [(36,false),(5,false),(83,false),(84,true),(85,true),(86,false),(92,true)]
theorem der_26689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26689 :=
  CNF.rup_sound cl_26689 [cl_4699,cl_26688] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4699 v h) (hints_cons _ _ _ (der_26688 v h) (by intro d hd; cases hd)))
def cl_26690 : CNF.NClause := [(36,false),(5,true),(84,true),(83,false),(85,true),(86,false),(92,true)]
theorem der_26690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26690 :=
  CNF.rup_sound cl_26690 [cl_4700,cl_26688] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4700 v h) (hints_cons _ _ _ (der_26688 v h) (by intro d hd; cases hd)))
def cl_26691 : CNF.NClause := [(36,false),(5,false),(82,false),(84,true),(85,true),(86,false),(92,true)]
theorem der_26691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26691 :=
  CNF.rup_sound cl_26691 [cl_4701,cl_26689] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4701 v h) (hints_cons _ _ _ (der_26689 v h) (by intro d hd; cases hd)))
def cl_26692 : CNF.NClause := [(36,false),(83,true),(5,true),(82,false),(84,true),(85,true),(86,false)]
theorem der_26692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26692 :=
  CNF.rup_sound cl_26692 [cl_4702,cl_26630] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4702 v h) (hints_cons _ _ _ (der_26630 v h) (by intro d hd; cases hd)))
def cl_26693 : CNF.NClause := [(36,false),(82,true),(5,false),(83,true),(84,true),(85,true),(86,false)]
theorem der_26693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26693 :=
  CNF.rup_sound cl_26693 [cl_4703,cl_26631] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4703 v h) (hints_cons _ _ _ (der_26631 v h) (by intro d hd; cases hd)))
def cl_26694 : CNF.NClause := [(36,false),(83,true),(82,true),(84,true),(85,true),(86,false),(92,true)]
theorem der_26694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26694 :=
  CNF.rup_sound cl_26694 [cl_4704,cl_26693] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4704 v h) (hints_cons _ _ _ (der_26693 v h) (by intro d hd; cases hd)))
def cl_26695 : CNF.NClause := [(36,false),(92,true),(5,false),(82,false),(83,false),(85,false),(84,false)]
theorem der_26695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26695 :=
  CNF.rup_sound cl_26695 [cl_4705,cl_26665] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4705 v h) (hints_cons _ _ _ (der_26665 v h) (by intro d hd; cases hd)))
def cl_26696 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,false),(86,true),(85,false)]
theorem der_26696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26696 :=
  CNF.rup_sound cl_26696 [cl_4706,cl_26641] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4706 v h) (hints_cons _ _ _ (der_26641 v h) (by intro d hd; cases hd)))
def cl_26697 : CNF.NClause := [(36,false),(82,true),(5,false),(83,false),(84,false),(85,false),(86,true)]
theorem der_26697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26697 :=
  CNF.rup_sound cl_26697 [cl_4707,cl_26634] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4707 v h) (hints_cons _ _ _ (der_26634 v h) (by intro d hd; cases hd)))
def cl_26698 : CNF.NClause := [(36,false),(82,true),(5,true),(83,false),(85,false),(84,false),(92,true)]
theorem der_26698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26698 :=
  CNF.rup_sound cl_26698 [cl_4708,cl_26666] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4708 v h) (hints_cons _ _ _ (der_26666 v h) (by intro d hd; cases hd)))
def cl_26699 : CNF.NClause := [(36,false),(83,true),(5,false),(82,false),(84,false),(85,false),(86,true)]
theorem der_26699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26699 :=
  CNF.rup_sound cl_26699 [cl_4709,cl_26636] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4709 v h) (hints_cons _ _ _ (der_26636 v h) (by intro d hd; cases hd)))
def cl_26700 : CNF.NClause := [(36,false),(83,true),(5,true),(82,false),(84,false),(85,false),(86,true)]
theorem der_26700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26700 :=
  CNF.rup_sound cl_26700 [cl_4710,cl_26653] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4710 v h) (hints_cons _ _ _ (der_26653 v h) (by intro d hd; cases hd)))
def cl_26701 : CNF.NClause := [(36,false),(82,true),(5,false),(84,false),(85,false),(86,true),(92,true)]
theorem der_26701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26701 :=
  CNF.rup_sound cl_26701 [cl_4711,cl_26697] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4711 v h) (hints_cons _ _ _ (der_26697 v h) (by intro d hd; cases hd)))
def cl_26702 : CNF.NClause := [(36,false),(83,true),(5,true),(84,false),(85,false),(86,true),(92,true)]
theorem der_26702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26702 :=
  CNF.rup_sound cl_26702 [cl_4712,cl_26700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4712 v h) (hints_cons _ _ _ (der_26700 v h) (by intro d hd; cases hd)))
def cl_26703 : CNF.NClause := [(36,false),(84,true),(5,false),(82,false),(83,false),(85,false),(86,true)]
theorem der_26703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26703 :=
  CNF.rup_sound cl_26703 [cl_4713,cl_26656] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4713 v h) (hints_cons _ _ _ (der_26656 v h) (by intro d hd; cases hd)))
def cl_26704 : CNF.NClause := [(36,false),(5,true),(82,false),(84,true),(85,false),(83,false),(86,true)]
theorem der_26704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26704 :=
  CNF.rup_sound cl_26704 [cl_4714,cl_26641] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4714 v h) (hints_cons _ _ _ (der_26641 v h) (by intro d hd; cases hd)))
def cl_26705 : CNF.NClause := [(36,false),(82,true),(5,false),(83,false),(84,true),(85,false),(92,true)]
theorem der_26705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26705 :=
  CNF.rup_sound cl_26705 [cl_4715,cl_26673] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4715 v h) (hints_cons _ _ _ (der_26673 v h) (by intro d hd; cases hd)))
def cl_26706 : CNF.NClause := [(36,false),(84,true),(5,true),(82,true),(83,false),(85,false),(86,true)]
theorem der_26706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26706 :=
  CNF.rup_sound cl_26706 [cl_4716,cl_26643] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4716 v h) (hints_cons _ _ _ (der_26643 v h) (by intro d hd; cases hd)))
def cl_26707 : CNF.NClause := [(36,false),(83,true),(5,false),(82,false),(84,true),(85,false),(86,true)]
theorem der_26707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26707 :=
  CNF.rup_sound cl_26707 [cl_4717,cl_26645] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4717 v h) (hints_cons _ _ _ (der_26645 v h) (by intro d hd; cases hd)))
def cl_26708 : CNF.NClause := [(36,false),(83,true),(5,true),(82,false),(84,true),(85,false),(86,true)]
theorem der_26708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26708 :=
  CNF.rup_sound cl_26708 [cl_4718,cl_26645] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4718 v h) (hints_cons _ _ _ (der_26645 v h) (by intro d hd; cases hd)))
def cl_26709 : CNF.NClause := [(36,false),(82,true),(5,false),(83,true),(85,false),(86,true),(92,true)]
theorem der_26709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26709 :=
  CNF.rup_sound cl_26709 [cl_4719,cl_26701] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4719 v h) (hints_cons _ _ _ (der_26701 v h) (by intro d hd; cases hd)))
def cl_26710 : CNF.NClause := [(36,false),(83,true),(5,true),(84,true),(85,false),(86,true),(92,true)]
theorem der_26710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26710 :=
  CNF.rup_sound cl_26710 [cl_4720,cl_26708] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4720 v h) (hints_cons _ _ _ (der_26708 v h) (by intro d hd; cases hd)))
def cl_26711 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(86,true),(84,false),(92,true)]
theorem der_26711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26711 :=
  CNF.rup_sound cl_26711 [cl_4721,cl_26695] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4721 v h) (hints_cons _ _ _ (der_26695 v h) (by intro d hd; cases hd)))
def cl_26712 : CNF.NClause := [(36,false),(92,true),(82,false),(83,false),(85,true),(84,false),(86,true)]
theorem der_26712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26712 :=
  CNF.rup_sound cl_26712 [cl_4722,cl_26711] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4722 v h) (hints_cons _ _ _ (der_26711 v h) (by intro d hd; cases hd)))
def cl_26713 : CNF.NClause := [(36,false),(82,true),(5,false),(83,false),(84,false),(86,true),(92,true)]
theorem der_26713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26713 :=
  CNF.rup_sound cl_26713 [cl_4723,cl_26701] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4723 v h) (hints_cons _ _ _ (der_26701 v h) (by intro d hd; cases hd)))
def cl_26714 : CNF.NClause := [(36,false),(82,true),(5,true),(86,true),(83,false),(84,false),(92,true)]
theorem der_26714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26714 :=
  CNF.rup_sound cl_26714 [cl_4724,cl_26698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4724 v h) (hints_cons _ _ _ (der_26698 v h) (by intro d hd; cases hd)))
def cl_26715 : CNF.NClause := [(36,false),(83,true),(5,false),(82,false),(84,false),(85,true),(92,true)]
theorem der_26715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26715 :=
  CNF.rup_sound cl_26715 [cl_4725,cl_26683] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4725 v h) (hints_cons _ _ _ (der_26683 v h) (by intro d hd; cases hd)))
def cl_26716 : CNF.NClause := [(36,false),(83,true),(5,true),(82,false),(84,false),(85,true),(86,true)]
theorem der_26716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26716 :=
  CNF.rup_sound cl_26716 [cl_4726,cl_26653] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4726 v h) (hints_cons _ _ _ (der_26653 v h) (by intro d hd; cases hd)))
def cl_26717 : CNF.NClause := [(36,false),(5,false),(83,true),(84,false),(85,true),(86,true),(92,true)]
theorem der_26717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26717 :=
  CNF.rup_sound cl_26717 [cl_4727,cl_26715] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4727 v h) (hints_cons _ _ _ (der_26715 v h) (by intro d hd; cases hd)))
def cl_26718 : CNF.NClause := [(36,false),(83,true),(5,true),(82,true),(84,false),(85,true),(86,true)]
theorem der_26718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26718 :=
  CNF.rup_sound cl_26718 [cl_4728,cl_26655] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4728 v h) (hints_cons _ _ _ (der_26655 v h) (by intro d hd; cases hd)))
def cl_26719 : CNF.NClause := [(36,false),(84,true),(5,false),(82,false),(83,false),(85,true),(86,true)]
theorem der_26719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26719 :=
  CNF.rup_sound cl_26719 [cl_4729,cl_26656] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4729 v h) (hints_cons _ _ _ (der_26656 v h) (by intro d hd; cases hd)))
def cl_26720 : CNF.NClause := [(36,false),(92,true),(5,true),(82,false),(84,true),(85,true),(83,false)]
theorem der_26720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26720 :=
  CNF.rup_sound cl_26720 [cl_4730,cl_26690] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4730 v h) (hints_cons _ _ _ (der_26690 v h) (by intro d hd; cases hd)))
def cl_26721 : CNF.NClause := [(36,false),(82,true),(5,false),(83,false),(84,true),(85,true),(86,true)]
theorem der_26721 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26721 :=
  CNF.rup_sound cl_26721 [cl_4731,cl_26658] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4731 v h) (hints_cons _ _ _ (der_26658 v h) (by intro d hd; cases hd)))
def cl_26722 : CNF.NClause := [(36,false),(84,true),(82,true),(83,false),(85,true),(86,true),(92,true)]
theorem der_26722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26722 :=
  CNF.rup_sound cl_26722 [cl_4732,cl_26721] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4732 v h) (hints_cons _ _ _ (der_26721 v h) (by intro d hd; cases hd)))
def cl_26724 : CNF.NClause := [(36,false),(83,true),(5,true),(82,false),(84,true),(86,true),(92,true)]
theorem der_26724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26724 :=
  CNF.rup_sound cl_26724 [cl_4734,cl_26708] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4734 v h) (hints_cons _ _ _ (der_26708 v h) (by intro d hd; cases hd)))
def cl_26726 : CNF.NClause := [(36,false),(83,true),(5,true),(82,true),(84,true),(86,true),(92,true)]
theorem der_26726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26726 :=
  CNF.rup_sound cl_26726 [cl_4736,cl_26710] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4736 v h) (hints_cons _ _ _ (der_26710 v h) (by intro d hd; cases hd)))
def cl_26727 : CNF.NClause := [(49,false),(69,false),(18,true),(77,false),(65,false),(86,false),(73,false)]
theorem der_26727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26727 :=
  CNF.rup_sound cl_26727 [cl_6274,cl_6338] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6274 v h) (hints_cons _ _ _ (inp_6338 v h) (by intro d hd; cases hd)))
def cl_26728 : CNF.NClause := [(49,false),(77,true),(18,false),(65,false),(73,false),(86,false),(69,false)]
theorem der_26728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26728 :=
  CNF.rup_sound cl_26728 [cl_6289,cl_26319] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6289 v h) (hints_cons _ _ _ (der_26319 v h) (by intro d hd; cases hd)))
def cl_26729 : CNF.NClause := [(49,false),(18,true),(65,false),(77,true),(73,false),(86,false),(69,false)]
theorem der_26729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26729 :=
  CNF.rup_sound cl_26729 [cl_6290,cl_26319] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6290 v h) (hints_cons _ _ _ (der_26319 v h) (by intro d hd; cases hd)))
def cl_26730 : CNF.NClause := [(57,false),(26,true),(79,false),(83,false),(91,false),(62,true),(71,false)]
theorem der_26730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26730 :=
  CNF.rup_sound cl_26730 [cl_7308,cl_7300] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7308 v h) (hints_cons _ _ _ (inp_7300 v h) (by intro d hd; cases hd)))
def cl_26731 : CNF.NClause := [(57,false),(26,true),(71,false),(75,false),(62,true),(83,false),(91,false)]
theorem der_26731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26731 :=
  CNF.rup_sound cl_26731 [cl_7316,cl_7300] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7316 v h) (hints_cons _ _ _ (inp_7300 v h) (by intro d hd; cases hd)))
def cl_26732 : CNF.NClause := [(57,false),(26,true),(71,false),(62,true),(75,true),(83,false),(91,false)]
theorem der_26732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26732 :=
  CNF.rup_sound cl_26732 [cl_7324,cl_26730] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7324 v h) (hints_cons _ _ _ (der_26730 v h) (by intro d hd; cases hd)))
def cl_26733 : CNF.NClause := [(57,false),(26,true),(71,false),(75,false),(79,false),(62,true),(91,false)]
theorem der_26733 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26733 :=
  CNF.rup_sound cl_26733 [cl_7332,cl_7300] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7332 v h) (hints_cons _ _ _ (inp_7300 v h) (by intro d hd; cases hd)))
def cl_26734 : CNF.NClause := [(57,false),(26,true),(71,false),(62,true),(75,true),(79,false),(91,false)]
theorem der_26734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26734 :=
  CNF.rup_sound cl_26734 [cl_7340,cl_26732] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7340 v h) (hints_cons _ _ _ (der_26732 v h) (by intro d hd; cases hd)))
def cl_26735 : CNF.NClause := [(57,false),(79,true),(26,true),(71,false),(75,false),(62,true),(91,false)]
theorem der_26735 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26735 :=
  CNF.rup_sound cl_26735 [cl_7348,cl_26731] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7348 v h) (hints_cons _ _ _ (der_26731 v h) (by intro d hd; cases hd)))
def cl_26736 : CNF.NClause := [(57,false),(79,true),(26,true),(71,false),(62,true),(75,true),(91,false)]
theorem der_26736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26736 :=
  CNF.rup_sound cl_26736 [cl_7356,cl_26732] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7356 v h) (hints_cons _ _ _ (der_26732 v h) (by intro d hd; cases hd)))
def cl_26737 : CNF.NClause := [(57,false),(71,false),(26,true),(62,true),(75,false),(83,false),(79,false)]
theorem der_26737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26737 :=
  CNF.rup_sound cl_26737 [cl_7364,cl_7300] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7364 v h) (hints_cons _ _ _ (inp_7300 v h) (by intro d hd; cases hd)))
def cl_26738 : CNF.NClause := [(57,false),(75,true),(26,true),(71,false),(62,true),(79,false),(83,false)]
theorem der_26738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26738 :=
  CNF.rup_sound cl_26738 [cl_7372,cl_26732] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7372 v h) (hints_cons _ _ _ (der_26732 v h) (by intro d hd; cases hd)))
def cl_26739 : CNF.NClause := [(57,false),(26,true),(71,false),(75,false),(62,true),(83,false),(91,true)]
theorem der_26739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26739 :=
  CNF.rup_sound cl_26739 [cl_7380,cl_26737] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7380 v h) (hints_cons _ _ _ (der_26737 v h) (by intro d hd; cases hd)))
def cl_26740 : CNF.NClause := [(57,false),(79,true),(26,true),(71,false),(62,true),(75,true),(83,false)]
theorem der_26740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26740 :=
  CNF.rup_sound cl_26740 [cl_7388,cl_26732] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7388 v h) (hints_cons _ _ _ (der_26732 v h) (by intro d hd; cases hd)))
def cl_26741 : CNF.NClause := [(57,false),(26,true),(71,false),(75,false),(79,false),(62,true),(91,true)]
theorem der_26741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26741 :=
  CNF.rup_sound cl_26741 [cl_7396,cl_26737] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7396 v h) (hints_cons _ _ _ (der_26737 v h) (by intro d hd; cases hd)))
def cl_26742 : CNF.NClause := [(57,false),(83,true),(26,true),(71,false),(62,true),(79,false),(75,true)]
theorem der_26742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26742 :=
  CNF.rup_sound cl_26742 [cl_7404,cl_26734] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7404 v h) (hints_cons _ _ _ (der_26734 v h) (by intro d hd; cases hd)))
def cl_26743 : CNF.NClause := [(57,false),(79,true),(26,true),(71,false),(75,false),(62,true),(83,true)]
theorem der_26743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26743 :=
  CNF.rup_sound cl_26743 [cl_7412,cl_26735] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7412 v h) (hints_cons _ _ _ (der_26735 v h) (by intro d hd; cases hd)))
def cl_26744 : CNF.NClause := [(57,false),(79,true),(26,true),(71,false),(62,true),(75,true),(91,true)]
theorem der_26744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26744 :=
  CNF.rup_sound cl_26744 [cl_7420,cl_26740] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7420 v h) (hints_cons _ _ _ (der_26740 v h) (by intro d hd; cases hd)))
def cl_26745 : CNF.NClause := [(44,false),(78,true),(65,false),(13,true),(72,false),(71,false),(88,false)]
theorem der_26745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26745 :=
  CNF.rup_sound cl_26745 [cl_5682,cl_5650] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5682 v h) (hints_cons _ _ _ (inp_5650 v h) (by intro d hd; cases hd)))
def cl_26746 : CNF.NClause := [(44,false),(78,true),(65,false),(13,true),(72,false),(71,false),(84,false)]
theorem der_26746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26746 :=
  CNF.rup_sound cl_26746 [cl_5714,cl_5650] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5714 v h) (hints_cons _ _ _ (inp_5650 v h) (by intro d hd; cases hd)))
def cl_26747 : CNF.NClause := [(44,false),(65,false),(13,true),(72,false),(78,false),(71,false),(84,true)]
theorem der_26747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26747 :=
  CNF.rup_sound cl_26747 [cl_5730,cl_5666] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5730 v h) (hints_cons _ _ _ (inp_5666 v h) (by intro d hd; cases hd)))
def cl_26748 : CNF.NClause := [(44,false),(78,true),(65,false),(13,true),(72,false),(71,false),(88,true)]
theorem der_26748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26748 :=
  CNF.rup_sound cl_26748 [cl_5746,cl_26746] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5746 v h) (hints_cons _ _ _ (der_26746 v h) (by intro d hd; cases hd)))
def cl_26749 : CNF.NClause := [(50,false),(19,true),(85,false),(63,false),(71,false),(77,false),(90,false)]
theorem der_26749 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26749 :=
  CNF.rup_sound cl_26749 [cl_6410,cl_6402] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6410 v h) (hints_cons _ _ _ (inp_6402 v h) (by intro d hd; cases hd)))
def cl_26750 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(85,false),(77,true),(90,false)]
theorem der_26750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26750 :=
  CNF.rup_sound cl_26750 [cl_6426,cl_26320] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6426 v h) (hints_cons _ _ _ (der_26320 v h) (by intro d hd; cases hd)))
def cl_26751 : CNF.NClause := [(50,false),(74,true),(19,true),(63,false),(77,false),(71,false),(90,false)]
theorem der_26751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26751 :=
  CNF.rup_sound cl_26751 [cl_6442,cl_26749] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6442 v h) (hints_cons _ _ _ (der_26749 v h) (by intro d hd; cases hd)))
def cl_26752 : CNF.NClause := [(50,false),(19,true),(63,false),(71,false),(74,true),(77,true),(90,false)]
theorem der_26752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26752 :=
  CNF.rup_sound cl_26752 [cl_6458,cl_26750] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6458 v h) (hints_cons _ _ _ (der_26750 v h) (by intro d hd; cases hd)))
def cl_26753 : CNF.NClause := [(50,false),(19,true),(74,false),(71,false),(63,false),(77,false),(85,false)]
theorem der_26753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26753 :=
  CNF.rup_sound cl_26753 [cl_6466,cl_6402] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6466 v h) (hints_cons _ _ _ (inp_6402 v h) (by intro d hd; cases hd)))
def cl_26754 : CNF.NClause := [(50,false),(74,true),(19,true),(71,false),(77,false),(85,false),(63,false)]
theorem der_26754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26754 :=
  CNF.rup_sound cl_26754 [cl_6474,cl_26751] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6474 v h) (hints_cons _ _ _ (der_26751 v h) (by intro d hd; cases hd)))
def cl_26755 : CNF.NClause := [(50,false),(19,true),(63,false),(85,false),(74,false),(90,true),(71,false)]
theorem der_26755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26755 :=
  CNF.rup_sound cl_26755 [cl_6482,cl_26753] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6482 v h) (hints_cons _ _ _ (der_26753 v h) (by intro d hd; cases hd)))
def cl_26756 : CNF.NClause := [(50,false),(74,true),(19,true),(63,false),(71,false),(77,true),(85,false)]
theorem der_26756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26756 :=
  CNF.rup_sound cl_26756 [cl_6490,cl_26750] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6490 v h) (hints_cons _ _ _ (der_26750 v h) (by intro d hd; cases hd)))
def cl_26757 : CNF.NClause := [(50,false),(74,true),(19,true),(63,false),(85,true),(77,false),(71,false)]
theorem der_26757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26757 :=
  CNF.rup_sound cl_26757 [cl_6506,cl_26751] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6506 v h) (hints_cons _ _ _ (der_26751 v h) (by intro d hd; cases hd)))
def cl_26758 : CNF.NClause := [(50,false),(85,true),(19,true),(63,false),(71,false),(74,true),(77,true)]
theorem der_26758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26758 :=
  CNF.rup_sound cl_26758 [cl_6522,cl_26752] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6522 v h) (hints_cons _ _ _ (der_26752 v h) (by intro d hd; cases hd)))
def cl_26759 : CNF.NClause := [(48,false),(70,false),(17,true),(76,false),(88,false),(64,false),(77,false)]
theorem der_26759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26759 :=
  CNF.rup_sound cl_26759 [cl_6146,cl_6178] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6146 v h) (hints_cons _ _ _ (inp_6178 v h) (by intro d hd; cases hd)))
def cl_26760 : CNF.NClause := [(48,false),(77,true),(17,true),(70,false),(83,false),(64,false),(88,false)]
theorem der_26760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26760 :=
  CNF.rup_sound cl_26760 [cl_6162,cl_26344] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6162 v h) (hints_cons _ _ _ (der_26344 v h) (by intro d hd; cases hd)))
def cl_26761 : CNF.NClause := [(44,false),(88,false),(13,true),(71,false),(84,false),(65,false),(72,false)]
theorem der_26761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26761 :=
  CNF.rup_sound cl_26761 [cl_5634,cl_26745] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5634 v h) (hints_cons _ _ _ (der_26745 v h) (by intro d hd; cases hd)))
def cl_26762 : CNF.NClause := [(52,false),(21,true),(79,false),(73,false),(88,false),(85,false),(66,false)]
theorem der_26762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26762 :=
  CNF.rup_sound cl_26762 [cl_6658,cl_26350] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6658 v h) (hints_cons _ _ _ (der_26350 v h) (by intro d hd; cases hd)))
def cl_26763 : CNF.NClause := [(47,false),(77,true),(66,false),(75,false),(89,false),(68,false),(84,false)]
theorem der_26763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26763 :=
  CNF.rup_sound cl_26763 [cl_6033,cl_26365] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6033 v h) (hints_cons _ _ _ (der_26365 v h) (by intro d hd; cases hd)))
def cl_26764 : CNF.NClause := [(45,false),(70,false),(14,true),(89,false),(63,false),(79,false),(72,false)]
theorem der_26764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26764 :=
  CNF.rup_sound cl_26764 [cl_5794,cl_5762] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5794 v h) (hints_cons _ _ _ (inp_5762 v h) (by intro d hd; cases hd)))
def cl_26765 : CNF.NClause := [(45,false),(70,false),(14,true),(63,false),(79,false),(72,false),(86,true)]
theorem der_26765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26765 :=
  CNF.rup_sound cl_26765 [cl_5858,cl_26764] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5858 v h) (hints_cons _ _ _ (der_26764 v h) (by intro d hd; cases hd)))
def cl_26766 : CNF.NClause := [(53,false),(22,true),(90,false),(78,false),(64,false),(67,false),(86,false)]
theorem der_26766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26766 :=
  CNF.rup_sound cl_26766 [cl_6794,cl_6786] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6794 v h) (hints_cons _ _ _ (inp_6786 v h) (by intro d hd; cases hd)))
def cl_26767 : CNF.NClause := [(53,false),(22,true),(64,false),(90,false),(67,false),(86,false),(75,false)]
theorem der_26767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26767 :=
  CNF.rup_sound cl_26767 [cl_6802,cl_6786] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6802 v h) (hints_cons _ _ _ (inp_6786 v h) (by intro d hd; cases hd)))
def cl_26768 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,true),(86,false),(90,false)]
theorem der_26768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26768 :=
  CNF.rup_sound cl_26768 [cl_6810,cl_26766] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6810 v h) (hints_cons _ _ _ (der_26766 v h) (by intro d hd; cases hd)))
def cl_26769 : CNF.NClause := [(53,false),(22,true),(64,false),(75,false),(78,false),(67,false),(90,false)]
theorem der_26769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26769 :=
  CNF.rup_sound cl_26769 [cl_6818,cl_6786] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6818 v h) (hints_cons _ _ _ (inp_6786 v h) (by intro d hd; cases hd)))
def cl_26770 : CNF.NClause := [(53,false),(75,true),(22,true),(64,false),(67,false),(78,false),(90,false)]
theorem der_26770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26770 :=
  CNF.rup_sound cl_26770 [cl_6826,cl_26768] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6826 v h) (hints_cons _ _ _ (der_26768 v h) (by intro d hd; cases hd)))
def cl_26771 : CNF.NClause := [(53,false),(78,true),(22,true),(64,false),(75,false),(67,false),(90,false)]
theorem der_26771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26771 :=
  CNF.rup_sound cl_26771 [cl_6834,cl_26767] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6834 v h) (hints_cons _ _ _ (der_26767 v h) (by intro d hd; cases hd)))
def cl_26772 : CNF.NClause := [(53,false),(78,true),(22,true),(64,false),(67,false),(75,true),(90,false)]
theorem der_26772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26772 :=
  CNF.rup_sound cl_26772 [cl_6842,cl_26768] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6842 v h) (hints_cons _ _ _ (der_26768 v h) (by intro d hd; cases hd)))
def cl_26773 : CNF.NClause := [(53,false),(22,true),(78,false),(67,false),(86,false),(75,false),(64,false)]
theorem der_26773 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26773 :=
  CNF.rup_sound cl_26773 [cl_6850,cl_6786] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6850 v h) (hints_cons _ _ _ (inp_6786 v h) (by intro d hd; cases hd)))
def cl_26774 : CNF.NClause := [(53,false),(75,true),(22,true),(64,false),(67,false),(86,false),(78,false)]
theorem der_26774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26774 :=
  CNF.rup_sound cl_26774 [cl_6858,cl_26768] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6858 v h) (hints_cons _ _ _ (der_26768 v h) (by intro d hd; cases hd)))
def cl_26775 : CNF.NClause := [(53,false),(78,true),(22,true),(64,false),(75,false),(67,false),(86,false)]
theorem der_26775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26775 :=
  CNF.rup_sound cl_26775 [cl_6866,cl_26767] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6866 v h) (hints_cons _ _ _ (der_26767 v h) (by intro d hd; cases hd)))
def cl_26776 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,true),(86,false),(90,true)]
theorem der_26776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26776 :=
  CNF.rup_sound cl_26776 [cl_6874,cl_26774] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6874 v h) (hints_cons _ _ _ (der_26774 v h) (by intro d hd; cases hd)))
def cl_26777 : CNF.NClause := [(53,false),(22,true),(64,false),(75,false),(67,false),(86,true),(78,false)]
theorem der_26777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26777 :=
  CNF.rup_sound cl_26777 [cl_6882,cl_26769] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6882 v h) (hints_cons _ _ _ (der_26769 v h) (by intro d hd; cases hd)))
def cl_26778 : CNF.NClause := [(53,false),(90,true),(22,true),(64,false),(67,false),(75,true),(78,false)]
theorem der_26778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26778 :=
  CNF.rup_sound cl_26778 [cl_6890,cl_26774] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6890 v h) (hints_cons _ _ _ (der_26774 v h) (by intro d hd; cases hd)))
def cl_26779 : CNF.NClause := [(53,false),(78,true),(22,true),(64,false),(75,false),(67,false),(90,true)]
theorem der_26779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26779 :=
  CNF.rup_sound cl_26779 [cl_6898,cl_26775] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6898 v h) (hints_cons _ _ _ (der_26775 v h) (by intro d hd; cases hd)))
def cl_26780 : CNF.NClause := [(53,false),(78,true),(22,true),(64,false),(67,false),(86,true),(90,true)]
theorem der_26780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26780 :=
  CNF.rup_sound cl_26780 [cl_6906,cl_26779] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6906 v h) (hints_cons _ _ _ (der_26779 v h) (by intro d hd; cases hd)))
def cl_26781 : CNF.NClause := [(40,false),(9,true),(63,false),(75,false),(81,false),(82,false),(88,false)]
theorem der_26781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26781 :=
  CNF.rup_sound cl_26781 [cl_5126,cl_5122] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5126 v h) (hints_cons _ _ _ (inp_5122 v h) (by intro d hd; cases hd)))
def cl_26782 : CNF.NClause := [(40,false),(9,true),(63,false),(81,false),(69,false),(82,false),(88,false)]
theorem der_26782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26782 :=
  CNF.rup_sound cl_26782 [cl_5130,cl_5122] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5130 v h) (hints_cons _ _ _ (inp_5122 v h) (by intro d hd; cases hd)))
def cl_26783 : CNF.NClause := [(40,false),(9,true),(63,false),(75,true),(81,false),(82,false),(88,false)]
theorem der_26783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26783 :=
  CNF.rup_sound cl_26783 [cl_5134,cl_26782] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5134 v h) (hints_cons _ _ _ (der_26782 v h) (by intro d hd; cases hd)))
def cl_26784 : CNF.NClause := [(40,false),(9,true),(82,false),(69,false),(75,false),(63,false),(88,false)]
theorem der_26784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26784 :=
  CNF.rup_sound cl_26784 [cl_5138,cl_26782] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5138 v h) (hints_cons _ _ _ (der_26782 v h) (by intro d hd; cases hd)))
def cl_26785 : CNF.NClause := [(40,false),(9,true),(63,false),(75,false),(81,true),(82,false),(88,false)]
theorem der_26785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26785 :=
  CNF.rup_sound cl_26785 [cl_5142,cl_26784] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5142 v h) (hints_cons _ _ _ (der_26784 v h) (by intro d hd; cases hd)))
def cl_26786 : CNF.NClause := [(40,false),(9,true),(69,false),(63,false),(75,true),(82,false),(88,false)]
theorem der_26786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26786 :=
  CNF.rup_sound cl_26786 [cl_5146,cl_26783] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5146 v h) (hints_cons _ _ _ (der_26783 v h) (by intro d hd; cases hd)))
def chunk008 : List CNF.NClause := [cl_26275,cl_26276,cl_26277,cl_26278,cl_26279,cl_26280,cl_26281,cl_26282,cl_26283,cl_26284,cl_26285,cl_26286,cl_26287,cl_26288,cl_26289,cl_26290,cl_26291,cl_26292,cl_26293,cl_26294,cl_26295,cl_26296,cl_26297,cl_26298,cl_26299,cl_26300,cl_26301,cl_26302,cl_26303,cl_26304,cl_26305,cl_26306,cl_26307,cl_26308,cl_26309,cl_26310,cl_26311,cl_26312,cl_26313,cl_26314,cl_26315,cl_26316,cl_26317,cl_26318,cl_26319,cl_26320,cl_26321,cl_26322,cl_26323,cl_26324,cl_26325,cl_26326,cl_26327,cl_26328,cl_26329,cl_26330,cl_26331,cl_26332,cl_26333,cl_26334,cl_26335,cl_26336,cl_26337,cl_26338,cl_26339,cl_26340,cl_26341,cl_26342,cl_26343,cl_26344,cl_26345,cl_26346,cl_26347,cl_26348,cl_26349,cl_26350,cl_26351,cl_26352,cl_26353,cl_26354,cl_26355,cl_26356,cl_26357,cl_26358,cl_26359,cl_26360,cl_26361,cl_26362,cl_26363,cl_26364,cl_26365,cl_26366,cl_26367,cl_26368,cl_26369,cl_26370,cl_26371,cl_26372,cl_26373,cl_26374,cl_26375,cl_26376,cl_26377,cl_26378,cl_26379,cl_26380,cl_26381,cl_26382,cl_26383,cl_26384,cl_26385,cl_26386,cl_26387,cl_26388,cl_26389,cl_26390,cl_26391,cl_26392,cl_26393,cl_26394,cl_26395,cl_26396,cl_26397,cl_26398,cl_26399,cl_26400,cl_26401,cl_26402,cl_26403,cl_26404,cl_26405,cl_26406,cl_26407,cl_26408,cl_26409,cl_26410,cl_26411,cl_26412,cl_26414,cl_26415,cl_26416,cl_26417,cl_26418,cl_26419,cl_26420,cl_26421,cl_26422,cl_26423,cl_26424,cl_26425,cl_26426,cl_26427,cl_26428,cl_26429,cl_26430,cl_26431,cl_26432,cl_26433,cl_26434,cl_26435,cl_26436,cl_26437,cl_26438,cl_26439,cl_26440,cl_26441,cl_26442,cl_26443,cl_26445,cl_26446,cl_26447,cl_26448,cl_26449,cl_26450,cl_26451,cl_26453,cl_26454,cl_26455,cl_26456,cl_26457,cl_26458,cl_26459,cl_26460,cl_26461,cl_26462,cl_26463,cl_26464,cl_26465,cl_26466,cl_26467,cl_26469,cl_26470,cl_26471,cl_26472,cl_26473,cl_26474,cl_26475,cl_26477,cl_26478,cl_26479,cl_26480,cl_26481,cl_26482,cl_26483,cl_26485,cl_26486,cl_26487,cl_26488,cl_26489,cl_26490,cl_26491,cl_26492,cl_26493,cl_26494,cl_26495,cl_26496,cl_26497,cl_26498,cl_26499,cl_26500,cl_26501,cl_26502,cl_26503,cl_26504,cl_26505,cl_26506,cl_26507,cl_26508,cl_26509,cl_26510,cl_26511,cl_26512,cl_26513,cl_26514,cl_26515,cl_26516,cl_26517,cl_26518,cl_26519,cl_26520,cl_26521,cl_26522,cl_26523,cl_26524,cl_26525,cl_26526,cl_26527,cl_26528,cl_26529,cl_26530,cl_26531,cl_26532,cl_26533,cl_26534,cl_26535,cl_26536,cl_26537,cl_26538,cl_26539,cl_26540,cl_26541,cl_26542,cl_26543,cl_26544,cl_26545,cl_26546,cl_26547,cl_26548,cl_26549,cl_26550,cl_26551,cl_26552,cl_26553,cl_26555,cl_26556,cl_26557,cl_26558,cl_26559,cl_26560,cl_26561,cl_26562,cl_26563,cl_26565,cl_26566,cl_26567,cl_26568,cl_26569,cl_26570,cl_26571,cl_26573,cl_26574,cl_26575,cl_26576,cl_26577,cl_26578,cl_26579,cl_26580,cl_26581,cl_26582,cl_26583,cl_26584,cl_26585,cl_26586,cl_26587,cl_26588,cl_26589,cl_26590,cl_26591,cl_26592,cl_26593,cl_26594,cl_26595,cl_26596,cl_26597,cl_26598,cl_26599,cl_26600,cl_26601,cl_26602,cl_26603,cl_26605,cl_26606,cl_26607,cl_26608,cl_26609,cl_26610,cl_26611,cl_26612,cl_26613,cl_26614,cl_26615,cl_26616,cl_26617,cl_26618,cl_26619,cl_26620,cl_26621,cl_26622,cl_26623,cl_26624,cl_26625,cl_26626,cl_26627,cl_26628,cl_26629,cl_26630,cl_26631,cl_26632,cl_26633,cl_26634,cl_26635,cl_26636,cl_26637,cl_26638,cl_26639,cl_26640,cl_26641,cl_26642,cl_26643,cl_26644,cl_26645,cl_26646,cl_26647,cl_26648,cl_26649,cl_26650,cl_26651,cl_26652,cl_26653,cl_26654,cl_26655,cl_26656,cl_26657,cl_26658,cl_26659,cl_26660,cl_26661,cl_26662,cl_26663,cl_26664,cl_26665,cl_26666,cl_26667,cl_26668,cl_26669,cl_26670,cl_26671,cl_26672,cl_26673,cl_26674,cl_26675,cl_26676,cl_26677,cl_26678,cl_26679,cl_26680,cl_26681,cl_26682,cl_26683,cl_26684,cl_26685,cl_26686,cl_26687,cl_26688,cl_26689,cl_26690,cl_26691,cl_26692,cl_26693,cl_26694,cl_26695,cl_26696,cl_26697,cl_26698,cl_26699,cl_26700,cl_26701,cl_26702,cl_26703,cl_26704,cl_26705,cl_26706,cl_26707,cl_26708,cl_26709,cl_26710,cl_26711,cl_26712,cl_26713,cl_26714,cl_26715,cl_26716,cl_26717,cl_26718,cl_26719,cl_26720,cl_26721,cl_26722,cl_26724,cl_26726,cl_26727,cl_26728,cl_26729,cl_26730,cl_26731,cl_26732,cl_26733,cl_26734,cl_26735,cl_26736,cl_26737,cl_26738,cl_26739,cl_26740,cl_26741,cl_26742,cl_26743,cl_26744,cl_26745,cl_26746,cl_26747,cl_26748,cl_26749,cl_26750,cl_26751,cl_26752,cl_26753,cl_26754,cl_26755,cl_26756,cl_26757,cl_26758,cl_26759,cl_26760,cl_26761,cl_26762,cl_26763,cl_26764,cl_26765,cl_26766,cl_26767,cl_26768,cl_26769,cl_26770,cl_26771,cl_26772,cl_26773,cl_26774,cl_26775,cl_26776,cl_26777,cl_26778,cl_26779,cl_26780,cl_26781,cl_26782,cl_26783,cl_26784,cl_26785,cl_26786]
theorem chunk_sound008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk008, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_26275 v h) (hints_cons _ _ _ (der_26276 v h) (hints_cons _ _ _ (der_26277 v h) (hints_cons _ _ _ (der_26278 v h) (hints_cons _ _ _ (der_26279 v h) (hints_cons _ _ _ (der_26280 v h) (hints_cons _ _ _ (der_26281 v h) (hints_cons _ _ _ (der_26282 v h) (hints_cons _ _ _ (der_26283 v h) (hints_cons _ _ _ (der_26284 v h) (hints_cons _ _ _ (der_26285 v h) (hints_cons _ _ _ (der_26286 v h) (hints_cons _ _ _ (der_26287 v h) (hints_cons _ _ _ (der_26288 v h) (hints_cons _ _ _ (der_26289 v h) (hints_cons _ _ _ (der_26290 v h) (hints_cons _ _ _ (der_26291 v h) (hints_cons _ _ _ (der_26292 v h) (hints_cons _ _ _ (der_26293 v h) (hints_cons _ _ _ (der_26294 v h) (hints_cons _ _ _ (der_26295 v h) (hints_cons _ _ _ (der_26296 v h) (hints_cons _ _ _ (der_26297 v h) (hints_cons _ _ _ (der_26298 v h) (hints_cons _ _ _ (der_26299 v h) (hints_cons _ _ _ (der_26300 v h) (hints_cons _ _ _ (der_26301 v h) (hints_cons _ _ _ (der_26302 v h) (hints_cons _ _ _ (der_26303 v h) (hints_cons _ _ _ (der_26304 v h) (hints_cons _ _ _ (der_26305 v h) (hints_cons _ _ _ (der_26306 v h) (hints_cons _ _ _ (der_26307 v h) (hints_cons _ _ _ (der_26308 v h) (hints_cons _ _ _ (der_26309 v h) (hints_cons _ _ _ (der_26310 v h) (hints_cons _ _ _ (der_26311 v h) (hints_cons _ _ _ (der_26312 v h) (hints_cons _ _ _ (der_26313 v h) (hints_cons _ _ _ (der_26314 v h) (hints_cons _ _ _ (der_26315 v h) (hints_cons _ _ _ (der_26316 v h) (hints_cons _ _ _ (der_26317 v h) (hints_cons _ _ _ (der_26318 v h) (hints_cons _ _ _ (der_26319 v h) (hints_cons _ _ _ (der_26320 v h) (hints_cons _ _ _ (der_26321 v h) (hints_cons _ _ _ (der_26322 v h) (hints_cons _ _ _ (der_26323 v h) (hints_cons _ _ _ (der_26324 v h) (hints_cons _ _ _ (der_26325 v h) (hints_cons _ _ _ (der_26326 v h) (hints_cons _ _ _ (der_26327 v h) (hints_cons _ _ _ (der_26328 v h) (hints_cons _ _ _ (der_26329 v h) (hints_cons _ _ _ (der_26330 v h) (hints_cons _ _ _ (der_26331 v h) (hints_cons _ _ _ (der_26332 v h) (hints_cons _ _ _ (der_26333 v h) (hints_cons _ _ _ (der_26334 v h) (hints_cons _ _ _ (der_26335 v h) (hints_cons _ _ _ (der_26336 v h) (hints_cons _ _ _ (der_26337 v h) (hints_cons _ _ _ (der_26338 v h) (hints_cons _ _ _ (der_26339 v h) (hints_cons _ _ _ (der_26340 v h) (hints_cons _ _ _ (der_26341 v h) (hints_cons _ _ _ (der_26342 v h) (hints_cons _ _ _ (der_26343 v h) (hints_cons _ _ _ (der_26344 v h) (hints_cons _ _ _ (der_26345 v h) (hints_cons _ _ _ (der_26346 v h) (hints_cons _ _ _ (der_26347 v h) (hints_cons _ _ _ (der_26348 v h) (hints_cons _ _ _ (der_26349 v h) (hints_cons _ _ _ (der_26350 v h) (hints_cons _ _ _ (der_26351 v h) (hints_cons _ _ _ (der_26352 v h) (hints_cons _ _ _ (der_26353 v h) (hints_cons _ _ _ (der_26354 v h) (hints_cons _ _ _ (der_26355 v h) (hints_cons _ _ _ (der_26356 v h) (hints_cons _ _ _ (der_26357 v h) (hints_cons _ _ _ (der_26358 v h) (hints_cons _ _ _ (der_26359 v h) (hints_cons _ _ _ (der_26360 v h) (hints_cons _ _ _ (der_26361 v h) (hints_cons _ _ _ (der_26362 v h) (hints_cons _ _ _ (der_26363 v h) (hints_cons _ _ _ (der_26364 v h) (hints_cons _ _ _ (der_26365 v h) (hints_cons _ _ _ (der_26366 v h) (hints_cons _ _ _ (der_26367 v h) (hints_cons _ _ _ (der_26368 v h) (hints_cons _ _ _ (der_26369 v h) (hints_cons _ _ _ (der_26370 v h) (hints_cons _ _ _ (der_26371 v h) (hints_cons _ _ _ (der_26372 v h) (hints_cons _ _ _ (der_26373 v h) (hints_cons _ _ _ (der_26374 v h) (hints_cons _ _ _ (der_26375 v h) (hints_cons _ _ _ (der_26376 v h) (hints_cons _ _ _ (der_26377 v h) (hints_cons _ _ _ (der_26378 v h) (hints_cons _ _ _ (der_26379 v h) (hints_cons _ _ _ (der_26380 v h) (hints_cons _ _ _ (der_26381 v h) (hints_cons _ _ _ (der_26382 v h) (hints_cons _ _ _ (der_26383 v h) (hints_cons _ _ _ (der_26384 v h) (hints_cons _ _ _ (der_26385 v h) (hints_cons _ _ _ (der_26386 v h) (hints_cons _ _ _ (der_26387 v h) (hints_cons _ _ _ (der_26388 v h) (hints_cons _ _ _ (der_26389 v h) (hints_cons _ _ _ (der_26390 v h) (hints_cons _ _ _ (der_26391 v h) (hints_cons _ _ _ (der_26392 v h) (hints_cons _ _ _ (der_26393 v h) (hints_cons _ _ _ (der_26394 v h) (hints_cons _ _ _ (der_26395 v h) (hints_cons _ _ _ (der_26396 v h) (hints_cons _ _ _ (der_26397 v h) (hints_cons _ _ _ (der_26398 v h) (hints_cons _ _ _ (der_26399 v h) (hints_cons _ _ _ (der_26400 v h) (hints_cons _ _ _ (der_26401 v h) (hints_cons _ _ _ (der_26402 v h) (hints_cons _ _ _ (der_26403 v h) (hints_cons _ _ _ (der_26404 v h) (hints_cons _ _ _ (der_26405 v h) (hints_cons _ _ _ (der_26406 v h) (hints_cons _ _ _ (der_26407 v h) (hints_cons _ _ _ (der_26408 v h) (hints_cons _ _ _ (der_26409 v h) (hints_cons _ _ _ (der_26410 v h) (hints_cons _ _ _ (der_26411 v h) (hints_cons _ _ _ (der_26412 v h) (hints_cons _ _ _ (der_26414 v h) (hints_cons _ _ _ (der_26415 v h) (hints_cons _ _ _ (der_26416 v h) (hints_cons _ _ _ (der_26417 v h) (hints_cons _ _ _ (der_26418 v h) (hints_cons _ _ _ (der_26419 v h) (hints_cons _ _ _ (der_26420 v h) (hints_cons _ _ _ (der_26421 v h) (hints_cons _ _ _ (der_26422 v h) (hints_cons _ _ _ (der_26423 v h) (hints_cons _ _ _ (der_26424 v h) (hints_cons _ _ _ (der_26425 v h) (hints_cons _ _ _ (der_26426 v h) (hints_cons _ _ _ (der_26427 v h) (hints_cons _ _ _ (der_26428 v h) (hints_cons _ _ _ (der_26429 v h) (hints_cons _ _ _ (der_26430 v h) (hints_cons _ _ _ (der_26431 v h) (hints_cons _ _ _ (der_26432 v h) (hints_cons _ _ _ (der_26433 v h) (hints_cons _ _ _ (der_26434 v h) (hints_cons _ _ _ (der_26435 v h) (hints_cons _ _ _ (der_26436 v h) (hints_cons _ _ _ (der_26437 v h) (hints_cons _ _ _ (der_26438 v h) (hints_cons _ _ _ (der_26439 v h) (hints_cons _ _ _ (der_26440 v h) (hints_cons _ _ _ (der_26441 v h) (hints_cons _ _ _ (der_26442 v h) (hints_cons _ _ _ (der_26443 v h) (hints_cons _ _ _ (der_26445 v h) (hints_cons _ _ _ (der_26446 v h) (hints_cons _ _ _ (der_26447 v h) (hints_cons _ _ _ (der_26448 v h) (hints_cons _ _ _ (der_26449 v h) (hints_cons _ _ _ (der_26450 v h) (hints_cons _ _ _ (der_26451 v h) (hints_cons _ _ _ (der_26453 v h) (hints_cons _ _ _ (der_26454 v h) (hints_cons _ _ _ (der_26455 v h) (hints_cons _ _ _ (der_26456 v h) (hints_cons _ _ _ (der_26457 v h) (hints_cons _ _ _ (der_26458 v h) (hints_cons _ _ _ (der_26459 v h) (hints_cons _ _ _ (der_26460 v h) (hints_cons _ _ _ (der_26461 v h) (hints_cons _ _ _ (der_26462 v h) (hints_cons _ _ _ (der_26463 v h) (hints_cons _ _ _ (der_26464 v h) (hints_cons _ _ _ (der_26465 v h) (hints_cons _ _ _ (der_26466 v h) (hints_cons _ _ _ (der_26467 v h) (hints_cons _ _ _ (der_26469 v h) (hints_cons _ _ _ (der_26470 v h) (hints_cons _ _ _ (der_26471 v h) (hints_cons _ _ _ (der_26472 v h) (hints_cons _ _ _ (der_26473 v h) (hints_cons _ _ _ (der_26474 v h) (hints_cons _ _ _ (der_26475 v h) (hints_cons _ _ _ (der_26477 v h) (hints_cons _ _ _ (der_26478 v h) (hints_cons _ _ _ (der_26479 v h) (hints_cons _ _ _ (der_26480 v h) (hints_cons _ _ _ (der_26481 v h) (hints_cons _ _ _ (der_26482 v h) (hints_cons _ _ _ (der_26483 v h) (hints_cons _ _ _ (der_26485 v h) (hints_cons _ _ _ (der_26486 v h) (hints_cons _ _ _ (der_26487 v h) (hints_cons _ _ _ (der_26488 v h) (hints_cons _ _ _ (der_26489 v h) (hints_cons _ _ _ (der_26490 v h) (hints_cons _ _ _ (der_26491 v h) (hints_cons _ _ _ (der_26492 v h) (hints_cons _ _ _ (der_26493 v h) (hints_cons _ _ _ (der_26494 v h) (hints_cons _ _ _ (der_26495 v h) (hints_cons _ _ _ (der_26496 v h) (hints_cons _ _ _ (der_26497 v h) (hints_cons _ _ _ (der_26498 v h) (hints_cons _ _ _ (der_26499 v h) (hints_cons _ _ _ (der_26500 v h) (hints_cons _ _ _ (der_26501 v h) (hints_cons _ _ _ (der_26502 v h) (hints_cons _ _ _ (der_26503 v h) (hints_cons _ _ _ (der_26504 v h) (hints_cons _ _ _ (der_26505 v h) (hints_cons _ _ _ (der_26506 v h) (hints_cons _ _ _ (der_26507 v h) (hints_cons _ _ _ (der_26508 v h) (hints_cons _ _ _ (der_26509 v h) (hints_cons _ _ _ (der_26510 v h) (hints_cons _ _ _ (der_26511 v h) (hints_cons _ _ _ (der_26512 v h) (hints_cons _ _ _ (der_26513 v h) (hints_cons _ _ _ (der_26514 v h) (hints_cons _ _ _ (der_26515 v h) (hints_cons _ _ _ (der_26516 v h) (hints_cons _ _ _ (der_26517 v h) (hints_cons _ _ _ (der_26518 v h) (hints_cons _ _ _ (der_26519 v h) (hints_cons _ _ _ (der_26520 v h) (hints_cons _ _ _ (der_26521 v h) (hints_cons _ _ _ (der_26522 v h) (hints_cons _ _ _ (der_26523 v h) (hints_cons _ _ _ (der_26524 v h) (hints_cons _ _ _ (der_26525 v h) (hints_cons _ _ _ (der_26526 v h) (hints_cons _ _ _ (der_26527 v h) (hints_cons _ _ _ (der_26528 v h) (hints_cons _ _ _ (der_26529 v h) (hints_cons _ _ _ (der_26530 v h) (hints_cons _ _ _ (der_26531 v h) (hints_cons _ _ _ (der_26532 v h) (hints_cons _ _ _ (der_26533 v h) (hints_cons _ _ _ (der_26534 v h) (hints_cons _ _ _ (der_26535 v h) (hints_cons _ _ _ (der_26536 v h) (hints_cons _ _ _ (der_26537 v h) (hints_cons _ _ _ (der_26538 v h) (hints_cons _ _ _ (der_26539 v h) (hints_cons _ _ _ (der_26540 v h) (hints_cons _ _ _ (der_26541 v h) (hints_cons _ _ _ (der_26542 v h) (hints_cons _ _ _ (der_26543 v h) (hints_cons _ _ _ (der_26544 v h) (hints_cons _ _ _ (der_26545 v h) (hints_cons _ _ _ (der_26546 v h) (hints_cons _ _ _ (der_26547 v h) (hints_cons _ _ _ (der_26548 v h) (hints_cons _ _ _ (der_26549 v h) (hints_cons _ _ _ (der_26550 v h) (hints_cons _ _ _ (der_26551 v h) (hints_cons _ _ _ (der_26552 v h) (hints_cons _ _ _ (der_26553 v h) (hints_cons _ _ _ (der_26555 v h) (hints_cons _ _ _ (der_26556 v h) (hints_cons _ _ _ (der_26557 v h) (hints_cons _ _ _ (der_26558 v h) (hints_cons _ _ _ (der_26559 v h) (hints_cons _ _ _ (der_26560 v h) (hints_cons _ _ _ (der_26561 v h) (hints_cons _ _ _ (der_26562 v h) (hints_cons _ _ _ (der_26563 v h) (hints_cons _ _ _ (der_26565 v h) (hints_cons _ _ _ (der_26566 v h) (hints_cons _ _ _ (der_26567 v h) (hints_cons _ _ _ (der_26568 v h) (hints_cons _ _ _ (der_26569 v h) (hints_cons _ _ _ (der_26570 v h) (hints_cons _ _ _ (der_26571 v h) (hints_cons _ _ _ (der_26573 v h) (hints_cons _ _ _ (der_26574 v h) (hints_cons _ _ _ (der_26575 v h) (hints_cons _ _ _ (der_26576 v h) (hints_cons _ _ _ (der_26577 v h) (hints_cons _ _ _ (der_26578 v h) (hints_cons _ _ _ (der_26579 v h) (hints_cons _ _ _ (der_26580 v h) (hints_cons _ _ _ (der_26581 v h) (hints_cons _ _ _ (der_26582 v h) (hints_cons _ _ _ (der_26583 v h) (hints_cons _ _ _ (der_26584 v h) (hints_cons _ _ _ (der_26585 v h) (hints_cons _ _ _ (der_26586 v h) (hints_cons _ _ _ (der_26587 v h) (hints_cons _ _ _ (der_26588 v h) (hints_cons _ _ _ (der_26589 v h) (hints_cons _ _ _ (der_26590 v h) (hints_cons _ _ _ (der_26591 v h) (hints_cons _ _ _ (der_26592 v h) (hints_cons _ _ _ (der_26593 v h) (hints_cons _ _ _ (der_26594 v h) (hints_cons _ _ _ (der_26595 v h) (hints_cons _ _ _ (der_26596 v h) (hints_cons _ _ _ (der_26597 v h) (hints_cons _ _ _ (der_26598 v h) (hints_cons _ _ _ (der_26599 v h) (hints_cons _ _ _ (der_26600 v h) (hints_cons _ _ _ (der_26601 v h) (hints_cons _ _ _ (der_26602 v h) (hints_cons _ _ _ (der_26603 v h) (hints_cons _ _ _ (der_26605 v h) (hints_cons _ _ _ (der_26606 v h) (hints_cons _ _ _ (der_26607 v h) (hints_cons _ _ _ (der_26608 v h) (hints_cons _ _ _ (der_26609 v h) (hints_cons _ _ _ (der_26610 v h) (hints_cons _ _ _ (der_26611 v h) (hints_cons _ _ _ (der_26612 v h) (hints_cons _ _ _ (der_26613 v h) (hints_cons _ _ _ (der_26614 v h) (hints_cons _ _ _ (der_26615 v h) (hints_cons _ _ _ (der_26616 v h) (hints_cons _ _ _ (der_26617 v h) (hints_cons _ _ _ (der_26618 v h) (hints_cons _ _ _ (der_26619 v h) (hints_cons _ _ _ (der_26620 v h) (hints_cons _ _ _ (der_26621 v h) (hints_cons _ _ _ (der_26622 v h) (hints_cons _ _ _ (der_26623 v h) (hints_cons _ _ _ (der_26624 v h) (hints_cons _ _ _ (der_26625 v h) (hints_cons _ _ _ (der_26626 v h) (hints_cons _ _ _ (der_26627 v h) (hints_cons _ _ _ (der_26628 v h) (hints_cons _ _ _ (der_26629 v h) (hints_cons _ _ _ (der_26630 v h) (hints_cons _ _ _ (der_26631 v h) (hints_cons _ _ _ (der_26632 v h) (hints_cons _ _ _ (der_26633 v h) (hints_cons _ _ _ (der_26634 v h) (hints_cons _ _ _ (der_26635 v h) (hints_cons _ _ _ (der_26636 v h) (hints_cons _ _ _ (der_26637 v h) (hints_cons _ _ _ (der_26638 v h) (hints_cons _ _ _ (der_26639 v h) (hints_cons _ _ _ (der_26640 v h) (hints_cons _ _ _ (der_26641 v h) (hints_cons _ _ _ (der_26642 v h) (hints_cons _ _ _ (der_26643 v h) (hints_cons _ _ _ (der_26644 v h) (hints_cons _ _ _ (der_26645 v h) (hints_cons _ _ _ (der_26646 v h) (hints_cons _ _ _ (der_26647 v h) (hints_cons _ _ _ (der_26648 v h) (hints_cons _ _ _ (der_26649 v h) (hints_cons _ _ _ (der_26650 v h) (hints_cons _ _ _ (der_26651 v h) (hints_cons _ _ _ (der_26652 v h) (hints_cons _ _ _ (der_26653 v h) (hints_cons _ _ _ (der_26654 v h) (hints_cons _ _ _ (der_26655 v h) (hints_cons _ _ _ (der_26656 v h) (hints_cons _ _ _ (der_26657 v h) (hints_cons _ _ _ (der_26658 v h) (hints_cons _ _ _ (der_26659 v h) (hints_cons _ _ _ (der_26660 v h) (hints_cons _ _ _ (der_26661 v h) (hints_cons _ _ _ (der_26662 v h) (hints_cons _ _ _ (der_26663 v h) (hints_cons _ _ _ (der_26664 v h) (hints_cons _ _ _ (der_26665 v h) (hints_cons _ _ _ (der_26666 v h) (hints_cons _ _ _ (der_26667 v h) (hints_cons _ _ _ (der_26668 v h) (hints_cons _ _ _ (der_26669 v h) (hints_cons _ _ _ (der_26670 v h) (hints_cons _ _ _ (der_26671 v h) (hints_cons _ _ _ (der_26672 v h) (hints_cons _ _ _ (der_26673 v h) (hints_cons _ _ _ (der_26674 v h) (hints_cons _ _ _ (der_26675 v h) (hints_cons _ _ _ (der_26676 v h) (hints_cons _ _ _ (der_26677 v h) (hints_cons _ _ _ (der_26678 v h) (hints_cons _ _ _ (der_26679 v h) (hints_cons _ _ _ (der_26680 v h) (hints_cons _ _ _ (der_26681 v h) (hints_cons _ _ _ (der_26682 v h) (hints_cons _ _ _ (der_26683 v h) (hints_cons _ _ _ (der_26684 v h) (hints_cons _ _ _ (der_26685 v h) (hints_cons _ _ _ (der_26686 v h) (hints_cons _ _ _ (der_26687 v h) (hints_cons _ _ _ (der_26688 v h) (hints_cons _ _ _ (der_26689 v h) (hints_cons _ _ _ (der_26690 v h) (hints_cons _ _ _ (der_26691 v h) (hints_cons _ _ _ (der_26692 v h) (hints_cons _ _ _ (der_26693 v h) (hints_cons _ _ _ (der_26694 v h) (hints_cons _ _ _ (der_26695 v h) (hints_cons _ _ _ (der_26696 v h) (hints_cons _ _ _ (der_26697 v h) (hints_cons _ _ _ (der_26698 v h) (hints_cons _ _ _ (der_26699 v h) (hints_cons _ _ _ (der_26700 v h) (hints_cons _ _ _ (der_26701 v h) (hints_cons _ _ _ (der_26702 v h) (hints_cons _ _ _ (der_26703 v h) (hints_cons _ _ _ (der_26704 v h) (hints_cons _ _ _ (der_26705 v h) (hints_cons _ _ _ (der_26706 v h) (hints_cons _ _ _ (der_26707 v h) (hints_cons _ _ _ (der_26708 v h) (hints_cons _ _ _ (der_26709 v h) (hints_cons _ _ _ (der_26710 v h) (hints_cons _ _ _ (der_26711 v h) (hints_cons _ _ _ (der_26712 v h) (hints_cons _ _ _ (der_26713 v h) (hints_cons _ _ _ (der_26714 v h) (hints_cons _ _ _ (der_26715 v h) (hints_cons _ _ _ (der_26716 v h) (hints_cons _ _ _ (der_26717 v h) (hints_cons _ _ _ (der_26718 v h) (hints_cons _ _ _ (der_26719 v h) (hints_cons _ _ _ (der_26720 v h) (hints_cons _ _ _ (der_26721 v h) (hints_cons _ _ _ (der_26722 v h) (hints_cons _ _ _ (der_26724 v h) (hints_cons _ _ _ (der_26726 v h) (hints_cons _ _ _ (der_26727 v h) (hints_cons _ _ _ (der_26728 v h) (hints_cons _ _ _ (der_26729 v h) (hints_cons _ _ _ (der_26730 v h) (hints_cons _ _ _ (der_26731 v h) (hints_cons _ _ _ (der_26732 v h) (hints_cons _ _ _ (der_26733 v h) (hints_cons _ _ _ (der_26734 v h) (hints_cons _ _ _ (der_26735 v h) (hints_cons _ _ _ (der_26736 v h) (hints_cons _ _ _ (der_26737 v h) (hints_cons _ _ _ (der_26738 v h) (hints_cons _ _ _ (der_26739 v h) (hints_cons _ _ _ (der_26740 v h) (hints_cons _ _ _ (der_26741 v h) (hints_cons _ _ _ (der_26742 v h) (hints_cons _ _ _ (der_26743 v h) (hints_cons _ _ _ (der_26744 v h) (hints_cons _ _ _ (der_26745 v h) (hints_cons _ _ _ (der_26746 v h) (hints_cons _ _ _ (der_26747 v h) (hints_cons _ _ _ (der_26748 v h) (hints_cons _ _ _ (der_26749 v h) (hints_cons _ _ _ (der_26750 v h) (hints_cons _ _ _ (der_26751 v h) (hints_cons _ _ _ (der_26752 v h) (hints_cons _ _ _ (der_26753 v h) (hints_cons _ _ _ (der_26754 v h) (hints_cons _ _ _ (der_26755 v h) (hints_cons _ _ _ (der_26756 v h) (hints_cons _ _ _ (der_26757 v h) (hints_cons _ _ _ (der_26758 v h) (hints_cons _ _ _ (der_26759 v h) (hints_cons _ _ _ (der_26760 v h) (hints_cons _ _ _ (der_26761 v h) (hints_cons _ _ _ (der_26762 v h) (hints_cons _ _ _ (der_26763 v h) (hints_cons _ _ _ (der_26764 v h) (hints_cons _ _ _ (der_26765 v h) (hints_cons _ _ _ (der_26766 v h) (hints_cons _ _ _ (der_26767 v h) (hints_cons _ _ _ (der_26768 v h) (hints_cons _ _ _ (der_26769 v h) (hints_cons _ _ _ (der_26770 v h) (hints_cons _ _ _ (der_26771 v h) (hints_cons _ _ _ (der_26772 v h) (hints_cons _ _ _ (der_26773 v h) (hints_cons _ _ _ (der_26774 v h) (hints_cons _ _ _ (der_26775 v h) (hints_cons _ _ _ (der_26776 v h) (hints_cons _ _ _ (der_26777 v h) (hints_cons _ _ _ (der_26778 v h) (hints_cons _ _ _ (der_26779 v h) (hints_cons _ _ _ (der_26780 v h) (hints_cons _ _ _ (der_26781 v h) (hints_cons _ _ _ (der_26782 v h) (hints_cons _ _ _ (der_26783 v h) (hints_cons _ _ _ (der_26784 v h) (hints_cons _ _ _ (der_26785 v h) (hints_cons _ _ _ (der_26786 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix008 := prefix007 ++ chunk008
theorem prefix_sound008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix008, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound007 v h c hc
  · exact chunk_sound008 v h c hc
end Percolation.NReplay
