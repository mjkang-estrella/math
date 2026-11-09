import NReplay047
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_51199 : CNF.NClause := [(90,true),(62,true),(73,false),(81,true),(59,false)]
theorem der_51199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51199 :=
  CNF.rup_sound cl_51199 [cl_33595,cl_51195] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33595 v h) (hints_cons _ _ _ (der_51195 v h) (by intro d hd; cases hd)))
def cl_51200 : CNF.NClause := [(62,false),(59,false),(73,true),(28,false),(70,false)]
theorem der_51200 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51200 :=
  CNF.rup_sound cl_51200 [cl_33596,cl_33547] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33596 v h) (hints_cons _ _ _ (der_33547 v h) (by intro d hd; cases hd)))
def cl_51202 : CNF.NClause := [(90,true),(62,true),(73,true),(28,true),(59,false)]
theorem der_51202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51202 :=
  CNF.rup_sound cl_51202 [cl_33601,cl_50590] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33601 v h) (hints_cons _ _ _ (der_50590 v h) (by intro d hd; cases hd)))
def cl_51217 : CNF.NClause := [(41,false),(92,false),(73,false),(76,false),(72,true)]
theorem der_51217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51217 :=
  CNF.rup_sound cl_51217 [cl_33616,cl_44004] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33616 v h) (hints_cons _ _ _ (der_44004 v h) (by intro d hd; cases hd)))
def cl_51218 : CNF.NClause := [(76,false),(92,false),(74,false),(73,true),(41,false)]
theorem der_51218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51218 :=
  CNF.rup_sound cl_51218 [cl_33618,cl_47556] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33618 v h) (hints_cons _ _ _ (der_47556 v h) (by intro d hd; cases hd)))
def cl_51219 : CNF.NClause := [(92,false),(72,false),(74,true),(41,false),(76,false)]
theorem der_51219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51219 :=
  CNF.rup_sound cl_51219 [cl_33622,cl_44004] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33622 v h) (hints_cons _ _ _ (der_44004 v h) (by intro d hd; cases hd)))
def cl_51220 : CNF.NClause := [(76,false),(74,true),(92,false),(10,false),(41,false)]
theorem der_51220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51220 :=
  CNF.rup_sound cl_51220 [cl_33623,cl_51219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33623 v h) (hints_cons _ _ _ (der_51219 v h) (by intro d hd; cases hd)))
def cl_51222 : CNF.NClause := [(73,true),(92,false),(41,false),(74,false),(75,false)]
theorem der_51222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51222 :=
  CNF.rup_sound cl_51222 [cl_33628,cl_33626] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33628 v h) (hints_cons _ _ _ (der_33626 v h) (by intro d hd; cases hd)))
def cl_51223 : CNF.NClause := [(73,false),(75,false),(92,false),(41,false),(74,true)]
theorem der_51223 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51223 :=
  CNF.rup_sound cl_51223 [cl_33630,cl_33629] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33630 v h) (hints_cons _ _ _ (der_33629 v h) (by intro d hd; cases hd)))
def cl_51224 : CNF.NClause := [(73,true),(92,false),(75,false),(41,false),(72,false)]
theorem der_51224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51224 :=
  CNF.rup_sound cl_51224 [cl_33632,cl_33626] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33632 v h) (hints_cons _ _ _ (der_33626 v h) (by intro d hd; cases hd)))
def cl_51226 : CNF.NClause := [(73,true),(92,false),(41,false),(72,false),(74,false)]
theorem der_51226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51226 :=
  CNF.rup_sound cl_51226 [cl_33639,cl_33626] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33639 v h) (hints_cons _ _ _ (der_33626 v h) (by intro d hd; cases hd)))
def cl_51228 : CNF.NClause := [(92,false),(72,false),(73,true),(10,false),(41,false)]
theorem der_51228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51228 :=
  CNF.rup_sound cl_51228 [cl_33645,cl_33638] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33645 v h) (hints_cons _ _ _ (der_33638 v h) (by intro d hd; cases hd)))
def cl_51229 : CNF.NClause := [(75,true),(41,false),(74,true),(92,false),(72,false)]
theorem der_51229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51229 :=
  CNF.rup_sound cl_51229 [cl_33646,cl_51219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33646 v h) (hints_cons _ _ _ (der_51219 v h) (by intro d hd; cases hd)))
def cl_51231 : CNF.NClause := [(92,true),(76,false),(74,false),(72,false),(41,false)]
theorem der_51231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51231 :=
  CNF.rup_sound cl_51231 [cl_35522,cl_35707] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35522 v h) (hints_cons _ _ _ (der_35707 v h) (by intro d hd; cases hd)))
def cl_51232 : CNF.NClause := [(73,true),(72,false),(74,false),(41,false),(76,false)]
theorem der_51232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51232 :=
  CNF.rup_sound cl_51232 [cl_33650,cl_35707] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33650 v h) (hints_cons _ _ _ (der_35707 v h) (by intro d hd; cases hd)))
def cl_51233 : CNF.NClause := [(75,false),(74,false),(41,false),(10,true),(76,false)]
theorem der_51233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51233 :=
  CNF.rup_sound cl_51233 [cl_33652,cl_49751] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33652 v h) (hints_cons _ _ _ (der_49751 v h) (by intro d hd; cases hd)))
def cl_51234 : CNF.NClause := [(75,false),(72,true),(73,false),(76,false),(41,false)]
theorem der_51234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51234 :=
  CNF.rup_sound cl_51234 [cl_33655,cl_33649] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33655 v h) (hints_cons _ _ _ (der_33649 v h) (by intro d hd; cases hd)))
def cl_51235 : CNF.NClause := [(72,false),(74,true),(41,false),(75,false),(76,false)]
theorem der_51235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51235 :=
  CNF.rup_sound cl_51235 [cl_33656,cl_49751] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33656 v h) (hints_cons _ _ _ (der_49751 v h) (by intro d hd; cases hd)))
def cl_51236 : CNF.NClause := [(76,false),(75,false),(41,false),(74,true),(10,false)]
theorem der_51236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51236 :=
  CNF.rup_sound cl_51236 [cl_33658,cl_51235] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33658 v h) (hints_cons _ _ _ (der_51235 v h) (by intro d hd; cases hd)))
def cl_51237 : CNF.NClause := [(75,false),(74,true),(10,true),(41,false),(76,false)]
theorem der_51237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51237 :=
  CNF.rup_sound cl_51237 [cl_33659,cl_49751] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33659 v h) (hints_cons _ _ _ (der_49751 v h) (by intro d hd; cases hd)))
def cl_51238 : CNF.NClause := [(73,false),(76,false),(10,true),(41,false),(74,false)]
theorem der_51238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51238 :=
  CNF.rup_sound cl_51238 [cl_33662,cl_36694] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33662 v h) (hints_cons _ _ _ (der_36694 v h) (by intro d hd; cases hd)))
def cl_51240 : CNF.NClause := [(73,true),(74,false),(76,false),(41,false),(10,false)]
theorem der_51240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51240 :=
  CNF.rup_sound cl_51240 [cl_33665,cl_51218] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33665 v h) (hints_cons _ _ _ (der_51218 v h) (by intro d hd; cases hd)))
def cl_51241 : CNF.NClause := [(76,false),(74,false),(41,false),(92,true),(10,true)]
theorem der_51241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51241 :=
  CNF.rup_sound cl_51241 [cl_33666,cl_36694] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33666 v h) (hints_cons _ _ _ (der_36694 v h) (by intro d hd; cases hd)))
def cl_51243 : CNF.NClause := [(41,false),(75,true),(10,false),(72,false),(76,false)]
theorem der_51243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51243 :=
  CNF.rup_sound cl_51243 [cl_33671,cl_33667] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33671 v h) (hints_cons _ _ _ (der_33667 v h) (by intro d hd; cases hd)))
def cl_51244 : CNF.NClause := [(75,true),(41,false),(72,false),(76,false),(92,true)]
theorem der_51244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51244 :=
  CNF.rup_sound cl_51244 [cl_33672,cl_33668] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33672 v h) (hints_cons _ _ _ (der_33668 v h) (by intro d hd; cases hd)))
def cl_51245 : CNF.NClause := [(75,true),(41,false),(74,true),(76,false),(10,false)]
theorem der_51245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51245 :=
  CNF.rup_sound cl_51245 [cl_33673,cl_51243] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33673 v h) (hints_cons _ _ _ (der_51243 v h) (by intro d hd; cases hd)))
def cl_51246 : CNF.NClause := [(75,false),(74,false),(72,true),(73,false),(41,false)]
theorem der_51246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51246 :=
  CNF.rup_sound cl_51246 [cl_33677,cl_33649] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33677 v h) (hints_cons _ _ _ (der_33649 v h) (by intro d hd; cases hd)))
def cl_51247 : CNF.NClause := [(75,false),(74,false),(72,false),(41,false),(10,true)]
theorem der_51247 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51247 :=
  CNF.rup_sound cl_51247 [cl_33679,cl_36694] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33679 v h) (hints_cons _ _ _ (der_36694 v h) (by intro d hd; cases hd)))
def cl_51248 : CNF.NClause := [(75,false),(41,false),(74,false),(10,false),(72,true)]
theorem der_51248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51248 :=
  CNF.rup_sound cl_51248 [cl_33680,cl_33651] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33680 v h) (hints_cons _ _ _ (der_33651 v h) (by intro d hd; cases hd)))
def cl_51249 : CNF.NClause := [(75,false),(74,false),(41,false),(72,true),(10,true)]
theorem der_51249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51249 :=
  CNF.rup_sound cl_51249 [cl_33681,cl_51246] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33681 v h) (hints_cons _ _ _ (der_51246 v h) (by intro d hd; cases hd)))
def cl_51250 : CNF.NClause := [(73,false),(72,false),(75,false),(41,false),(74,true)]
theorem der_51250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51250 :=
  CNF.rup_sound cl_51250 [cl_33683,cl_51223] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33683 v h) (hints_cons _ _ _ (der_51223 v h) (by intro d hd; cases hd)))
def cl_51251 : CNF.NClause := [(73,false),(41,false),(74,true),(10,false),(75,false)]
theorem der_51251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51251 :=
  CNF.rup_sound cl_51251 [cl_33684,cl_51236] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33684 v h) (hints_cons _ _ _ (der_51236 v h) (by intro d hd; cases hd)))
def cl_51252 : CNF.NClause := [(76,true),(74,true),(75,false),(41,false),(73,false)]
theorem der_51252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51252 :=
  CNF.rup_sound cl_51252 [cl_33685,cl_51223] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33685 v h) (hints_cons _ _ _ (der_51223 v h) (by intro d hd; cases hd)))
def cl_51253 : CNF.NClause := [(72,false),(41,false),(75,false),(74,true),(10,false)]
theorem der_51253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51253 :=
  CNF.rup_sound cl_51253 [cl_33686,cl_51235] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33686 v h) (hints_cons _ _ _ (der_51235 v h) (by intro d hd; cases hd)))
def cl_51254 : CNF.NClause := [(72,false),(41,false),(75,false),(74,true),(92,true)]
theorem der_51254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51254 :=
  CNF.rup_sound cl_51254 [cl_33687,cl_51235] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33687 v h) (hints_cons _ _ _ (der_51235 v h) (by intro d hd; cases hd)))
def cl_51255 : CNF.NClause := [(75,false),(74,true),(92,true),(10,false),(41,false)]
theorem der_51255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51255 :=
  CNF.rup_sound cl_51255 [cl_33688,cl_51236] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33688 v h) (hints_cons _ _ _ (der_51236 v h) (by intro d hd; cases hd)))
def cl_51256 : CNF.NClause := [(75,false),(41,false),(72,true),(73,true),(10,true)]
theorem der_51256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51256 :=
  CNF.rup_sound cl_51256 [cl_33689,cl_51249] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33689 v h) (hints_cons _ _ _ (der_51249 v h) (by intro d hd; cases hd)))
def cl_51257 : CNF.NClause := [(73,false),(10,true),(41,false),(74,false),(72,false)]
theorem der_51257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51257 :=
  CNF.rup_sound cl_51257 [cl_33690,cl_51247] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33690 v h) (hints_cons _ _ _ (der_51247 v h) (by intro d hd; cases hd)))
def cl_51258 : CNF.NClause := [(41,false),(74,false),(73,false),(10,false),(72,true)]
theorem der_51258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51258 :=
  CNF.rup_sound cl_51258 [cl_33691,cl_51248] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33691 v h) (hints_cons _ _ _ (der_51248 v h) (by intro d hd; cases hd)))
def cl_51259 : CNF.NClause := [(74,false),(73,false),(41,false),(72,true),(92,true)]
theorem der_51259 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51259 :=
  CNF.rup_sound cl_51259 [cl_33692,cl_51246] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33692 v h) (hints_cons _ _ _ (der_51246 v h) (by intro d hd; cases hd)))
def cl_51261 : CNF.NClause := [(73,true),(75,true),(41,false),(72,false),(74,false)]
theorem der_51261 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51261 :=
  CNF.rup_sound cl_51261 [cl_33694,cl_51226] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33694 v h) (hints_cons _ _ _ (der_51226 v h) (by intro d hd; cases hd)))
def cl_51262 : CNF.NClause := [(75,true),(10,false),(73,true),(41,false),(74,false)]
theorem der_51262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51262 :=
  CNF.rup_sound cl_51262 [cl_33695,cl_51240] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33695 v h) (hints_cons _ _ _ (der_51240 v h) (by intro d hd; cases hd)))
def cl_51263 : CNF.NClause := [(74,false),(75,true),(76,true),(73,true),(41,false)]
theorem der_51263 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51263 :=
  CNF.rup_sound cl_51263 [cl_33696,cl_51261] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33696 v h) (hints_cons _ _ _ (der_51261 v h) (by intro d hd; cases hd)))
def cl_51264 : CNF.NClause := [(73,false),(41,false),(74,true),(10,false),(72,true)]
theorem der_51264 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51264 :=
  CNF.rup_sound cl_51264 [cl_33699,cl_51251] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33699 v h) (hints_cons _ _ _ (der_51251 v h) (by intro d hd; cases hd)))
def cl_51265 : CNF.NClause := [(76,true),(72,true),(73,false),(41,false),(74,true)]
theorem der_51265 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51265 :=
  CNF.rup_sound cl_51265 [cl_33700,cl_51252] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33700 v h) (hints_cons _ _ _ (der_51252 v h) (by intro d hd; cases hd)))
def cl_51266 : CNF.NClause := [(72,false),(73,true),(75,true),(41,false),(10,false)]
theorem der_51266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51266 :=
  CNF.rup_sound cl_51266 [cl_33701,cl_51228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33701 v h) (hints_cons _ _ _ (der_51228 v h) (by intro d hd; cases hd)))
def cl_51267 : CNF.NClause := [(76,true),(75,true),(41,false),(74,true),(10,true)]
theorem der_51267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51267 :=
  CNF.rup_sound cl_51267 [cl_33704,cl_33702] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33704 v h) (hints_cons _ _ _ (der_33702 v h) (by intro d hd; cases hd)))
def cl_51271 : CNF.NClause := [(63,true),(78,false),(87,false),(83,false),(35,false)]
theorem der_51271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51271 :=
  CNF.rup_sound cl_51271 [cl_33713,cl_33710] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33713 v h) (hints_cons _ _ _ (der_33710 v h) (by intro d hd; cases hd)))
def cl_51272 : CNF.NClause := [(83,false),(73,false),(87,false),(35,false),(63,true)]
theorem der_51272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51272 :=
  CNF.rup_sound cl_51272 [cl_33717,cl_33714] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33717 v h) (hints_cons _ _ _ (der_33714 v h) (by intro d hd; cases hd)))
def cl_51273 : CNF.NClause := [(87,false),(35,false),(83,false),(68,false),(63,true)]
theorem der_51273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51273 :=
  CNF.rup_sound cl_51273 [cl_33720,cl_33714] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33720 v h) (hints_cons _ _ _ (der_33714 v h) (by intro d hd; cases hd)))
def cl_51275 : CNF.NClause := [(87,false),(63,true),(35,false),(83,false),(4,false)]
theorem der_51275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51275 :=
  CNF.rup_sound cl_51275 [cl_33723,cl_51273] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33723 v h) (hints_cons _ _ _ (der_51273 v h) (by intro d hd; cases hd)))
def cl_51276 : CNF.NClause := [(63,true),(35,false),(87,false),(83,false),(4,true)]
theorem der_51276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51276 :=
  CNF.rup_sound cl_51276 [cl_33724,cl_51273] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33724 v h) (hints_cons _ _ _ (der_51273 v h) (by intro d hd; cases hd)))
def cl_51277 : CNF.NClause := [(73,true),(78,false),(35,false),(87,false),(68,false)]
theorem der_51277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51277 :=
  CNF.rup_sound cl_51277 [cl_33730,cl_33729] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33730 v h) (hints_cons _ _ _ (der_33729 v h) (by intro d hd; cases hd)))
def cl_51278 : CNF.NClause := [(68,true),(78,false),(35,false),(63,false),(87,false)]
theorem der_51278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51278 :=
  CNF.rup_sound cl_51278 [cl_33731,cl_33726] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33731 v h) (hints_cons _ _ _ (der_33726 v h) (by intro d hd; cases hd)))
def cl_51279 : CNF.NClause := [(87,false),(78,false),(73,true),(35,false),(4,false)]
theorem der_51279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51279 :=
  CNF.rup_sound cl_51279 [cl_33732,cl_51277] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33732 v h) (hints_cons _ _ _ (der_51277 v h) (by intro d hd; cases hd)))
def cl_51280 : CNF.NClause := [(73,true),(78,false),(68,true),(35,false),(87,false)]
theorem der_51280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51280 :=
  CNF.rup_sound cl_51280 [cl_33733,cl_51279] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33733 v h) (hints_cons _ _ _ (der_51279 v h) (by intro d hd; cases hd)))
def cl_51281 : CNF.NClause := [(78,true),(73,false),(87,false),(68,false),(35,false)]
theorem der_51281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51281 :=
  CNF.rup_sound cl_51281 [cl_33736,cl_33734] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33736 v h) (hints_cons _ _ _ (der_33734 v h) (by intro d hd; cases hd)))
def cl_51282 : CNF.NClause := [(68,true),(35,false),(63,false),(73,false),(87,false)]
theorem der_51282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51282 :=
  CNF.rup_sound cl_51282 [cl_33738,cl_33726] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33738 v h) (hints_cons _ _ _ (der_33726 v h) (by intro d hd; cases hd)))
def cl_51283 : CNF.NClause := [(63,true),(73,false),(87,false),(4,false),(35,false)]
theorem der_51283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51283 :=
  CNF.rup_sound cl_51283 [cl_33739,cl_33727] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33739 v h) (hints_cons _ _ _ (der_33727 v h) (by intro d hd; cases hd)))
def cl_51284 : CNF.NClause := [(87,false),(78,true),(73,false),(35,false),(63,true)]
theorem der_51284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51284 :=
  CNF.rup_sound cl_51284 [cl_33740,cl_51283] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33740 v h) (hints_cons _ _ _ (der_51283 v h) (by intro d hd; cases hd)))
def cl_51285 : CNF.NClause := [(78,true),(68,false),(63,false),(87,false),(35,false)]
theorem der_51285 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51285 :=
  CNF.rup_sound cl_51285 [cl_33742,cl_33734] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33742 v h) (hints_cons _ _ _ (der_33734 v h) (by intro d hd; cases hd)))
def cl_51286 : CNF.NClause := [(78,true),(68,false),(87,false),(35,false),(4,false)]
theorem der_51286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51286 :=
  CNF.rup_sound cl_51286 [cl_33743,cl_51281] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33743 v h) (hints_cons _ _ _ (der_51281 v h) (by intro d hd; cases hd)))
def cl_51287 : CNF.NClause := [(78,true),(35,false),(87,false),(68,false),(4,true)]
theorem der_51287 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51287 :=
  CNF.rup_sound cl_51287 [cl_33744,cl_51285] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33744 v h) (hints_cons _ _ _ (der_51285 v h) (by intro d hd; cases hd)))
def cl_51291 : CNF.NClause := [(73,true),(78,false),(35,false),(83,false),(68,false)]
theorem der_51291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51291 :=
  CNF.rup_sound cl_51291 [cl_33754,cl_51277] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33754 v h) (hints_cons _ _ _ (der_51277 v h) (by intro d hd; cases hd)))
def cl_51292 : CNF.NClause := [(68,true),(78,false),(83,false),(4,false),(35,false)]
theorem der_51292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51292 :=
  CNF.rup_sound cl_51292 [cl_33756,cl_33755] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33756 v h) (hints_cons _ _ _ (der_33755 v h) (by intro d hd; cases hd)))
def cl_51293 : CNF.NClause := [(78,false),(35,false),(73,true),(83,false),(63,true)]
theorem der_51293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51293 :=
  CNF.rup_sound cl_51293 [cl_33757,cl_51291] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33757 v h) (hints_cons _ _ _ (der_51291 v h) (by intro d hd; cases hd)))
def cl_51294 : CNF.NClause := [(78,true),(73,false),(35,false),(83,false),(68,false)]
theorem der_51294 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51294 :=
  CNF.rup_sound cl_51294 [cl_33760,cl_51281] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33760 v h) (hints_cons _ _ _ (der_51281 v h) (by intro d hd; cases hd)))
def cl_51295 : CNF.NClause := [(78,true),(73,false),(35,false),(83,false),(4,false)]
theorem der_51295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51295 :=
  CNF.rup_sound cl_51295 [cl_33763,cl_33761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33763 v h) (hints_cons _ _ _ (der_33761 v h) (by intro d hd; cases hd)))
def cl_51297 : CNF.NClause := [(83,false),(68,false),(73,true),(4,true),(35,false)]
theorem der_51297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51297 :=
  CNF.rup_sound cl_51297 [cl_33767,cl_51291] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33767 v h) (hints_cons _ _ _ (der_51291 v h) (by intro d hd; cases hd)))
def cl_51298 : CNF.NClause := [(68,true),(83,false),(63,false),(35,false),(4,false)]
theorem der_51298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51298 :=
  CNF.rup_sound cl_51298 [cl_33768,cl_33755] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33768 v h) (hints_cons _ _ _ (der_33755 v h) (by intro d hd; cases hd)))
def cl_51299 : CNF.NClause := [(78,true),(83,false),(4,false),(63,true),(35,false)]
theorem der_51299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51299 :=
  CNF.rup_sound cl_51299 [cl_33770,cl_51275] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33770 v h) (hints_cons _ _ _ (der_51275 v h) (by intro d hd; cases hd)))
def cl_51300 : CNF.NClause := [(68,false),(78,false),(73,false),(35,false),(63,true)]
theorem der_51300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51300 :=
  CNF.rup_sound cl_51300 [cl_33774,cl_33773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33774 v h) (hints_cons _ _ _ (der_33773 v h) (by intro d hd; cases hd)))
def cl_51301 : CNF.NClause := [(78,false),(35,false),(73,false),(4,false),(63,true)]
theorem der_51301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51301 :=
  CNF.rup_sound cl_51301 [cl_33776,cl_51300] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33776 v h) (hints_cons _ _ _ (der_51300 v h) (by intro d hd; cases hd)))
def cl_51302 : CNF.NClause := [(68,false),(78,false),(63,false),(73,true),(35,false)]
theorem der_51302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51302 :=
  CNF.rup_sound cl_51302 [cl_33779,cl_33778] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33779 v h) (hints_cons _ _ _ (der_33778 v h) (by intro d hd; cases hd)))
def cl_51303 : CNF.NClause := [(78,false),(73,true),(68,false),(63,true),(35,false)]
theorem der_51303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51303 :=
  CNF.rup_sound cl_51303 [cl_33781,cl_51291] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33781 v h) (hints_cons _ _ _ (der_51291 v h) (by intro d hd; cases hd)))
def cl_51304 : CNF.NClause := [(78,false),(35,false),(63,false),(73,true),(4,false)]
theorem der_51304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51304 :=
  CNF.rup_sound cl_51304 [cl_33782,cl_51302] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33782 v h) (hints_cons _ _ _ (der_51302 v h) (by intro d hd; cases hd)))
def cl_51306 : CNF.NClause := [(78,true),(73,false),(35,false),(68,false),(63,true)]
theorem der_51306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51306 :=
  CNF.rup_sound cl_51306 [cl_33786,cl_51294] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33786 v h) (hints_cons _ _ _ (der_51294 v h) (by intro d hd; cases hd)))
def cl_51307 : CNF.NClause := [(68,true),(73,false),(63,false),(35,false),(83,true)]
theorem der_51307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51307 :=
  CNF.rup_sound cl_51307 [cl_33788,cl_51282] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33788 v h) (hints_cons _ _ _ (der_51282 v h) (by intro d hd; cases hd)))
def cl_51308 : CNF.NClause := [(73,false),(35,false),(4,false),(63,true),(87,true)]
theorem der_51308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51308 :=
  CNF.rup_sound cl_51308 [cl_33789,cl_51301] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33789 v h) (hints_cons _ _ _ (der_51301 v h) (by intro d hd; cases hd)))
def cl_51309 : CNF.NClause := [(78,true),(35,false),(73,false),(63,true),(87,true)]
theorem der_51309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51309 :=
  CNF.rup_sound cl_51309 [cl_33790,cl_51306] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33790 v h) (hints_cons _ _ _ (der_51306 v h) (by intro d hd; cases hd)))
def cl_51310 : CNF.NClause := [(68,false),(63,false),(73,true),(35,false),(4,false)]
theorem der_51310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51310 :=
  CNF.rup_sound cl_51310 [cl_33791,cl_33778] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33791 v h) (hints_cons _ _ _ (der_33778 v h) (by intro d hd; cases hd)))
def cl_51311 : CNF.NClause := [(68,false),(63,false),(73,true),(35,false),(83,true)]
theorem der_51311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51311 :=
  CNF.rup_sound cl_51311 [cl_33792,cl_51302] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33792 v h) (hints_cons _ _ _ (der_51302 v h) (by intro d hd; cases hd)))
def cl_51312 : CNF.NClause := [(78,true),(68,false),(35,false),(4,false),(63,true)]
theorem der_51312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51312 :=
  CNF.rup_sound cl_51312 [cl_33793,cl_51299] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33793 v h) (hints_cons _ _ _ (der_51299 v h) (by intro d hd; cases hd)))
def cl_51313 : CNF.NClause := [(63,false),(78,true),(35,false),(73,true),(4,false)]
theorem der_51313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51313 :=
  CNF.rup_sound cl_51313 [cl_33795,cl_51310] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33795 v h) (hints_cons _ _ _ (der_51310 v h) (by intro d hd; cases hd)))
def cl_51314 : CNF.NClause := [(78,true),(63,false),(68,true),(35,false),(73,true)]
theorem der_51314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51314 :=
  CNF.rup_sound cl_51314 [cl_33796,cl_51313] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33796 v h) (hints_cons _ _ _ (der_51313 v h) (by intro d hd; cases hd)))
def cl_51321 : CNF.NClause := [(57,false),(83,false),(71,false),(91,false),(62,true)]
theorem der_51321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51321 :=
  CNF.rup_sound cl_51321 [cl_33811,cl_50707] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33811 v h) (hints_cons _ _ _ (der_50707 v h) (by intro d hd; cases hd)))
def cl_51325 : CNF.NClause := [(75,false),(79,false),(91,false),(57,false),(71,true)]
theorem der_51325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51325 :=
  CNF.rup_sound cl_51325 [cl_33818,cl_49554] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33818 v h) (hints_cons _ _ _ (der_49554 v h) (by intro d hd; cases hd)))
def cl_51326 : CNF.NClause := [(91,false),(75,true),(79,false),(26,true),(57,false)]
theorem der_51326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51326 :=
  CNF.rup_sound cl_51326 [cl_33820,cl_49554] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33820 v h) (hints_cons _ _ _ (der_49554 v h) (by intro d hd; cases hd)))
def cl_51327 : CNF.NClause := [(62,true),(91,false),(71,false),(57,false),(79,false)]
theorem der_51327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51327 :=
  CNF.rup_sound cl_51327 [cl_33821,cl_33816] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33821 v h) (hints_cons _ _ _ (der_33816 v h) (by intro d hd; cases hd)))
def cl_51328 : CNF.NClause := [(57,false),(79,false),(91,false),(62,false),(71,true)]
theorem der_51328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51328 :=
  CNF.rup_sound cl_51328 [cl_33822,cl_49554] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33822 v h) (hints_cons _ _ _ (der_49554 v h) (by intro d hd; cases hd)))
def cl_51329 : CNF.NClause := [(62,false),(91,false),(71,true),(79,false),(57,false)]
theorem der_51329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51329 :=
  CNF.rup_sound cl_51329 [cl_33823,cl_51325] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33823 v h) (hints_cons _ _ _ (der_51325 v h) (by intro d hd; cases hd)))
def cl_51330 : CNF.NClause := [(62,true),(57,false),(79,false),(91,false),(71,true)]
theorem der_51330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51330 :=
  CNF.rup_sound cl_51330 [cl_33824,cl_50704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33824 v h) (hints_cons _ _ _ (der_50704 v h) (by intro d hd; cases hd)))
def cl_51331 : CNF.NClause := [(57,false),(75,false),(71,false),(91,false),(62,true)]
theorem der_51331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51331 :=
  CNF.rup_sound cl_51331 [cl_33827,cl_32372] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33827 v h) (hints_cons _ _ _ (der_32372 v h) (by intro d hd; cases hd)))
def cl_51332 : CNF.NClause := [(62,false),(75,false),(91,false),(57,false),(71,true)]
theorem der_51332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51332 :=
  CNF.rup_sound cl_51332 [cl_33829,cl_51325] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33829 v h) (hints_cons _ _ _ (der_51325 v h) (by intro d hd; cases hd)))
def cl_51333 : CNF.NClause := [(57,false),(26,false),(75,false),(91,false),(71,true)]
theorem der_51333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51333 :=
  CNF.rup_sound cl_51333 [cl_33830,cl_51325] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33830 v h) (hints_cons _ _ _ (der_51325 v h) (by intro d hd; cases hd)))
def cl_51334 : CNF.NClause := [(57,false),(91,false),(71,true),(75,false),(26,true)]
theorem der_51334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51334 :=
  CNF.rup_sound cl_51334 [cl_33831,cl_51325] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33831 v h) (hints_cons _ _ _ (der_51325 v h) (by intro d hd; cases hd)))
def cl_51335 : CNF.NClause := [(91,false),(26,true),(57,false),(71,false),(75,true)]
theorem der_51335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51335 :=
  CNF.rup_sound cl_51335 [cl_33833,cl_51326] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33833 v h) (hints_cons _ _ _ (der_51326 v h) (by intro d hd; cases hd)))
def cl_51337 : CNF.NClause := [(57,false),(62,false),(26,false),(91,false),(71,true)]
theorem der_51337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51337 :=
  CNF.rup_sound cl_51337 [cl_33835,cl_51328] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33835 v h) (hints_cons _ _ _ (der_51328 v h) (by intro d hd; cases hd)))
def cl_51338 : CNF.NClause := [(62,false),(91,false),(71,true),(26,true),(57,false)]
theorem der_51338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51338 :=
  CNF.rup_sound cl_51338 [cl_33836,cl_51329] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33836 v h) (hints_cons _ _ _ (der_51329 v h) (by intro d hd; cases hd)))
def cl_51340 : CNF.NClause := [(57,false),(79,false),(75,false),(83,false),(71,true)]
theorem der_51340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51340 :=
  CNF.rup_sound cl_51340 [cl_33842,cl_49554] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33842 v h) (hints_cons _ _ _ (der_49554 v h) (by intro d hd; cases hd)))
def cl_51341 : CNF.NClause := [(83,false),(62,true),(57,false),(71,false),(79,false)]
theorem der_51341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51341 :=
  CNF.rup_sound cl_51341 [cl_33845,cl_33840] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33845 v h) (hints_cons _ _ _ (der_33840 v h) (by intro d hd; cases hd)))
def cl_51343 : CNF.NClause := [(57,false),(83,false),(79,false),(71,true),(75,true)]
theorem der_51343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51343 :=
  CNF.rup_sound cl_51343 [cl_33848,cl_49554] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33848 v h) (hints_cons _ _ _ (der_49554 v h) (by intro d hd; cases hd)))
def cl_51344 : CNF.NClause := [(83,false),(62,true),(57,false),(71,false),(75,false)]
theorem der_51344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51344 :=
  CNF.rup_sound cl_51344 [cl_33851,cl_50707] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33851 v h) (hints_cons _ _ _ (der_50707 v h) (by intro d hd; cases hd)))
def cl_51345 : CNF.NClause := [(83,false),(62,false),(57,false),(71,true),(75,false)]
theorem der_51345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51345 :=
  CNF.rup_sound cl_51345 [cl_33853,cl_33841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33853 v h) (hints_cons _ _ _ (der_33841 v h) (by intro d hd; cases hd)))
def cl_51347 : CNF.NClause := [(83,false),(79,true),(75,false),(57,false),(62,true)]
theorem der_51347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51347 :=
  CNF.rup_sound cl_51347 [cl_33855,cl_51344] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33855 v h) (hints_cons _ _ _ (der_51344 v h) (by intro d hd; cases hd)))
def cl_51348 : CNF.NClause := [(83,false),(62,true),(71,false),(79,true),(57,false)]
theorem der_51348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51348 :=
  CNF.rup_sound cl_51348 [cl_33858,cl_51344] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33858 v h) (hints_cons _ _ _ (der_51344 v h) (by intro d hd; cases hd)))
def cl_51349 : CNF.NClause := [(83,false),(62,false),(26,false),(57,false),(71,true)]
theorem der_51349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51349 :=
  CNF.rup_sound cl_51349 [cl_33859,cl_33852] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33859 v h) (hints_cons _ _ _ (der_33852 v h) (by intro d hd; cases hd)))
def cl_51350 : CNF.NClause := [(83,false),(62,false),(57,false),(71,true),(75,true)]
theorem der_51350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51350 :=
  CNF.rup_sound cl_51350 [cl_33860,cl_51349] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33860 v h) (hints_cons _ _ _ (der_51349 v h) (by intro d hd; cases hd)))
def cl_51352 : CNF.NClause := [(83,false),(62,true),(57,false),(75,true),(26,true)]
theorem der_51352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51352 :=
  CNF.rup_sound cl_51352 [cl_33862,cl_50706] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33862 v h) (hints_cons _ _ _ (der_50706 v h) (by intro d hd; cases hd)))
def cl_51353 : CNF.NClause := [(83,true),(75,false),(79,false),(26,true),(57,false)]
theorem der_51353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51353 :=
  CNF.rup_sound cl_51353 [cl_33863,cl_49554] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33863 v h) (hints_cons _ _ _ (der_49554 v h) (by intro d hd; cases hd)))
def cl_51354 : CNF.NClause := [(79,false),(75,false),(71,false),(62,true),(57,false)]
theorem der_51354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51354 :=
  CNF.rup_sound cl_51354 [cl_33864,cl_51327] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33864 v h) (hints_cons _ _ _ (der_51327 v h) (by intro d hd; cases hd)))
def cl_51359 : CNF.NClause := [(83,true),(79,false),(26,true),(57,false),(75,true)]
theorem der_51359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51359 :=
  CNF.rup_sound cl_51359 [cl_33870,cl_49554] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33870 v h) (hints_cons _ _ _ (der_49554 v h) (by intro d hd; cases hd)))
def cl_51360 : CNF.NClause := [(62,true),(79,false),(71,false),(57,false),(26,false)]
theorem der_51360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51360 :=
  CNF.rup_sound cl_51360 [cl_33871,cl_51327] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33871 v h) (hints_cons _ _ _ (der_51327 v h) (by intro d hd; cases hd)))
def cl_51363 : CNF.NClause := [(57,false),(75,false),(71,false),(79,true),(62,true)]
theorem der_51363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51363 :=
  CNF.rup_sound cl_51363 [cl_33877,cl_51331] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33877 v h) (hints_cons _ _ _ (der_51331 v h) (by intro d hd; cases hd)))
def cl_51364 : CNF.NClause := [(57,false),(26,false),(75,false),(62,false),(71,true)]
theorem der_51364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51364 :=
  CNF.rup_sound cl_51364 [cl_33878,cl_33852] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33878 v h) (hints_cons _ _ _ (der_33852 v h) (by intro d hd; cases hd)))
def cl_51365 : CNF.NClause := [(75,false),(71,true),(62,false),(83,true),(57,false)]
theorem der_51365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51365 :=
  CNF.rup_sound cl_51365 [cl_33879,cl_51332] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33879 v h) (hints_cons _ _ _ (der_51332 v h) (by intro d hd; cases hd)))
def cl_51368 : CNF.NClause := [(62,true),(71,false),(57,false),(79,true),(91,true)]
theorem der_51368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51368 :=
  CNF.rup_sound cl_51368 [cl_33883,cl_51363] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33883 v h) (hints_cons _ _ _ (der_51363 v h) (by intro d hd; cases hd)))
def cl_51371 : CNF.NClause := [(71,false),(92,false),(51,false),(70,false),(67,true)]
theorem der_51371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51371 :=
  CNF.rup_sound cl_51371 [cl_33891,cl_33889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33891 v h) (hints_cons _ _ _ (der_33889 v h) (by intro d hd; cases hd)))
def cl_51373 : CNF.NClause := [(68,false),(51,false),(92,false),(71,false),(67,true)]
theorem der_51373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51373 :=
  CNF.rup_sound cl_51373 [cl_33897,cl_33892] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33897 v h) (hints_cons _ _ _ (der_33892 v h) (by intro d hd; cases hd)))
def cl_51374 : CNF.NClause := [(92,false),(51,false),(68,true),(71,false),(67,false)]
theorem der_51374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51374 :=
  CNF.rup_sound cl_51374 [cl_33899,cl_33893] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33899 v h) (hints_cons _ _ _ (der_33893 v h) (by intro d hd; cases hd)))
def cl_51377 : CNF.NClause := [(68,true),(92,false),(69,false),(51,false),(70,false)]
theorem der_51377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51377 :=
  CNF.rup_sound cl_51377 [cl_33904,cl_33903] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33904 v h) (hints_cons _ _ _ (der_33903 v h) (by intro d hd; cases hd)))
def cl_51378 : CNF.NClause := [(70,false),(51,false),(92,false),(68,false),(69,true)]
theorem der_51378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51378 :=
  CNF.rup_sound cl_51378 [cl_33907,cl_33905] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33907 v h) (hints_cons _ _ _ (der_33905 v h) (by intro d hd; cases hd)))
def cl_51382 : CNF.NClause := [(68,true),(67,false),(69,false),(92,false),(51,false)]
theorem der_51382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51382 :=
  CNF.rup_sound cl_51382 [cl_33916,cl_33903] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33916 v h) (hints_cons _ _ _ (der_33903 v h) (by intro d hd; cases hd)))
def cl_51383 : CNF.NClause := [(69,false),(92,false),(70,true),(51,false),(67,true)]
theorem der_51383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51383 :=
  CNF.rup_sound cl_51383 [cl_33918,cl_33917] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33918 v h) (hints_cons _ _ _ (der_33917 v h) (by intro d hd; cases hd)))
def cl_51384 : CNF.NClause := [(68,false),(51,false),(69,true),(92,false),(67,false)]
theorem der_51384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51384 :=
  CNF.rup_sound cl_51384 [cl_33920,cl_33919] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33920 v h) (hints_cons _ _ _ (der_33919 v h) (by intro d hd; cases hd)))
def cl_51385 : CNF.NClause := [(92,false),(69,true),(51,false),(68,false),(20,false)]
theorem der_51385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51385 :=
  CNF.rup_sound cl_51385 [cl_33921,cl_51378] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33921 v h) (hints_cons _ _ _ (der_51378 v h) (by intro d hd; cases hd)))
def cl_51386 : CNF.NClause := [(92,false),(68,false),(69,true),(20,true),(51,false)]
theorem der_51386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51386 :=
  CNF.rup_sound cl_51386 [cl_33922,cl_51384] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33922 v h) (hints_cons _ _ _ (der_51384 v h) (by intro d hd; cases hd)))
def cl_51388 : CNF.NClause := [(92,false),(67,false),(68,true),(20,true),(51,false)]
theorem der_51388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51388 :=
  CNF.rup_sound cl_51388 [cl_33924,cl_51382] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33924 v h) (hints_cons _ _ _ (der_51382 v h) (by intro d hd; cases hd)))
def cl_51390 : CNF.NClause := [(69,false),(51,false),(71,false),(70,false),(67,true)]
theorem der_51390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51390 :=
  CNF.rup_sound cl_51390 [cl_33930,cl_33927] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33930 v h) (hints_cons _ _ _ (der_33927 v h) (by intro d hd; cases hd)))
def cl_51392 : CNF.NClause := [(71,false),(51,false),(68,true),(70,false),(67,true)]
theorem der_51392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51392 :=
  CNF.rup_sound cl_51392 [cl_33936,cl_51390] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33936 v h) (hints_cons _ _ _ (der_51390 v h) (by intro d hd; cases hd)))
def cl_51394 : CNF.NClause := [(67,false),(68,false),(71,false),(20,true),(51,false)]
theorem der_51394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51394 :=
  CNF.rup_sound cl_51394 [cl_33944,cl_33937] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33944 v h) (hints_cons _ _ _ (der_33937 v h) (by intro d hd; cases hd)))
def cl_51395 : CNF.NClause := [(68,false),(51,false),(71,false),(20,false),(67,true)]
theorem der_51395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51395 :=
  CNF.rup_sound cl_51395 [cl_33945,cl_33938] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33945 v h) (hints_cons _ _ _ (der_33938 v h) (by intro d hd; cases hd)))
def cl_51396 : CNF.NClause := [(68,true),(67,true),(71,false),(20,false),(51,false)]
theorem der_51396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51396 :=
  CNF.rup_sound cl_51396 [cl_33949,cl_51392] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33949 v h) (hints_cons _ _ _ (der_51392 v h) (by intro d hd; cases hd)))
def cl_51397 : CNF.NClause := [(71,false),(51,false),(68,true),(20,true),(67,true)]
theorem der_51397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51397 :=
  CNF.rup_sound cl_51397 [cl_33950,cl_51392] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33950 v h) (hints_cons _ _ _ (der_51392 v h) (by intro d hd; cases hd)))
def cl_51400 : CNF.NClause := [(69,false),(70,false),(68,true),(51,false),(67,true)]
theorem der_51400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51400 :=
  CNF.rup_sound cl_51400 [cl_33957,cl_51392] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33957 v h) (hints_cons _ _ _ (der_51392 v h) (by intro d hd; cases hd)))
def cl_51401 : CNF.NClause := [(70,false),(51,false),(69,true),(67,false),(68,false)]
theorem der_51401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51401 :=
  CNF.rup_sound cl_51401 [cl_33959,cl_33958] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33959 v h) (hints_cons _ _ _ (der_33958 v h) (by intro d hd; cases hd)))
def cl_51402 : CNF.NClause := [(51,false),(68,false),(70,false),(69,true),(20,false)]
theorem der_51402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51402 :=
  CNF.rup_sound cl_51402 [cl_33960,cl_51401] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33960 v h) (hints_cons _ _ _ (der_51401 v h) (by intro d hd; cases hd)))
def cl_51403 : CNF.NClause := [(51,false),(67,false),(70,false),(69,true),(20,false)]
theorem der_51403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51403 :=
  CNF.rup_sound cl_51403 [cl_33962,cl_33908] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33962 v h) (hints_cons _ _ _ (der_33908 v h) (by intro d hd; cases hd)))
def cl_51404 : CNF.NClause := [(51,false),(69,true),(67,false),(70,false),(92,true)]
theorem der_51404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51404 :=
  CNF.rup_sound cl_51404 [cl_33963,cl_33934] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33963 v h) (hints_cons _ _ _ (der_33934 v h) (by intro d hd; cases hd)))
def cl_51405 : CNF.NClause := [(67,true),(68,false),(20,false),(51,false),(69,false)]
theorem der_51405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51405 :=
  CNF.rup_sound cl_51405 [cl_33967,cl_33913] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33967 v h) (hints_cons _ _ _ (der_33913 v h) (by intro d hd; cases hd)))
def cl_51406 : CNF.NClause := [(68,false),(67,true),(71,true),(51,false),(69,false)]
theorem der_51406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51406 :=
  CNF.rup_sound cl_51406 [cl_33968,cl_51405] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33968 v h) (hints_cons _ _ _ (der_51405 v h) (by intro d hd; cases hd)))
def cl_51408 : CNF.NClause := [(67,false),(92,true),(20,true),(51,false),(69,false)]
theorem der_51408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51408 :=
  CNF.rup_sound cl_51408 [cl_33970,cl_33955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33970 v h) (hints_cons _ _ _ (der_33955 v h) (by intro d hd; cases hd)))
def cl_51409 : CNF.NClause := [(68,true),(69,false),(67,true),(20,true),(51,false)]
theorem der_51409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51409 :=
  CNF.rup_sound cl_51409 [cl_33972,cl_51400] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33972 v h) (hints_cons _ _ _ (der_51400 v h) (by intro d hd; cases hd)))
def cl_51410 : CNF.NClause := [(68,false),(69,true),(67,false),(51,false),(70,true)]
theorem der_51410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51410 :=
  CNF.rup_sound cl_51410 [cl_33974,cl_51384] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33974 v h) (hints_cons _ _ _ (der_51384 v h) (by intro d hd; cases hd)))
def cl_51412 : CNF.NClause := [(67,false),(69,true),(51,false),(70,true),(20,false)]
theorem der_51412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51412 :=
  CNF.rup_sound cl_51412 [cl_33977,cl_51410] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33977 v h) (hints_cons _ _ _ (der_51410 v h) (by intro d hd; cases hd)))
def cl_51413 : CNF.NClause := [(67,false),(71,true),(92,true),(20,true),(51,false)]
theorem der_51413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51413 :=
  CNF.rup_sound cl_51413 [cl_33978,cl_51408] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33978 v h) (hints_cons _ _ _ (der_51408 v h) (by intro d hd; cases hd)))
def cl_51414 : CNF.NClause := [(70,true),(69,true),(51,false),(71,true),(20,false)]
theorem der_51414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51414 :=
  CNF.rup_sound cl_51414 [cl_33979,cl_51412] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33979 v h) (hints_cons _ _ _ (der_51412 v h) (by intro d hd; cases hd)))
def cl_51416 : CNF.NClause := [(90,false),(85,false),(50,false),(77,false),(71,true)]
theorem der_51416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51416 :=
  CNF.rup_sound cl_51416 [cl_33985,cl_49560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33985 v h) (hints_cons _ _ _ (der_49560 v h) (by intro d hd; cases hd)))
def cl_51418 : CNF.NClause := [(50,false),(85,false),(90,false),(71,true),(19,false)]
theorem der_51418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51418 :=
  CNF.rup_sound cl_51418 [cl_33996,cl_33994] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33996 v h) (hints_cons _ _ _ (der_33994 v h) (by intro d hd; cases hd)))
def cl_51420 : CNF.NClause := [(90,false),(74,false),(50,false),(77,false),(71,true)]
theorem der_51420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51420 :=
  CNF.rup_sound cl_51420 [cl_34001,cl_33999] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34001 v h) (hints_cons _ _ _ (der_33999 v h) (by intro d hd; cases hd)))
def cl_51421 : CNF.NClause := [(71,false),(77,false),(74,true),(90,false),(50,false)]
theorem der_51421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51421 :=
  CNF.rup_sound cl_51421 [cl_34004,cl_34002] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34004 v h) (hints_cons _ _ _ (der_34002 v h) (by intro d hd; cases hd)))
def cl_51422 : CNF.NClause := [(77,false),(63,false),(50,false),(71,true),(90,false)]
theorem der_51422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51422 :=
  CNF.rup_sound cl_51422 [cl_34006,cl_51416] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34006 v h) (hints_cons _ _ _ (der_51416 v h) (by intro d hd; cases hd)))
def cl_51423 : CNF.NClause := [(90,false),(77,false),(19,false),(50,false),(71,true)]
theorem der_51423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51423 :=
  CNF.rup_sound cl_51423 [cl_34007,cl_34005] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34007 v h) (hints_cons _ _ _ (der_34005 v h) (by intro d hd; cases hd)))
def cl_51424 : CNF.NClause := [(50,false),(71,true),(77,false),(90,false),(19,true)]
theorem der_51424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51424 :=
  CNF.rup_sound cl_51424 [cl_34008,cl_51422] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34008 v h) (hints_cons _ _ _ (der_51422 v h) (by intro d hd; cases hd)))
def cl_51425 : CNF.NClause := [(50,false),(90,false),(63,false),(19,true),(71,false)]
theorem der_51425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51425 :=
  CNF.rup_sound cl_51425 [cl_34009,cl_50714] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34009 v h) (hints_cons _ _ _ (der_50714 v h) (by intro d hd; cases hd)))
def cl_51426 : CNF.NClause := [(50,false),(90,false),(74,false),(71,true),(19,false)]
theorem der_51426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51426 :=
  CNF.rup_sound cl_51426 [cl_34013,cl_34011] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34013 v h) (hints_cons _ _ _ (der_34011 v h) (by intro d hd; cases hd)))
def cl_51427 : CNF.NClause := [(50,false),(63,true),(71,true),(74,false),(90,false)]
theorem der_51427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51427 :=
  CNF.rup_sound cl_51427 [cl_34014,cl_51426] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34014 v h) (hints_cons _ _ _ (der_51426 v h) (by intro d hd; cases hd)))
def cl_51428 : CNF.NClause := [(50,false),(63,false),(71,false),(90,false),(74,true)]
theorem der_51428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51428 :=
  CNF.rup_sound cl_51428 [cl_34015,cl_50714] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34015 v h) (hints_cons _ _ _ (der_50714 v h) (by intro d hd; cases hd)))
def cl_51431 : CNF.NClause := [(63,false),(74,true),(50,false),(90,false),(19,false)]
theorem der_51431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51431 :=
  CNF.rup_sound cl_51431 [cl_34018,cl_51428] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34018 v h) (hints_cons _ _ _ (der_51428 v h) (by intro d hd; cases hd)))
def cl_51432 : CNF.NClause := [(63,false),(74,true),(50,false),(71,true),(90,false)]
theorem der_51432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51432 :=
  CNF.rup_sound cl_51432 [cl_34019,cl_51422] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34019 v h) (hints_cons _ _ _ (der_51422 v h) (by intro d hd; cases hd)))
def cl_51433 : CNF.NClause := [(77,true),(50,false),(90,false),(19,false),(74,true)]
theorem der_51433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51433 :=
  CNF.rup_sound cl_51433 [cl_34020,cl_51431] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34020 v h) (hints_cons _ _ _ (der_51431 v h) (by intro d hd; cases hd)))
def cl_51434 : CNF.NClause := [(50,false),(77,true),(74,true),(90,false),(63,true)]
theorem der_51434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51434 :=
  CNF.rup_sound cl_51434 [cl_34021,cl_51433] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34021 v h) (hints_cons _ _ _ (der_51433 v h) (by intro d hd; cases hd)))
def cl_51435 : CNF.NClause := [(50,false),(63,true),(85,false),(74,false),(77,false)]
theorem der_51435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51435 :=
  CNF.rup_sound cl_51435 [cl_34025,cl_49560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34025 v h) (hints_cons _ _ _ (der_49560 v h) (by intro d hd; cases hd)))
def cl_51437 : CNF.NClause := [(85,false),(63,true),(50,false),(77,false),(71,true)]
theorem der_51437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51437 :=
  CNF.rup_sound cl_51437 [cl_34031,cl_49560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34031 v h) (hints_cons _ _ _ (der_49560 v h) (by intro d hd; cases hd)))
def cl_51438 : CNF.NClause := [(63,true),(74,false),(50,false),(19,false),(85,false)]
theorem der_51438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51438 :=
  CNF.rup_sound cl_51438 [cl_34037,cl_34033] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34037 v h) (hints_cons _ _ _ (der_34033 v h) (by intro d hd; cases hd)))
def cl_51439 : CNF.NClause := [(50,false),(63,true),(85,false),(74,false),(71,true)]
theorem der_51439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51439 :=
  CNF.rup_sound cl_51439 [cl_34038,cl_51435] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34038 v h) (hints_cons _ _ _ (der_51435 v h) (by intro d hd; cases hd)))
def cl_51440 : CNF.NClause := [(71,false),(85,false),(63,false),(50,false),(77,true)]
theorem der_51440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51440 :=
  CNF.rup_sound cl_51440 [cl_34039,cl_50713] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34039 v h) (hints_cons _ _ _ (der_50713 v h) (by intro d hd; cases hd)))
def cl_51441 : CNF.NClause := [(71,false),(63,true),(50,false),(85,false),(19,false)]
theorem der_51441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51441 :=
  CNF.rup_sound cl_51441 [cl_34040,cl_34033] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34040 v h) (hints_cons _ _ _ (der_34033 v h) (by intro d hd; cases hd)))
def cl_51442 : CNF.NClause := [(71,false),(74,true),(19,true),(50,false),(85,false)]
theorem der_51442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51442 :=
  CNF.rup_sound cl_51442 [cl_34041,cl_50713] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34041 v h) (hints_cons _ _ _ (der_50713 v h) (by intro d hd; cases hd)))
def cl_51443 : CNF.NClause := [(85,false),(63,false),(50,false),(77,true),(19,false)]
theorem der_51443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51443 :=
  CNF.rup_sound cl_51443 [cl_34042,cl_51440] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34042 v h) (hints_cons _ _ _ (der_51440 v h) (by intro d hd; cases hd)))
def cl_51444 : CNF.NClause := [(50,false),(63,false),(74,true),(85,false),(77,true)]
theorem der_51444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51444 :=
  CNF.rup_sound cl_51444 [cl_34043,cl_51440] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34043 v h) (hints_cons _ _ _ (der_51440 v h) (by intro d hd; cases hd)))
def cl_51445 : CNF.NClause := [(90,true),(85,false),(63,true),(50,false),(19,false)]
theorem der_51445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51445 :=
  CNF.rup_sound cl_51445 [cl_34044,cl_51438] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34044 v h) (hints_cons _ _ _ (der_51438 v h) (by intro d hd; cases hd)))
def cl_51446 : CNF.NClause := [(50,false),(63,false),(19,true),(77,false),(71,false)]
theorem der_51446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51446 :=
  CNF.rup_sound cl_51446 [cl_34045,cl_50714] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34045 v h) (hints_cons _ _ _ (der_50714 v h) (by intro d hd; cases hd)))
def cl_51447 : CNF.NClause := [(71,false),(50,false),(77,false),(74,false),(63,true)]
theorem der_51447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51447 :=
  CNF.rup_sound cl_51447 [cl_34047,cl_51435] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34047 v h) (hints_cons _ _ _ (der_51435 v h) (by intro d hd; cases hd)))
def cl_51448 : CNF.NClause := [(74,false),(50,false),(77,false),(71,true),(19,false)]
theorem der_51448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51448 :=
  CNF.rup_sound cl_51448 [cl_34050,cl_34048] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34050 v h) (hints_cons _ _ _ (der_34048 v h) (by intro d hd; cases hd)))
def cl_51449 : CNF.NClause := [(50,false),(71,true),(77,false),(19,true),(74,false)]
theorem der_51449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51449 :=
  CNF.rup_sound cl_51449 [cl_34051,cl_49560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34051 v h) (hints_cons _ _ _ (der_49560 v h) (by intro d hd; cases hd)))
def cl_51450 : CNF.NClause := [(71,false),(63,false),(77,false),(50,false),(74,true)]
theorem der_51450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51450 :=
  CNF.rup_sound cl_51450 [cl_34052,cl_32387] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34052 v h) (hints_cons _ _ _ (der_32387 v h) (by intro d hd; cases hd)))
def cl_51451 : CNF.NClause := [(71,false),(19,false),(50,false),(77,false),(74,true)]
theorem der_51451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51451 :=
  CNF.rup_sound cl_51451 [cl_34053,cl_51450] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34053 v h) (hints_cons _ _ _ (der_51450 v h) (by intro d hd; cases hd)))
def cl_51452 : CNF.NClause := [(71,false),(74,true),(19,true),(50,false),(77,false)]
theorem der_51452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51452 :=
  CNF.rup_sound cl_51452 [cl_34054,cl_51450] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34054 v h) (hints_cons _ _ _ (der_51450 v h) (by intro d hd; cases hd)))
def cl_51453 : CNF.NClause := [(77,false),(74,true),(19,true),(50,false),(63,false)]
theorem der_51453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51453 :=
  CNF.rup_sound cl_51453 [cl_34056,cl_49560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34056 v h) (hints_cons _ _ _ (der_49560 v h) (by intro d hd; cases hd)))
def cl_51454 : CNF.NClause := [(63,false),(19,true),(50,false),(71,false),(74,false)]
theorem der_51454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51454 :=
  CNF.rup_sound cl_51454 [cl_34058,cl_51425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34058 v h) (hints_cons _ _ _ (der_51425 v h) (by intro d hd; cases hd)))
def cl_51455 : CNF.NClause := [(71,false),(19,true),(50,false),(74,false),(77,true)]
theorem der_51455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51455 :=
  CNF.rup_sound cl_51455 [cl_34060,cl_51454] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34060 v h) (hints_cons _ _ _ (der_51454 v h) (by intro d hd; cases hd)))
def cl_51457 : CNF.NClause := [(85,true),(74,false),(63,false),(50,false),(71,true)]
theorem der_51457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51457 :=
  CNF.rup_sound cl_51457 [cl_34062,cl_34049] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34062 v h) (hints_cons _ _ _ (der_34049 v h) (by intro d hd; cases hd)))
def cl_51458 : CNF.NClause := [(50,false),(74,false),(71,true),(19,false),(90,true)]
theorem der_51458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51458 :=
  CNF.rup_sound cl_51458 [cl_34063,cl_51448] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34063 v h) (hints_cons _ _ _ (der_51448 v h) (by intro d hd; cases hd)))
def cl_51459 : CNF.NClause := [(63,true),(71,true),(19,true),(50,false),(74,false)]
theorem der_51459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51459 :=
  CNF.rup_sound cl_51459 [cl_34064,cl_51439] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34064 v h) (hints_cons _ _ _ (der_51439 v h) (by intro d hd; cases hd)))
def cl_51460 : CNF.NClause := [(85,true),(71,false),(63,false),(50,false),(74,true)]
theorem der_51460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51460 :=
  CNF.rup_sound cl_51460 [cl_34065,cl_50714] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34065 v h) (hints_cons _ _ _ (der_50714 v h) (by intro d hd; cases hd)))
def cl_51462 : CNF.NClause := [(85,true),(71,false),(50,false),(74,true),(77,true)]
theorem der_51462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51462 :=
  CNF.rup_sound cl_51462 [cl_34067,cl_51460] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34067 v h) (hints_cons _ _ _ (der_51460 v h) (by intro d hd; cases hd)))
def cl_51467 : CNF.NClause := [(102,true),(50,false),(44,false),(51,true),(32,false)]
theorem der_51467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51467 :=
  CNF.rup_sound cl_51467 [cl_23849,cl_38847] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23849 v h) (hints_cons _ _ _ (der_38847 v h) (by intro d hd; cases hd)))
def cl_51469 : CNF.NClause := [(102,true),(50,false),(44,false),(32,false),(57,false)]
theorem der_51469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51469 :=
  CNF.rup_sound cl_51469 [cl_23862,cl_38847] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23862 v h) (hints_cons _ _ _ (der_38847 v h) (by intro d hd; cases hd)))
def cl_51472 : CNF.NClause := [(119,true),(31,true),(44,true),(60,false),(48,false)]
theorem der_51472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51472 :=
  CNF.rup_sound cl_51472 [cl_23888,cl_49584] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23888 v h) (hints_cons _ _ _ (der_49584 v h) (by intro d hd; cases hd)))
def cl_51475 : CNF.NClause := [(32,false),(81,false),(66,true),(71,false),(87,false)]
theorem der_51475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51475 :=
  CNF.rup_sound cl_51475 [cl_34090,cl_34089] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34090 v h) (hints_cons _ _ _ (der_34089 v h) (by intro d hd; cases hd)))
def cl_51476 : CNF.NClause := [(32,false),(76,false),(71,false),(87,false),(66,true)]
theorem der_51476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51476 :=
  CNF.rup_sound cl_51476 [cl_34096,cl_34087] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34096 v h) (hints_cons _ _ _ (der_34087 v h) (by intro d hd; cases hd)))
def cl_51477 : CNF.NClause := [(32,false),(76,false),(71,true),(1,true),(87,false)]
theorem der_51477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51477 :=
  CNF.rup_sound cl_51477 [cl_34100,cl_43007] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34100 v h) (hints_cons _ _ _ (der_43007 v h) (by intro d hd; cases hd)))
def cl_51479 : CNF.NClause := [(76,true),(32,false),(71,true),(87,false),(66,false)]
theorem der_51479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51479 :=
  CNF.rup_sound cl_51479 [cl_34106,cl_34084] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34106 v h) (hints_cons _ _ _ (der_34084 v h) (by intro d hd; cases hd)))
def cl_51481 : CNF.NClause := [(76,true),(32,false),(71,true),(87,false),(81,true)]
theorem der_51481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51481 :=
  CNF.rup_sound cl_51481 [cl_34108,cl_51479] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34108 v h) (hints_cons _ _ _ (der_51479 v h) (by intro d hd; cases hd)))
def cl_51482 : CNF.NClause := [(71,false),(32,false),(81,false),(1,true),(86,false)]
theorem der_51482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51482 :=
  CNF.rup_sound cl_51482 [cl_34114,cl_34113] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34114 v h) (hints_cons _ _ _ (der_34113 v h) (by intro d hd; cases hd)))
def cl_51483 : CNF.NClause := [(32,false),(81,false),(1,true),(86,false),(66,false)]
theorem der_51483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51483 :=
  CNF.rup_sound cl_51483 [cl_34116,cl_34113] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34116 v h) (hints_cons _ _ _ (der_34113 v h) (by intro d hd; cases hd)))
def cl_51484 : CNF.NClause := [(32,false),(81,false),(1,true),(86,false),(66,true)]
theorem der_51484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51484 :=
  CNF.rup_sound cl_51484 [cl_34118,cl_51482] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34118 v h) (hints_cons _ _ _ (der_51482 v h) (by intro d hd; cases hd)))
def cl_51485 : CNF.NClause := [(32,false),(1,true),(86,false),(71,false),(66,true)]
theorem der_51485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51485 :=
  CNF.rup_sound cl_51485 [cl_34128,cl_51482] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34128 v h) (hints_cons _ _ _ (der_51482 v h) (by intro d hd; cases hd)))
def cl_51486 : CNF.NClause := [(32,false),(66,false),(86,false),(71,true),(81,true)]
theorem der_51486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51486 :=
  CNF.rup_sound cl_51486 [cl_34130,cl_34122] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34130 v h) (hints_cons _ _ _ (der_34122 v h) (by intro d hd; cases hd)))
def cl_51487 : CNF.NClause := [(32,false),(86,false),(71,true),(76,true),(81,true)]
theorem der_51487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51487 :=
  CNF.rup_sound cl_51487 [cl_34132,cl_34131] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34132 v h) (hints_cons _ _ _ (der_34131 v h) (by intro d hd; cases hd)))
def cl_51488 : CNF.NClause := [(32,false),(81,false),(66,true),(71,false),(76,false)]
theorem der_51488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51488 :=
  CNF.rup_sound cl_51488 [cl_34135,cl_34134] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34135 v h) (hints_cons _ _ _ (der_34134 v h) (by intro d hd; cases hd)))
def cl_51489 : CNF.NClause := [(32,false),(66,true),(81,false),(76,false),(1,false)]
theorem der_51489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51489 :=
  CNF.rup_sound cl_51489 [cl_34137,cl_34134] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34137 v h) (hints_cons _ _ _ (der_34134 v h) (by intro d hd; cases hd)))
def cl_51490 : CNF.NClause := [(32,false),(81,false),(1,true),(76,false),(66,true)]
theorem der_51490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51490 :=
  CNF.rup_sound cl_51490 [cl_34138,cl_51488] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34138 v h) (hints_cons _ _ _ (der_51488 v h) (by intro d hd; cases hd)))
def cl_51491 : CNF.NClause := [(32,false),(66,false),(81,false),(76,true),(1,false)]
theorem der_51491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51491 :=
  CNF.rup_sound cl_51491 [cl_34143,cl_34139] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34143 v h) (hints_cons _ _ _ (der_34139 v h) (by intro d hd; cases hd)))
def cl_51493 : CNF.NClause := [(32,false),(76,false),(71,false),(81,true),(1,false)]
theorem der_51493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51493 :=
  CNF.rup_sound cl_51493 [cl_34149,cl_34147] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34149 v h) (hints_cons _ _ _ (der_34147 v h) (by intro d hd; cases hd)))
def cl_51494 : CNF.NClause := [(32,false),(76,false),(66,false),(81,true),(1,false)]
theorem der_51494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51494 :=
  CNF.rup_sound cl_51494 [cl_34150,cl_34121] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34150 v h) (hints_cons _ _ _ (der_34121 v h) (by intro d hd; cases hd)))
def cl_51495 : CNF.NClause := [(87,true),(32,false),(76,false),(81,true),(1,false)]
theorem der_51495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51495 :=
  CNF.rup_sound cl_51495 [cl_34152,cl_51493] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34152 v h) (hints_cons _ _ _ (der_51493 v h) (by intro d hd; cases hd)))
def cl_51496 : CNF.NClause := [(32,false),(71,true),(76,false),(1,true),(66,true)]
theorem der_51496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51496 :=
  CNF.rup_sound cl_51496 [cl_34153,cl_51477] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34153 v h) (hints_cons _ _ _ (der_51477 v h) (by intro d hd; cases hd)))
def cl_51497 : CNF.NClause := [(32,false),(76,true),(1,false),(66,false),(71,true)]
theorem der_51497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51497 :=
  CNF.rup_sound cl_51497 [cl_34156,cl_51491] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34156 v h) (hints_cons _ _ _ (der_51491 v h) (by intro d hd; cases hd)))
def cl_51499 : CNF.NClause := [(76,true),(32,false),(71,true),(81,true),(66,true)]
theorem der_51499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51499 :=
  CNF.rup_sound cl_51499 [cl_34159,cl_51487] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34159 v h) (hints_cons _ _ _ (der_51487 v h) (by intro d hd; cases hd)))
def cl_51502 : CNF.NClause := [(57,false),(32,false),(50,true),(38,true),(102,true)]
theorem der_51502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51502 :=
  CNF.rup_sound cl_51502 [cl_23909,cl_42316] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23909 v h) (hints_cons _ _ _ (der_42316 v h) (by intro d hd; cases hd)))
def cl_51503 : CNF.NClause := [(50,false),(102,true),(51,false),(32,false),(38,true)]
theorem der_51503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51503 :=
  CNF.rup_sound cl_51503 [cl_23911,cl_38847] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23911 v h) (hints_cons _ _ _ (der_38847 v h) (by intro d hd; cases hd)))
def cl_51506 : CNF.NClause := [(14,false),(2,false),(21,false),(79,true),(8,true)]
theorem der_51506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51506 :=
  CNF.rup_sound cl_51506 [cl_23962,cl_50138] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23962 v h) (hints_cons _ _ _ (der_50138 v h) (by intro d hd; cases hd)))
def cl_51508 : CNF.NClause := [(8,true),(26,false),(14,false),(79,true),(21,true)]
theorem der_51508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51508 :=
  CNF.rup_sound cl_51508 [cl_23966,cl_49770] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23966 v h) (hints_cons _ _ _ (der_49770 v h) (by intro d hd; cases hd)))
def cl_51516 : CNF.NClause := [(17,false),(6,true),(20,false),(70,true),(14,true)]
theorem der_51516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51516 :=
  CNF.rup_sound cl_51516 [cl_24061,cl_50466] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24061 v h) (hints_cons _ _ _ (der_50466 v h) (by intro d hd; cases hd)))
def cl_51519 : CNF.NClause := [(19,false),(5,true),(27,false),(85,true),(12,false)]
theorem der_51519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51519 :=
  CNF.rup_sound cl_51519 [cl_34287,cl_49138] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34287 v h) (hints_cons _ _ _ (der_49138 v h) (by intro d hd; cases hd)))
def cl_51520 : CNF.NClause := [(27,false),(21,false),(19,false),(5,true),(85,true)]
theorem der_51520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51520 :=
  CNF.rup_sound cl_51520 [cl_24091,cl_50131] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24091 v h) (hints_cons _ _ _ (der_50131 v h) (by intro d hd; cases hd)))
def cl_51522 : CNF.NClause := [(19,false),(3,false),(85,true),(21,true),(12,false)]
theorem der_51522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51522 :=
  CNF.rup_sound cl_51522 [cl_24094,cl_30223] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24094 v h) (hints_cons _ _ _ (der_30223 v h) (by intro d hd; cases hd)))
def cl_51523 : CNF.NClause := [(12,false),(3,false),(5,true),(27,false),(85,true)]
theorem der_51523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51523 :=
  CNF.rup_sound cl_51523 [cl_24096,cl_51519] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24096 v h) (hints_cons _ _ _ (der_51519 v h) (by intro d hd; cases hd)))
def cl_51524 : CNF.NClause := [(19,false),(85,true),(12,false),(27,true),(3,false)]
theorem der_51524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51524 :=
  CNF.rup_sound cl_51524 [cl_24098,cl_51522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24098 v h) (hints_cons _ _ _ (der_51522 v h) (by intro d hd; cases hd)))
def cl_51526 : CNF.NClause := [(21,false),(12,false),(85,true),(19,true),(5,true)]
theorem der_51526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51526 :=
  CNF.rup_sound cl_51526 [cl_24100,cl_50158] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24100 v h) (hints_cons _ _ _ (der_50158 v h) (by intro d hd; cases hd)))
def cl_51527 : CNF.NClause := [(83,true),(23,false),(17,false),(5,true),(11,true)]
theorem der_51527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51527 :=
  CNF.rup_sound cl_51527 [cl_24105,cl_49512] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24105 v h) (hints_cons _ _ _ (der_49512 v h) (by intro d hd; cases hd)))
def cl_51528 : CNF.NClause := [(27,false),(21,false),(85,true),(5,true),(19,false)]
theorem der_51528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51528 :=
  CNF.rup_sound cl_51528 [cl_24113,cl_50212] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24113 v h) (hints_cons _ _ _ (der_50212 v h) (by intro d hd; cases hd)))
def cl_51529 : CNF.NClause := [(83,true),(17,false),(26,false),(23,false),(5,true)]
theorem der_51529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51529 :=
  CNF.rup_sound cl_51529 [cl_24128,cl_51527] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24128 v h) (hints_cons _ _ _ (der_51527 v h) (by intro d hd; cases hd)))
def cl_51530 : CNF.NClause := [(83,true),(17,false),(23,false),(5,true),(26,true)]
theorem der_51530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51530 :=
  CNF.rup_sound cl_51530 [cl_24136,cl_32023] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24136 v h) (hints_cons _ _ _ (der_32023 v h) (by intro d hd; cases hd)))
def cl_51532 : CNF.NClause := [(71,true),(1,false),(7,true),(26,true),(13,false)]
theorem der_51532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51532 :=
  CNF.rup_sound cl_51532 [cl_24165,cl_49685] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24165 v h) (hints_cons _ _ _ (der_49685 v h) (by intro d hd; cases hd)))
def cl_51534 : CNF.NClause := [(4,false),(29,true),(68,true),(20,true),(16,false)]
theorem der_51534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51534 :=
  CNF.rup_sound cl_51534 [cl_24180,cl_50185] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24180 v h) (hints_cons _ _ _ (der_50185 v h) (by intro d hd; cases hd)))
def cl_51535 : CNF.NClause := [(7,false),(26,false),(1,true),(71,true),(13,true)]
theorem der_51535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51535 :=
  CNF.rup_sound cl_51535 [cl_24214,cl_43719] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24214 v h) (hints_cons _ _ _ (der_43719 v h) (by intro d hd; cases hd)))
def cl_51540 : CNF.NClause := [(15,true),(12,false),(81,true),(1,true),(23,false)]
theorem der_51540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51540 :=
  CNF.rup_sound cl_51540 [cl_24246,cl_50419] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24246 v h) (hints_cons _ _ _ (der_50419 v h) (by intro d hd; cases hd)))
def cl_51541 : CNF.NClause := [(12,false),(81,true),(9,true),(15,false),(1,true)]
theorem der_51541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51541 :=
  CNF.rup_sound cl_51541 [cl_24247,cl_50008] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24247 v h) (hints_cons _ _ _ (der_50008 v h) (by intro d hd; cases hd)))
def cl_51542 : CNF.NClause := [(81,true),(9,false),(12,true),(23,true),(15,false)]
theorem der_51542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51542 :=
  CNF.rup_sound cl_51542 [cl_24254,cl_49792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24254 v h) (hints_cons _ _ _ (der_49792 v h) (by intro d hd; cases hd)))
def cl_51543 : CNF.NClause := [(83,true),(17,false),(26,false),(4,false),(5,true)]
theorem der_51543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51543 :=
  CNF.rup_sound cl_51543 [cl_24261,cl_51529] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24261 v h) (hints_cons _ _ _ (der_51529 v h) (by intro d hd; cases hd)))
def cl_51551 : CNF.NClause := [(27,false),(9,true),(2,true),(18,false),(69,true)]
theorem der_51551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51551 :=
  CNF.rup_sound cl_51551 [cl_24388,cl_50011] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24388 v h) (hints_cons _ _ _ (der_50011 v h) (by intro d hd; cases hd)))
def cl_51557 : CNF.NClause := [(27,true),(1,false),(8,false),(24,true),(76,true)]
theorem der_51557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51557 :=
  CNF.rup_sound cl_51557 [cl_24481,cl_49531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24481 v h) (hints_cons _ _ _ (der_49531 v h) (by intro d hd; cases hd)))
def cl_51559 : CNF.NClause := [(9,false),(10,true),(75,true),(16,false),(26,true)]
theorem der_51559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51559 :=
  CNF.rup_sound cl_51559 [cl_24500,cl_49972] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24500 v h) (hints_cons _ _ _ (der_49972 v h) (by intro d hd; cases hd)))
def cl_51561 : CNF.NClause := [(8,true),(1,false),(27,false),(76,true),(10,true)]
theorem der_51561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51561 :=
  CNF.rup_sound cl_51561 [cl_24518,cl_50190] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24518 v h) (hints_cons _ _ _ (der_50190 v h) (by intro d hd; cases hd)))
def cl_51562 : CNF.NClause := [(27,true),(4,true),(15,false),(78,true),(6,false)]
theorem der_51562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51562 :=
  CNF.rup_sound cl_51562 [cl_24522,cl_49545] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24522 v h) (hints_cons _ _ _ (der_49545 v h) (by intro d hd; cases hd)))
def cl_51568 : CNF.NClause := [(71,true),(19,false),(26,true),(13,true),(1,false)]
theorem der_51568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51568 :=
  CNF.rup_sound cl_51568 [cl_24633,cl_42582] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24633 v h) (hints_cons _ _ _ (der_42582 v h) (by intro d hd; cases hd)))
def cl_51569 : CNF.NClause := [(27,false),(9,true),(11,true),(2,false),(69,true)]
theorem der_51569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51569 :=
  CNF.rup_sound cl_51569 [cl_24647,cl_47172] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24647 v h) (hints_cons _ _ _ (der_47172 v h) (by intro d hd; cases hd)))
def cl_51571 : CNF.NClause := [(69,false),(73,false),(91,true),(86,false),(49,false)]
theorem der_51571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51571 :=
  CNF.rup_sound cl_51571 [cl_34288,cl_42308] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34288 v h) (hints_cons _ _ _ (der_42308 v h) (by intro d hd; cases hd)))
def cl_51572 : CNF.NClause := [(88,false),(31,false),(91,true),(90,true),(87,true)]
theorem der_51572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51572 :=
  CNF.rup_sound cl_51572 [cl_34290,cl_50057] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34290 v h) (hints_cons _ _ _ (der_50057 v h) (by intro d hd; cases hd)))
def cl_51575 : CNF.NClause := [(65,false),(44,false),(78,false),(71,false),(84,true)]
theorem der_51575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51575 :=
  CNF.rup_sound cl_51575 [cl_34300,cl_47225] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34300 v h) (hints_cons _ _ _ (der_47225 v h) (by intro d hd; cases hd)))
def cl_51576 : CNF.NClause := [(66,false),(47,false),(75,false),(16,true),(89,false)]
theorem der_51576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51576 :=
  CNF.rup_sound cl_51576 [cl_34303,cl_32105] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34303 v h) (hints_cons _ _ _ (der_32105 v h) (by intro d hd; cases hd)))
def cl_51577 : CNF.NClause := [(72,false),(45,false),(63,false),(70,false),(86,true)]
theorem der_51577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51577 :=
  CNF.rup_sound cl_51577 [cl_34306,cl_49540] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34306 v h) (hints_cons _ _ _ (der_49540 v h) (by intro d hd; cases hd)))
def cl_51578 : CNF.NClause := [(66,false),(21,true),(52,false),(88,false),(73,false)]
theorem der_51578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51578 :=
  CNF.rup_sound cl_51578 [cl_34307,cl_46980] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34307 v h) (hints_cons _ _ _ (der_46980 v h) (by intro d hd; cases hd)))
def cl_51579 : CNF.NClause := [(66,false),(52,false),(21,true),(85,false),(73,false)]
theorem der_51579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51579 :=
  CNF.rup_sound cl_51579 [cl_34308,cl_40159] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34308 v h) (hints_cons _ _ _ (der_40159 v h) (by intro d hd; cases hd)))
def cl_51581 : CNF.NClause := [(65,false),(71,false),(44,false),(72,false),(84,true)]
theorem der_51581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51581 :=
  CNF.rup_sound cl_51581 [cl_34317,cl_50712] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34317 v h) (hints_cons _ _ _ (der_50712 v h) (by intro d hd; cases hd)))
def cl_51582 : CNF.NClause := [(75,false),(53,false),(67,false),(86,true),(22,true)]
theorem der_51582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51582 :=
  CNF.rup_sound cl_51582 [cl_34320,cl_34318] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34320 v h) (hints_cons _ _ _ (der_34318 v h) (by intro d hd; cases hd)))
def cl_51583 : CNF.NClause := [(70,true),(86,false),(63,false),(79,false),(45,false)]
theorem der_51583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51583 :=
  CNF.rup_sound cl_51583 [cl_34329,cl_50736] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34329 v h) (hints_cons _ _ _ (der_50736 v h) (by intro d hd; cases hd)))
def cl_51584 : CNF.NClause := [(86,false),(72,false),(63,false),(45,false),(79,true)]
theorem der_51584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51584 :=
  CNF.rup_sound cl_51584 [cl_34330,cl_49540] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34330 v h) (hints_cons _ _ _ (der_49540 v h) (by intro d hd; cases hd)))
def cl_51585 : CNF.NClause := [(70,true),(86,false),(45,false),(63,false),(72,true)]
theorem der_51585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51585 :=
  CNF.rup_sound cl_51585 [cl_34331,cl_50736] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34331 v h) (hints_cons _ _ _ (der_50736 v h) (by intro d hd; cases hd)))
def cl_51587 : CNF.NClause := [(45,false),(79,false),(72,true),(63,false),(70,true)]
theorem der_51587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51587 :=
  CNF.rup_sound cl_51587 [cl_34333,cl_49539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34333 v h) (hints_cons _ _ _ (der_49539 v h) (by intro d hd; cases hd)))
def cl_51588 : CNF.NClause := [(89,true),(72,false),(63,false),(86,true),(45,false)]
theorem der_51588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51588 :=
  CNF.rup_sound cl_51588 [cl_34334,cl_49540] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34334 v h) (hints_cons _ _ _ (der_49540 v h) (by intro d hd; cases hd)))
def cl_51589 : CNF.NClause := [(89,false),(86,false),(14,true),(45,false),(79,false)]
theorem der_51589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51589 :=
  CNF.rup_sound cl_51589 [cl_34336,cl_47228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34336 v h) (hints_cons _ _ _ (der_47228 v h) (by intro d hd; cases hd)))
def cl_51590 : CNF.NClause := [(89,false),(86,false),(72,false),(14,true),(45,false)]
theorem der_51590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51590 :=
  CNF.rup_sound cl_51590 [cl_34337,cl_49538] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34337 v h) (hints_cons _ _ _ (der_49538 v h) (by intro d hd; cases hd)))
def cl_51591 : CNF.NClause := [(70,true),(89,false),(86,false),(14,true),(45,false)]
theorem der_51591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51591 :=
  CNF.rup_sound cl_51591 [cl_34338,cl_51590] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34338 v h) (hints_cons _ _ _ (der_51590 v h) (by intro d hd; cases hd)))
def cl_51592 : CNF.NClause := [(72,false),(45,false),(14,true),(79,false),(89,false)]
theorem der_51592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51592 :=
  CNF.rup_sound cl_51592 [cl_34339,cl_51589] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34339 v h) (hints_cons _ _ _ (der_51589 v h) (by intro d hd; cases hd)))
def cl_51593 : CNF.NClause := [(89,false),(72,true),(14,true),(45,false),(79,false)]
theorem der_51593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51593 :=
  CNF.rup_sound cl_51593 [cl_34340,cl_47228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34340 v h) (hints_cons _ _ _ (der_47228 v h) (by intro d hd; cases hd)))
def cl_51594 : CNF.NClause := [(70,true),(89,false),(14,true),(45,false),(72,false)]
theorem der_51594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51594 :=
  CNF.rup_sound cl_51594 [cl_34341,cl_49538] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34341 v h) (hints_cons _ _ _ (der_49538 v h) (by intro d hd; cases hd)))
def cl_51595 : CNF.NClause := [(89,false),(70,true),(14,true),(45,false),(72,true)]
theorem der_51595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51595 :=
  CNF.rup_sound cl_51595 [cl_34342,cl_51593] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34342 v h) (hints_cons _ _ _ (der_51593 v h) (by intro d hd; cases hd)))
def cl_51596 : CNF.NClause := [(70,true),(45,false),(79,false),(86,false),(14,true)]
theorem der_51596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51596 :=
  CNF.rup_sound cl_51596 [cl_34344,cl_51583] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34344 v h) (hints_cons _ _ _ (der_51583 v h) (by intro d hd; cases hd)))
def cl_51597 : CNF.NClause := [(70,true),(86,false),(14,true),(45,false),(72,false)]
theorem der_51597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51597 :=
  CNF.rup_sound cl_51597 [cl_34345,cl_50736] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34345 v h) (hints_cons _ _ _ (der_50736 v h) (by intro d hd; cases hd)))
def cl_51598 : CNF.NClause := [(70,true),(45,false),(86,false),(79,true),(14,true)]
theorem der_51598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51598 :=
  CNF.rup_sound cl_51598 [cl_34346,cl_51591] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34346 v h) (hints_cons _ _ _ (der_51591 v h) (by intro d hd; cases hd)))
def cl_51600 : CNF.NClause := [(89,true),(70,true),(14,true),(45,false),(79,false)]
theorem der_51600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51600 :=
  CNF.rup_sound cl_51600 [cl_34348,cl_51596] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34348 v h) (hints_cons _ _ _ (der_51596 v h) (by intro d hd; cases hd)))
def cl_51602 : CNF.NClause := [(89,true),(70,true),(86,true),(14,true),(45,false)]
theorem der_51602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51602 :=
  CNF.rup_sound cl_51602 [cl_34350,cl_50738] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34350 v h) (hints_cons _ _ _ (der_50738 v h) (by intro d hd; cases hd)))
def cl_51603 : CNF.NClause := [(68,true),(84,false),(47,false),(89,false),(66,false)]
theorem der_51603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51603 :=
  CNF.rup_sound cl_51603 [cl_34353,cl_32026] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34353 v h) (hints_cons _ _ _ (der_32026 v h) (by intro d hd; cases hd)))
def cl_51607 : CNF.NClause := [(68,true),(84,false),(47,false),(77,false),(66,false)]
theorem der_51607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51607 :=
  CNF.rup_sound cl_51607 [cl_34359,cl_32030] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34359 v h) (hints_cons _ _ _ (der_32030 v h) (by intro d hd; cases hd)))
def cl_51609 : CNF.NClause := [(68,true),(84,false),(47,false),(66,false),(16,false)]
theorem der_51609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51609 :=
  CNF.rup_sound cl_51609 [cl_34361,cl_51607] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34361 v h) (hints_cons _ _ _ (der_51607 v h) (by intro d hd; cases hd)))
def cl_51610 : CNF.NClause := [(68,true),(47,false),(77,false),(66,false),(16,false)]
theorem der_51610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51610 :=
  CNF.rup_sound cl_51610 [cl_34363,cl_51607] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34363 v h) (hints_cons _ _ _ (der_51607 v h) (by intro d hd; cases hd)))
def cl_51611 : CNF.NClause := [(68,true),(66,false),(47,false),(77,true),(16,false)]
theorem der_51611 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51611 :=
  CNF.rup_sound cl_51611 [cl_34365,cl_51609] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34365 v h) (hints_cons _ _ _ (der_51609 v h) (by intro d hd; cases hd)))
def cl_51612 : CNF.NClause := [(68,true),(84,false),(16,true),(47,false),(89,false)]
theorem der_51612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51612 :=
  CNF.rup_sound cl_51612 [cl_34368,cl_32026] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34368 v h) (hints_cons _ _ _ (der_32026 v h) (by intro d hd; cases hd)))
def cl_51615 : CNF.NClause := [(89,false),(68,true),(16,true),(47,false),(84,true)]
theorem der_51615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51615 :=
  CNF.rup_sound cl_51615 [cl_34372,cl_49547] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34372 v h) (hints_cons _ _ _ (der_49547 v h) (by intro d hd; cases hd)))
def cl_51620 : CNF.NClause := [(68,true),(47,false),(77,false),(84,true),(16,true)]
theorem der_51620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51620 :=
  CNF.rup_sound cl_51620 [cl_34378,cl_50565] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34378 v h) (hints_cons _ _ _ (der_50565 v h) (by intro d hd; cases hd)))
def cl_51621 : CNF.NClause := [(77,true),(47,false),(68,true),(75,false),(16,true)]
theorem der_51621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51621 :=
  CNF.rup_sound cl_51621 [cl_34379,cl_50566] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34379 v h) (hints_cons _ _ _ (der_50566 v h) (by intro d hd; cases hd)))
def cl_51622 : CNF.NClause := [(47,false),(68,true),(84,true),(16,true),(66,true)]
theorem der_51622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51622 :=
  CNF.rup_sound cl_51622 [cl_34380,cl_51620] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34380 v h) (hints_cons _ _ _ (der_51620 v h) (by intro d hd; cases hd)))
def cl_51623 : CNF.NClause := [(68,true),(77,false),(84,false),(47,false),(89,false)]
theorem der_51623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51623 :=
  CNF.rup_sound cl_51623 [cl_34382,cl_34381] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34382 v h) (hints_cons _ _ _ (der_34381 v h) (by intro d hd; cases hd)))
def cl_51624 : CNF.NClause := [(68,true),(84,false),(47,false),(75,false),(89,false)]
theorem der_51624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51624 :=
  CNF.rup_sound cl_51624 [cl_34383,cl_34381] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34383 v h) (hints_cons _ _ _ (der_34381 v h) (by intro d hd; cases hd)))
def cl_51626 : CNF.NClause := [(68,true),(77,false),(47,false),(75,false),(89,false)]
theorem der_51626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51626 :=
  CNF.rup_sound cl_51626 [cl_34386,cl_34381] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34386 v h) (hints_cons _ _ _ (der_34381 v h) (by intro d hd; cases hd)))
def cl_51627 : CNF.NClause := [(77,false),(66,true),(47,false),(89,false),(68,false)]
theorem der_51627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51627 :=
  CNF.rup_sound cl_51627 [cl_34387,cl_49547] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34387 v h) (hints_cons _ _ _ (der_49547 v h) (by intro d hd; cases hd)))
def cl_51628 : CNF.NClause := [(68,true),(77,true),(75,false),(89,false),(47,false)]
theorem der_51628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51628 :=
  CNF.rup_sound cl_51628 [cl_34389,cl_51624] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34389 v h) (hints_cons _ _ _ (der_51624 v h) (by intro d hd; cases hd)))
def cl_51629 : CNF.NClause := [(68,true),(47,false),(89,false),(77,true),(16,false)]
theorem der_51629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51629 :=
  CNF.rup_sound cl_51629 [cl_34391,cl_51628] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34391 v h) (hints_cons _ _ _ (der_51628 v h) (by intro d hd; cases hd)))
def cl_51630 : CNF.NClause := [(68,true),(84,false),(77,false),(47,false),(75,false)]
theorem der_51630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51630 :=
  CNF.rup_sound cl_51630 [cl_34392,cl_51626] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34392 v h) (hints_cons _ _ _ (der_51626 v h) (by intro d hd; cases hd)))
def cl_51631 : CNF.NClause := [(68,true),(84,false),(77,false),(66,true),(47,false)]
theorem der_51631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51631 :=
  CNF.rup_sound cl_51631 [cl_34394,cl_51630] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34394 v h) (hints_cons _ _ _ (der_51630 v h) (by intro d hd; cases hd)))
def cl_51634 : CNF.NClause := [(68,true),(84,false),(75,true),(66,true),(47,false)]
theorem der_51634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51634 :=
  CNF.rup_sound cl_51634 [cl_34398,cl_51631] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34398 v h) (hints_cons _ _ _ (der_51631 v h) (by intro d hd; cases hd)))
def cl_51636 : CNF.NClause := [(75,false),(68,false),(47,false),(16,false),(84,true)]
theorem der_51636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51636 :=
  CNF.rup_sound cl_51636 [cl_34403,cl_34388] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34403 v h) (hints_cons _ _ _ (der_34388 v h) (by intro d hd; cases hd)))
def cl_51639 : CNF.NClause := [(68,true),(75,true),(66,true),(47,false),(89,true)]
theorem der_51639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51639 :=
  CNF.rup_sound cl_51639 [cl_34406,cl_34402] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34406 v h) (hints_cons _ _ _ (der_34402 v h) (by intro d hd; cases hd)))
def cl_51640 : CNF.NClause := [(73,false),(67,false),(52,false),(79,true),(21,false)]
theorem der_51640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51640 :=
  CNF.rup_sound cl_51640 [cl_34414,cl_34410] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34414 v h) (hints_cons _ _ _ (der_34410 v h) (by intro d hd; cases hd)))
def cl_51642 : CNF.NClause := [(84,false),(75,false),(89,false),(16,true),(47,false)]
theorem der_51642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51642 :=
  CNF.rup_sound cl_51642 [cl_34417,cl_32105] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34417 v h) (hints_cons _ _ _ (der_32105 v h) (by intro d hd; cases hd)))
def cl_51643 : CNF.NClause := [(77,false),(47,false),(84,true),(89,false),(75,false)]
theorem der_51643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51643 :=
  CNF.rup_sound cl_51643 [cl_34418,cl_51626] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34418 v h) (hints_cons _ _ _ (der_51626 v h) (by intro d hd; cases hd)))
def cl_51644 : CNF.NClause := [(89,false),(47,false),(75,false),(84,true),(16,true)]
theorem der_51644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51644 :=
  CNF.rup_sound cl_51644 [cl_34419,cl_49547] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34419 v h) (hints_cons _ _ _ (der_49547 v h) (by intro d hd; cases hd)))
def cl_51645 : CNF.NClause := [(84,false),(66,true),(47,false),(77,false),(75,false)]
theorem der_51645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51645 :=
  CNF.rup_sound cl_51645 [cl_34420,cl_51630] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34420 v h) (hints_cons _ _ _ (der_51630 v h) (by intro d hd; cases hd)))
def cl_51646 : CNF.NClause := [(84,false),(75,false),(16,true),(47,false),(66,true)]
theorem der_51646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51646 :=
  CNF.rup_sound cl_51646 [cl_34421,cl_51645] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34421 v h) (hints_cons _ _ _ (der_51645 v h) (by intro d hd; cases hd)))
def cl_51647 : CNF.NClause := [(77,false),(66,true),(47,false),(75,false),(84,true)]
theorem der_51647 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51647 :=
  CNF.rup_sound cl_51647 [cl_34422,cl_51643] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34422 v h) (hints_cons _ _ _ (der_51643 v h) (by intro d hd; cases hd)))
def cl_51648 : CNF.NClause := [(77,true),(16,true),(47,false),(75,false),(84,true)]
theorem der_51648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51648 :=
  CNF.rup_sound cl_51648 [cl_34423,cl_51621] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34423 v h) (hints_cons _ _ _ (der_51621 v h) (by intro d hd; cases hd)))
def cl_51649 : CNF.NClause := [(67,false),(52,false),(88,false),(85,false),(66,true)]
theorem der_51649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51649 :=
  CNF.rup_sound cl_51649 [cl_34428,cl_34424] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34428 v h) (hints_cons _ _ _ (der_34424 v h) (by intro d hd; cases hd)))
def cl_51650 : CNF.NClause := [(67,true),(21,true),(52,false),(88,false),(85,false)]
theorem der_51650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51650 :=
  CNF.rup_sound cl_51650 [cl_34429,cl_34427] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34429 v h) (hints_cons _ _ _ (der_34427 v h) (by intro d hd; cases hd)))
def cl_51651 : CNF.NClause := [(67,false),(79,false),(88,false),(66,true),(52,false)]
theorem der_51651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51651 :=
  CNF.rup_sound cl_51651 [cl_34432,cl_34424] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34432 v h) (hints_cons _ _ _ (der_34424 v h) (by intro d hd; cases hd)))
def cl_51652 : CNF.NClause := [(67,true),(88,false),(79,false),(21,true),(52,false)]
theorem der_51652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51652 :=
  CNF.rup_sound cl_51652 [cl_34433,cl_34431] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34433 v h) (hints_cons _ _ _ (der_34431 v h) (by intro d hd; cases hd)))
def cl_51653 : CNF.NClause := [(73,false),(66,true),(67,false),(52,false),(88,false)]
theorem der_51653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51653 :=
  CNF.rup_sound cl_51653 [cl_34434,cl_51651] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34434 v h) (hints_cons _ _ _ (der_51651 v h) (by intro d hd; cases hd)))
def cl_51654 : CNF.NClause := [(88,false),(73,false),(21,true),(52,false),(79,true)]
theorem der_51654 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51654 :=
  CNF.rup_sound cl_51654 [cl_34435,cl_51578] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34435 v h) (hints_cons _ _ _ (der_51578 v h) (by intro d hd; cases hd)))
def cl_51655 : CNF.NClause := [(85,true),(88,false),(67,false),(52,false),(66,true)]
theorem der_51655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51655 :=
  CNF.rup_sound cl_51655 [cl_34436,cl_51651] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34436 v h) (hints_cons _ _ _ (der_51651 v h) (by intro d hd; cases hd)))
def cl_51656 : CNF.NClause := [(67,false),(79,false),(52,false),(85,false),(66,true)]
theorem der_51656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51656 :=
  CNF.rup_sound cl_51656 [cl_34439,cl_51649] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34439 v h) (hints_cons _ _ _ (der_51649 v h) (by intro d hd; cases hd)))
def cl_51657 : CNF.NClause := [(79,false),(21,true),(52,false),(85,false),(88,true)]
theorem der_51657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51657 :=
  CNF.rup_sound cl_51657 [cl_34440,cl_40159] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34440 v h) (hints_cons _ _ _ (der_40159 v h) (by intro d hd; cases hd)))
def cl_51659 : CNF.NClause := [(67,false),(73,true),(52,false),(79,false),(66,true)]
theorem der_51659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51659 :=
  CNF.rup_sound cl_51659 [cl_34445,cl_51656] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34445 v h) (hints_cons _ _ _ (der_51656 v h) (by intro d hd; cases hd)))
def cl_51660 : CNF.NClause := [(67,false),(73,true),(52,false),(66,true),(88,true)]
theorem der_51660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51660 :=
  CNF.rup_sound cl_51660 [cl_34449,cl_51659] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34449 v h) (hints_cons _ _ _ (der_51659 v h) (by intro d hd; cases hd)))
def cl_51661 : CNF.NClause := [(88,false),(44,false),(78,false),(84,false),(13,true)]
theorem der_51661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51661 :=
  CNF.rup_sound cl_51661 [cl_34451,cl_42957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34451 v h) (hints_cons _ _ _ (der_42957 v h) (by intro d hd; cases hd)))
def cl_51662 : CNF.NClause := [(84,false),(65,true),(88,false),(13,true),(44,false)]
theorem der_51662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51662 :=
  CNF.rup_sound cl_51662 [cl_34455,cl_34454] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34455 v h) (hints_cons _ _ _ (der_34454 v h) (by intro d hd; cases hd)))
def cl_51663 : CNF.NClause := [(88,false),(65,true),(78,false),(13,true),(44,false)]
theorem der_51663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51663 :=
  CNF.rup_sound cl_51663 [cl_34459,cl_34458] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34459 v h) (hints_cons _ _ _ (der_34458 v h) (by intro d hd; cases hd)))
def cl_51664 : CNF.NClause := [(88,false),(71,false),(13,true),(44,false),(72,false)]
theorem der_51664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51664 :=
  CNF.rup_sound cl_51664 [cl_34460,cl_50712] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34460 v h) (hints_cons _ _ _ (der_50712 v h) (by intro d hd; cases hd)))
def cl_51665 : CNF.NClause := [(88,false),(65,true),(72,false),(13,true),(44,false)]
theorem der_51665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51665 :=
  CNF.rup_sound cl_51665 [cl_34461,cl_51664] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34461 v h) (hints_cons _ _ _ (der_51664 v h) (by intro d hd; cases hd)))
def cl_51667 : CNF.NClause := [(88,false),(44,false),(71,true),(65,true),(13,true)]
theorem der_51667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51667 :=
  CNF.rup_sound cl_51667 [cl_34463,cl_51665] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34463 v h) (hints_cons _ _ _ (der_51665 v h) (by intro d hd; cases hd)))
def cl_51668 : CNF.NClause := [(84,false),(13,true),(44,false),(78,false),(72,false)]
theorem der_51668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51668 :=
  CNF.rup_sound cl_51668 [cl_34464,cl_42957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34464 v h) (hints_cons _ _ _ (der_42957 v h) (by intro d hd; cases hd)))
def cl_51669 : CNF.NClause := [(71,false),(78,false),(13,true),(44,false),(84,false)]
theorem der_51669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51669 :=
  CNF.rup_sound cl_51669 [cl_34465,cl_42957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34465 v h) (hints_cons _ _ _ (der_42957 v h) (by intro d hd; cases hd)))
def cl_51670 : CNF.NClause := [(78,false),(44,false),(13,true),(71,true),(84,false)]
theorem der_51670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51670 :=
  CNF.rup_sound cl_51670 [cl_34466,cl_42957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34466 v h) (hints_cons _ _ _ (der_42957 v h) (by intro d hd; cases hd)))
def cl_51671 : CNF.NClause := [(71,false),(84,false),(13,true),(44,false),(72,false)]
theorem der_51671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51671 :=
  CNF.rup_sound cl_51671 [cl_34467,cl_49563] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34467 v h) (hints_cons _ _ _ (der_49563 v h) (by intro d hd; cases hd)))
def cl_51674 : CNF.NClause := [(71,false),(13,true),(44,false),(78,false),(72,true)]
theorem der_51674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51674 :=
  CNF.rup_sound cl_51674 [cl_34473,cl_47225] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34473 v h) (hints_cons _ _ _ (der_47225 v h) (by intro d hd; cases hd)))
def cl_51675 : CNF.NClause := [(65,true),(72,true),(13,true),(44,false),(78,false)]
theorem der_51675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51675 :=
  CNF.rup_sound cl_51675 [cl_34474,cl_51674] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34474 v h) (hints_cons _ _ _ (der_51674 v h) (by intro d hd; cases hd)))
def cl_51676 : CNF.NClause := [(71,false),(72,false),(13,true),(44,false),(84,true)]
theorem der_51676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51676 :=
  CNF.rup_sound cl_51676 [cl_34475,cl_49563] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34475 v h) (hints_cons _ _ _ (der_49563 v h) (by intro d hd; cases hd)))
def cl_51678 : CNF.NClause := [(72,true),(44,false),(71,true),(65,true),(13,true)]
theorem der_51678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51678 :=
  CNF.rup_sound cl_51678 [cl_34477,cl_51675] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34477 v h) (hints_cons _ _ _ (der_51675 v h) (by intro d hd; cases hd)))
def cl_51679 : CNF.NClause := [(65,true),(91,false),(86,false),(49,false),(69,false)]
theorem der_51679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51679 :=
  CNF.rup_sound cl_51679 [cl_34480,cl_49716] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34480 v h) (hints_cons _ _ _ (der_49716 v h) (by intro d hd; cases hd)))
def cl_51681 : CNF.NClause := [(65,true),(91,false),(73,false),(49,false),(69,true)]
theorem der_51681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51681 :=
  CNF.rup_sound cl_51681 [cl_34484,cl_49712] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34484 v h) (hints_cons _ _ _ (der_49712 v h) (by intro d hd; cases hd)))
def cl_51685 : CNF.NClause := [(65,true),(86,true),(77,false),(49,false),(18,false)]
theorem der_51685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51685 :=
  CNF.rup_sound cl_51685 [cl_34495,cl_34493] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34495 v h) (hints_cons _ _ _ (der_34493 v h) (by intro d hd; cases hd)))
def cl_51691 : CNF.NClause := [(88,false),(71,false),(44,false),(78,false),(72,true)]
theorem der_51691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51691 :=
  CNF.rup_sound cl_51691 [cl_34508,cl_47225] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34508 v h) (hints_cons _ _ _ (der_47225 v h) (by intro d hd; cases hd)))
def cl_51694 : CNF.NClause := [(88,false),(78,true),(44,false),(71,false),(65,true)]
theorem der_51694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51694 :=
  CNF.rup_sound cl_51694 [cl_34512,cl_34510] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34512 v h) (hints_cons _ _ _ (der_34510 v h) (by intro d hd; cases hd)))
def cl_51695 : CNF.NClause := [(88,false),(78,true),(44,false),(65,true),(84,true)]
theorem der_51695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51695 :=
  CNF.rup_sound cl_51695 [cl_34513,cl_51694] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34513 v h) (hints_cons _ _ _ (der_51694 v h) (by intro d hd; cases hd)))
def cl_51696 : CNF.NClause := [(65,true),(84,false),(78,false),(71,false),(44,false)]
theorem der_51696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51696 :=
  CNF.rup_sound cl_51696 [cl_34514,cl_49673] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34514 v h) (hints_cons _ _ _ (der_49673 v h) (by intro d hd; cases hd)))
def cl_51697 : CNF.NClause := [(65,true),(72,false),(78,false),(44,false),(84,false)]
theorem der_51697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51697 :=
  CNF.rup_sound cl_51697 [cl_34515,cl_51696] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34515 v h) (hints_cons _ _ _ (der_51696 v h) (by intro d hd; cases hd)))
def cl_51699 : CNF.NClause := [(78,true),(72,false),(44,false),(84,false),(71,false)]
theorem der_51699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51699 :=
  CNF.rup_sound cl_51699 [cl_34518,cl_34502] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34518 v h) (hints_cons _ _ _ (der_34502 v h) (by intro d hd; cases hd)))
def cl_51700 : CNF.NClause := [(78,true),(72,false),(44,false),(84,false),(65,true)]
theorem der_51700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51700 :=
  CNF.rup_sound cl_51700 [cl_34519,cl_51699] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34519 v h) (hints_cons _ _ _ (der_51699 v h) (by intro d hd; cases hd)))
def cl_51701 : CNF.NClause := [(65,true),(84,false),(71,false),(72,true),(44,false)]
theorem der_51701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51701 :=
  CNF.rup_sound cl_51701 [cl_34520,cl_51696] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34520 v h) (hints_cons _ _ _ (der_51696 v h) (by intro d hd; cases hd)))
def cl_51703 : CNF.NClause := [(71,false),(72,false),(78,false),(84,true),(44,false)]
theorem der_51703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51703 :=
  CNF.rup_sound cl_51703 [cl_34522,cl_34506] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34522 v h) (hints_cons _ _ _ (der_34506 v h) (by intro d hd; cases hd)))
def cl_51705 : CNF.NClause := [(65,true),(78,false),(71,false),(72,true),(44,false)]
theorem der_51705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51705 :=
  CNF.rup_sound cl_51705 [cl_34524,cl_49673] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34524 v h) (hints_cons _ _ _ (der_49673 v h) (by intro d hd; cases hd)))
def cl_51707 : CNF.NClause := [(72,false),(44,false),(71,false),(65,true),(84,true)]
theorem der_51707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51707 :=
  CNF.rup_sound cl_51707 [cl_34526,cl_51703] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34526 v h) (hints_cons _ _ _ (der_51703 v h) (by intro d hd; cases hd)))
def cl_51711 : CNF.NClause := [(65,true),(91,false),(49,false),(77,false),(86,false)]
theorem der_51711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51711 :=
  CNF.rup_sound cl_51711 [cl_34532,cl_34530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34532 v h) (hints_cons _ _ _ (der_34530 v h) (by intro d hd; cases hd)))
def cl_51712 : CNF.NClause := [(73,false),(69,false),(77,true),(49,false),(86,false)]
theorem der_51712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51712 :=
  CNF.rup_sound cl_51712 [cl_34533,cl_51571] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34533 v h) (hints_cons _ _ _ (der_51571 v h) (by intro d hd; cases hd)))
def cl_51713 : CNF.NClause := [(65,true),(91,false),(73,false),(86,false),(49,false)]
theorem der_51713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51713 :=
  CNF.rup_sound cl_51713 [cl_34534,cl_42308] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34534 v h) (hints_cons _ _ _ (der_42308 v h) (by intro d hd; cases hd)))
def cl_51714 : CNF.NClause := [(65,true),(91,false),(49,false),(86,false),(77,true)]
theorem der_51714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51714 :=
  CNF.rup_sound cl_51714 [cl_34536,cl_51679] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34536 v h) (hints_cons _ _ _ (der_51679 v h) (by intro d hd; cases hd)))
def cl_51715 : CNF.NClause := [(65,true),(73,false),(77,false),(91,false),(49,false)]
theorem der_51715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51715 :=
  CNF.rup_sound cl_51715 [cl_34537,cl_51681] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34537 v h) (hints_cons _ _ _ (der_51681 v h) (by intro d hd; cases hd)))
def cl_51716 : CNF.NClause := [(65,true),(77,false),(69,false),(49,false),(91,false)]
theorem der_51716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51716 :=
  CNF.rup_sound cl_51716 [cl_34539,cl_51715] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34539 v h) (hints_cons _ _ _ (der_51715 v h) (by intro d hd; cases hd)))
def cl_51718 : CNF.NClause := [(69,false),(77,true),(73,false),(49,false),(91,false)]
theorem der_51718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51718 :=
  CNF.rup_sound cl_51718 [cl_34541,cl_51712] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34541 v h) (hints_cons _ _ _ (der_51712 v h) (by intro d hd; cases hd)))
def cl_51719 : CNF.NClause := [(65,true),(77,true),(49,false),(69,false),(91,false)]
theorem der_51719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51719 :=
  CNF.rup_sound cl_51719 [cl_34543,cl_51718] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34543 v h) (hints_cons _ _ _ (der_51718 v h) (by intro d hd; cases hd)))
def cl_51721 : CNF.NClause := [(65,true),(86,false),(73,false),(77,false),(49,false)]
theorem der_51721 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51721 :=
  CNF.rup_sound cl_51721 [cl_34546,cl_42308] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34546 v h) (hints_cons _ _ _ (der_42308 v h) (by intro d hd; cases hd)))
def cl_51722 : CNF.NClause := [(65,true),(49,false),(77,false),(69,false),(86,false)]
theorem der_51722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51722 :=
  CNF.rup_sound cl_51722 [cl_34547,cl_42308] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34547 v h) (hints_cons _ _ _ (der_42308 v h) (by intro d hd; cases hd)))
def cl_51723 : CNF.NClause := [(65,true),(86,false),(77,false),(91,true),(49,false)]
theorem der_51723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51723 :=
  CNF.rup_sound cl_51723 [cl_34548,cl_51722] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34548 v h) (hints_cons _ _ _ (der_51722 v h) (by intro d hd; cases hd)))
def cl_51725 : CNF.NClause := [(65,true),(77,true),(86,false),(49,false),(69,false)]
theorem der_51725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51725 :=
  CNF.rup_sound cl_51725 [cl_34551,cl_42308] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34551 v h) (hints_cons _ _ _ (der_42308 v h) (by intro d hd; cases hd)))
def cl_51726 : CNF.NClause := [(65,true),(91,true),(69,true),(86,false),(49,false)]
theorem der_51726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51726 :=
  CNF.rup_sound cl_51726 [cl_34552,cl_51723] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34552 v h) (hints_cons _ _ _ (der_51723 v h) (by intro d hd; cases hd)))
def cl_51727 : CNF.NClause := [(73,false),(77,false),(49,false),(91,true),(69,false)]
theorem der_51727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51727 :=
  CNF.rup_sound cl_51727 [cl_34553,cl_51571] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34553 v h) (hints_cons _ _ _ (der_51571 v h) (by intro d hd; cases hd)))
def cl_51728 : CNF.NClause := [(73,false),(91,true),(77,false),(65,true),(49,false)]
theorem der_51728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51728 :=
  CNF.rup_sound cl_51728 [cl_34554,cl_51727] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34554 v h) (hints_cons _ _ _ (der_51727 v h) (by intro d hd; cases hd)))
def cl_51729 : CNF.NClause := [(65,true),(77,false),(49,false),(69,false),(73,true)]
theorem der_51729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51729 :=
  CNF.rup_sound cl_51729 [cl_34555,cl_51722] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34555 v h) (hints_cons _ _ _ (der_51722 v h) (by intro d hd; cases hd)))
def cl_51730 : CNF.NClause := [(65,true),(73,false),(77,true),(49,false),(69,false)]
theorem der_51730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51730 :=
  CNF.rup_sound cl_51730 [cl_34557,cl_51718] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34557 v h) (hints_cons _ _ _ (der_51718 v h) (by intro d hd; cases hd)))
def cl_51737 : CNF.NClause := [(121,true),(31,true),(53,false),(59,false),(42,true)]
theorem der_51737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51737 :=
  CNF.rup_sound cl_51737 [cl_24759,cl_47827] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24759 v h) (hints_cons _ _ _ (der_47827 v h) (by intro d hd; cases hd)))
def cl_51743 : CNF.NClause := [(57,false),(31,true),(122,true),(37,true),(55,false)]
theorem der_51743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51743 :=
  CNF.rup_sound cl_51743 [cl_24834,cl_50219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24834 v h) (hints_cons _ _ _ (der_50219 v h) (by intro d hd; cases hd)))
def cl_51744 : CNF.NClause := [(122,true),(55,true),(49,false),(31,true),(43,false)]
theorem der_51744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51744 :=
  CNF.rup_sound cl_51744 [cl_34564,cl_48925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34564 v h) (hints_cons _ _ _ (der_48925 v h) (by intro d hd; cases hd)))
def cl_51745 : CNF.NClause := [(122,true),(31,true),(49,false),(57,false),(43,true)]
theorem der_51745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51745 :=
  CNF.rup_sound cl_51745 [cl_24835,cl_42474] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24835 v h) (hints_cons _ _ _ (der_42474 v h) (by intro d hd; cases hd)))
def cl_51746 : CNF.NClause := [(122,true),(31,true),(49,false),(55,false),(43,true)]
theorem der_51746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51746 :=
  CNF.rup_sound cl_51746 [cl_24837,cl_42474] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24837 v h) (hints_cons _ _ _ (der_42474 v h) (by intro d hd; cases hd)))
def cl_51747 : CNF.NClause := [(31,true),(37,true),(122,true),(43,false),(49,false)]
theorem der_51747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51747 :=
  CNF.rup_sound cl_51747 [cl_24839,cl_50219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24839 v h) (hints_cons _ _ _ (der_50219 v h) (by intro d hd; cases hd)))
def cl_51759 : CNF.NClause := [(77,true),(69,false),(86,false),(91,false),(49,false)]
theorem der_51759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51759 :=
  CNF.rup_sound cl_51759 [cl_34568,cl_49716] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34568 v h) (hints_cons _ _ _ (der_49716 v h) (by intro d hd; cases hd)))
def cl_51760 : CNF.NClause := [(77,true),(69,false),(86,false),(18,false),(49,false)]
theorem der_51760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51760 :=
  CNF.rup_sound cl_51760 [cl_34570,cl_51759] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34570 v h) (hints_cons _ _ _ (der_51759 v h) (by intro d hd; cases hd)))
def cl_51761 : CNF.NClause := [(18,false),(77,false),(86,true),(49,false),(69,false)]
theorem der_51761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51761 :=
  CNF.rup_sound cl_51761 [cl_34571,cl_51685] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34571 v h) (hints_cons _ _ _ (der_51685 v h) (by intro d hd; cases hd)))
def cl_51763 : CNF.NClause := [(88,false),(67,false),(52,false),(79,true),(21,false)]
theorem der_51763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51763 :=
  CNF.rup_sound cl_51763 [cl_34575,cl_34573] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34575 v h) (hints_cons _ _ _ (der_34573 v h) (by intro d hd; cases hd)))
def cl_51764 : CNF.NClause := [(85,false),(52,false),(67,false),(79,true),(21,false)]
theorem der_51764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51764 :=
  CNF.rup_sound cl_51764 [cl_34577,cl_34573] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34577 v h) (hints_cons _ _ _ (der_34573 v h) (by intro d hd; cases hd)))
def cl_51765 : CNF.NClause := [(67,false),(66,false),(21,false),(79,true),(52,false)]
theorem der_51765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51765 :=
  CNF.rup_sound cl_51765 [cl_34579,cl_51764] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34579 v h) (hints_cons _ _ _ (der_51764 v h) (by intro d hd; cases hd)))
def cl_51766 : CNF.NClause := [(85,true),(88,false),(52,false),(79,false),(67,false)]
theorem der_51766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51766 :=
  CNF.rup_sound cl_51766 [cl_34582,cl_34574] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34582 v h) (hints_cons _ _ _ (der_34574 v h) (by intro d hd; cases hd)))
def cl_51767 : CNF.NClause := [(67,false),(73,true),(52,false),(88,false),(85,true)]
theorem der_51767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51767 :=
  CNF.rup_sound cl_51767 [cl_34583,cl_51766] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34583 v h) (hints_cons _ _ _ (der_51766 v h) (by intro d hd; cases hd)))
def cl_51768 : CNF.NClause := [(73,true),(79,false),(52,false),(85,false),(67,false)]
theorem der_51768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51768 :=
  CNF.rup_sound cl_51768 [cl_34584,cl_34576] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34584 v h) (hints_cons _ _ _ (der_34576 v h) (by intro d hd; cases hd)))
def cl_51769 : CNF.NClause := [(67,false),(73,true),(52,false),(85,false),(88,true)]
theorem der_51769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51769 :=
  CNF.rup_sound cl_51769 [cl_34585,cl_51768] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34585 v h) (hints_cons _ _ _ (der_51768 v h) (by intro d hd; cases hd)))
def cl_51771 : CNF.NClause := [(69,false),(77,false),(49,false),(91,true),(86,false)]
theorem der_51771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51771 :=
  CNF.rup_sound cl_51771 [cl_34592,cl_51723] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34592 v h) (hints_cons _ _ _ (der_51723 v h) (by intro d hd; cases hd)))
def cl_51772 : CNF.NClause := [(69,false),(91,true),(86,false),(49,false),(65,false)]
theorem der_51772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51772 :=
  CNF.rup_sound cl_51772 [cl_34593,cl_51771] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34593 v h) (hints_cons _ _ _ (der_51771 v h) (by intro d hd; cases hd)))
def cl_51774 : CNF.NClause := [(88,false),(84,false),(78,false),(13,true),(44,false)]
theorem der_51774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51774 :=
  CNF.rup_sound cl_51774 [cl_34601,cl_49673] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34601 v h) (hints_cons _ _ _ (der_49673 v h) (by intro d hd; cases hd)))
def cl_51775 : CNF.NClause := [(88,false),(44,false),(78,false),(84,false),(71,true)]
theorem der_51775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51775 :=
  CNF.rup_sound cl_51775 [cl_34603,cl_51670] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34603 v h) (hints_cons _ _ _ (der_51670 v h) (by intro d hd; cases hd)))
def cl_51776 : CNF.NClause := [(88,false),(44,false),(78,false),(13,false),(72,true)]
theorem der_51776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51776 :=
  CNF.rup_sound cl_51776 [cl_34605,cl_51691] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34605 v h) (hints_cons _ _ _ (der_51691 v h) (by intro d hd; cases hd)))
def cl_51777 : CNF.NClause := [(84,false),(44,false),(78,false),(71,true),(13,false)]
theorem der_51777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51777 :=
  CNF.rup_sound cl_51777 [cl_34608,cl_49673] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34608 v h) (hints_cons _ _ _ (der_49673 v h) (by intro d hd; cases hd)))
def cl_51778 : CNF.NClause := [(78,false),(44,false),(72,true),(84,false),(71,true)]
theorem der_51778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51778 :=
  CNF.rup_sound cl_51778 [cl_34609,cl_51670] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34609 v h) (hints_cons _ _ _ (der_51670 v h) (by intro d hd; cases hd)))
def cl_51779 : CNF.NClause := [(72,false),(13,false),(84,false),(44,false),(78,true)]
theorem der_51779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51779 :=
  CNF.rup_sound cl_51779 [cl_34610,cl_51700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34610 v h) (hints_cons _ _ _ (der_51700 v h) (by intro d hd; cases hd)))
def cl_51781 : CNF.NClause := [(65,false),(72,false),(44,false),(78,false),(84,true)]
theorem der_51781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51781 :=
  CNF.rup_sound cl_51781 [cl_34612,cl_49563] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34612 v h) (hints_cons _ _ _ (der_49563 v h) (by intro d hd; cases hd)))
def cl_51784 : CNF.NClause := [(78,true),(72,false),(44,false),(88,false),(84,false)]
theorem der_51784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51784 :=
  CNF.rup_sound cl_51784 [cl_34616,cl_51700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34616 v h) (hints_cons _ _ _ (der_51700 v h) (by intro d hd; cases hd)))
def cl_51785 : CNF.NClause := [(72,true),(71,true),(88,false),(84,false),(44,false)]
theorem der_51785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51785 :=
  CNF.rup_sound cl_51785 [cl_34617,cl_51778] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34617 v h) (hints_cons _ _ _ (der_51778 v h) (by intro d hd; cases hd)))
def cl_51786 : CNF.NClause := [(88,false),(72,true),(78,false),(71,true),(44,false)]
theorem der_51786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51786 :=
  CNF.rup_sound cl_51786 [cl_34619,cl_51775] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34619 v h) (hints_cons _ _ _ (der_51775 v h) (by intro d hd; cases hd)))
def cl_51787 : CNF.NClause := [(88,false),(84,true),(13,true),(44,false),(72,false)]
theorem der_51787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51787 :=
  CNF.rup_sound cl_51787 [cl_34620,cl_49563] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34620 v h) (hints_cons _ _ _ (der_49563 v h) (by intro d hd; cases hd)))
def cl_51788 : CNF.NClause := [(72,true),(44,false),(71,true),(88,false),(13,true)]
theorem der_51788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51788 :=
  CNF.rup_sound cl_51788 [cl_34621,cl_51786] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34621 v h) (hints_cons _ _ _ (der_51786 v h) (by intro d hd; cases hd)))
def cl_51790 : CNF.NClause := [(72,false),(84,false),(13,true),(44,false),(88,true)]
theorem der_51790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51790 :=
  CNF.rup_sound cl_51790 [cl_34624,cl_49563] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34624 v h) (hints_cons _ _ _ (der_49563 v h) (by intro d hd; cases hd)))
def cl_51791 : CNF.NClause := [(72,true),(78,true),(84,false),(44,false),(71,true)]
theorem der_51791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51791 :=
  CNF.rup_sound cl_51791 [cl_34625,cl_51785] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34625 v h) (hints_cons _ _ _ (der_51785 v h) (by intro d hd; cases hd)))
def cl_51792 : CNF.NClause := [(65,false),(44,false),(78,false),(84,true),(71,true)]
theorem der_51792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51792 :=
  CNF.rup_sound cl_51792 [cl_34627,cl_51781] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34627 v h) (hints_cons _ _ _ (der_51781 v h) (by intro d hd; cases hd)))
def cl_51800 : CNF.NClause := [(47,false),(84,false),(89,false),(16,true),(66,true)]
theorem der_51800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51800 :=
  CNF.rup_sound cl_51800 [cl_34635,cl_49547] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34635 v h) (hints_cons _ _ _ (der_49547 v h) (by intro d hd; cases hd)))
def cl_51801 : CNF.NClause := [(84,false),(16,true),(47,false),(77,false),(66,true)]
theorem der_51801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51801 :=
  CNF.rup_sound cl_51801 [cl_34638,cl_51645] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34638 v h) (hints_cons _ _ _ (der_51645 v h) (by intro d hd; cases hd)))
def cl_51802 : CNF.NClause := [(66,true),(68,false),(47,false),(77,false),(84,true)]
theorem der_51802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51802 :=
  CNF.rup_sound cl_51802 [cl_34640,cl_51627] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34640 v h) (hints_cons _ _ _ (der_51627 v h) (by intro d hd; cases hd)))
def cl_51803 : CNF.NClause := [(77,true),(75,true),(47,false),(66,true),(89,true)]
theorem der_51803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51803 :=
  CNF.rup_sound cl_51803 [cl_34641,cl_51639] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34641 v h) (hints_cons _ _ _ (der_51639 v h) (by intro d hd; cases hd)))
def cl_51804 : CNF.NClause := [(78,true),(64,false),(67,false),(53,false),(90,false)]
theorem der_51804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51804 :=
  CNF.rup_sound cl_51804 [cl_34644,cl_34642] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34644 v h) (hints_cons _ _ _ (der_34642 v h) (by intro d hd; cases hd)))
def cl_51805 : CNF.NClause := [(67,false),(78,true),(64,false),(86,false),(53,false)]
theorem der_51805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51805 :=
  CNF.rup_sound cl_51805 [cl_34646,cl_34642] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34646 v h) (hints_cons _ _ _ (der_34642 v h) (by intro d hd; cases hd)))
def cl_51806 : CNF.NClause := [(67,false),(64,false),(86,true),(53,false),(78,false)]
theorem der_51806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51806 :=
  CNF.rup_sound cl_51806 [cl_34647,cl_49558] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34647 v h) (hints_cons _ _ _ (der_49558 v h) (by intro d hd; cases hd)))
def cl_51807 : CNF.NClause := [(67,false),(78,true),(64,false),(53,false),(22,false)]
theorem der_51807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51807 :=
  CNF.rup_sound cl_51807 [cl_34648,cl_51805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34648 v h) (hints_cons _ _ _ (der_51805 v h) (by intro d hd; cases hd)))
def cl_51809 : CNF.NClause := [(77,false),(47,false),(84,true),(68,false),(89,false)]
theorem der_51809 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51809 :=
  CNF.rup_sound cl_51809 [cl_34650,cl_49547] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34650 v h) (hints_cons _ _ _ (der_49547 v h) (by intro d hd; cases hd)))
def cl_51812 : CNF.NClause := [(90,false),(86,false),(22,true),(53,false),(67,false)]
theorem der_51812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51812 :=
  CNF.rup_sound cl_51812 [cl_34656,cl_49558] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34656 v h) (hints_cons _ _ _ (der_49558 v h) (by intro d hd; cases hd)))
def cl_51813 : CNF.NClause := [(90,false),(53,false),(67,false),(86,true),(22,true)]
theorem der_51813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51813 :=
  CNF.rup_sound cl_51813 [cl_34658,cl_49558] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34658 v h) (hints_cons _ _ _ (der_49558 v h) (by intro d hd; cases hd)))
def cl_51814 : CNF.NClause := [(90,true),(67,false),(86,false),(22,true),(53,false)]
theorem der_51814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51814 :=
  CNF.rup_sound cl_51814 [cl_34660,cl_49558] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34660 v h) (hints_cons _ _ _ (der_49558 v h) (by intro d hd; cases hd)))
def cl_51815 : CNF.NClause := [(77,true),(89,false),(47,false),(66,false),(84,false)]
theorem der_51815 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51815 :=
  CNF.rup_sound cl_51815 [cl_34663,cl_51603] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34663 v h) (hints_cons _ _ _ (der_51603 v h) (by intro d hd; cases hd)))
def cl_51816 : CNF.NClause := [(68,false),(75,true),(47,false),(89,false),(84,true)]
theorem der_51816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51816 :=
  CNF.rup_sound cl_51816 [cl_34665,cl_51809] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34665 v h) (hints_cons _ _ _ (der_51809 v h) (by intro d hd; cases hd)))
def cl_51817 : CNF.NClause := [(89,true),(77,false),(66,false),(47,false),(84,false)]
theorem der_51817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51817 :=
  CNF.rup_sound cl_51817 [cl_34666,cl_51607] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34666 v h) (hints_cons _ _ _ (der_51607 v h) (by intro d hd; cases hd)))
def cl_51818 : CNF.NClause := [(77,false),(68,false),(47,false),(84,true),(66,false)]
theorem der_51818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51818 :=
  CNF.rup_sound cl_51818 [cl_34668,cl_51809] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34668 v h) (hints_cons _ _ _ (der_51809 v h) (by intro d hd; cases hd)))
def cl_51819 : CNF.NClause := [(68,false),(66,false),(47,false),(84,true),(89,true)]
theorem der_51819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51819 :=
  CNF.rup_sound cl_51819 [cl_34669,cl_51818] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34669 v h) (hints_cons _ _ _ (der_51818 v h) (by intro d hd; cases hd)))
def cl_51820 : CNF.NClause := [(77,false),(61,false),(87,true),(72,true),(67,false)]
theorem der_51820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51820 :=
  CNF.rup_sound cl_51820 [cl_24968,cl_49618] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24968 v h) (hints_cons _ _ _ (der_49618 v h) (by intro d hd; cases hd)))
def cl_51822 : CNF.NClause := [(86,false),(45,false),(79,false),(63,false),(72,true)]
theorem der_51822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51822 :=
  CNF.rup_sound cl_51822 [cl_34671,cl_49539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34671 v h) (hints_cons _ _ _ (der_49539 v h) (by intro d hd; cases hd)))
def cl_51823 : CNF.NClause := [(89,true),(45,false),(63,false),(72,true),(79,false)]
theorem der_51823 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51823 :=
  CNF.rup_sound cl_51823 [cl_34673,cl_49539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34673 v h) (hints_cons _ _ _ (der_49539 v h) (by intro d hd; cases hd)))
def cl_51825 : CNF.NClause := [(44,false),(88,false),(84,true),(72,true),(13,false)]
theorem der_51825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51825 :=
  CNF.rup_sound cl_51825 [cl_34678,cl_51776] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34678 v h) (hints_cons _ _ _ (der_51776 v h) (by intro d hd; cases hd)))
def cl_51826 : CNF.NClause := [(65,false),(71,false),(13,false),(44,false),(78,true)]
theorem der_51826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51826 :=
  CNF.rup_sound cl_51826 [cl_34682,cl_34680] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34682 v h) (hints_cons _ _ _ (der_34680 v h) (by intro d hd; cases hd)))
def cl_51827 : CNF.NClause := [(86,false),(70,false),(89,false),(14,true),(45,false)]
theorem der_51827 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51827 :=
  CNF.rup_sound cl_51827 [cl_34684,cl_47228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34684 v h) (hints_cons _ _ _ (der_47228 v h) (by intro d hd; cases hd)))
def cl_51828 : CNF.NClause := [(89,false),(70,false),(14,true),(45,false),(72,true)]
theorem der_51828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51828 :=
  CNF.rup_sound cl_51828 [cl_34686,cl_47228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34686 v h) (hints_cons _ _ _ (der_47228 v h) (by intro d hd; cases hd)))
def cl_51829 : CNF.NClause := [(86,false),(63,false),(14,true),(45,false),(72,true)]
theorem der_51829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51829 :=
  CNF.rup_sound cl_51829 [cl_34688,cl_49539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34688 v h) (hints_cons _ _ _ (der_49539 v h) (by intro d hd; cases hd)))
def cl_51830 : CNF.NClause := [(89,true),(14,true),(45,false),(63,false),(86,true)]
theorem der_51830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51830 :=
  CNF.rup_sound cl_51830 [cl_34690,cl_51602] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34690 v h) (hints_cons _ _ _ (der_51602 v h) (by intro d hd; cases hd)))
def cl_51832 : CNF.NClause := [(88,false),(44,false),(84,false),(71,false),(13,true)]
theorem der_51832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51832 :=
  CNF.rup_sound cl_51832 [cl_34692,cl_51662] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34692 v h) (hints_cons _ _ _ (der_51662 v h) (by intro d hd; cases hd)))
def cl_51833 : CNF.NClause := [(88,false),(78,false),(71,false),(13,true),(44,false)]
theorem der_51833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51833 :=
  CNF.rup_sound cl_51833 [cl_34693,cl_34458] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34693 v h) (hints_cons _ _ _ (der_34458 v h) (by intro d hd; cases hd)))
def cl_51834 : CNF.NClause := [(44,false),(88,false),(71,false),(84,true),(72,true)]
theorem der_51834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51834 :=
  CNF.rup_sound cl_51834 [cl_34694,cl_51691] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34694 v h) (hints_cons _ _ _ (der_51691 v h) (by intro d hd; cases hd)))
def cl_51835 : CNF.NClause := [(78,false),(44,false),(88,true),(71,false),(13,true)]
theorem der_51835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51835 :=
  CNF.rup_sound cl_51835 [cl_34697,cl_49563] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34697 v h) (hints_cons _ _ _ (der_49563 v h) (by intro d hd; cases hd)))
def cl_51836 : CNF.NClause := [(65,false),(78,true),(71,false),(44,false),(88,true)]
theorem der_51836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51836 :=
  CNF.rup_sound cl_51836 [cl_34698,cl_51826] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34698 v h) (hints_cons _ _ _ (der_51826 v h) (by intro d hd; cases hd)))
def cl_51838 : CNF.NClause := [(73,true),(18,false),(91,false),(49,false),(69,true)]
theorem der_51838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51838 :=
  CNF.rup_sound cl_51838 [cl_34705,cl_34703] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34705 v h) (hints_cons _ _ _ (der_34703 v h) (by intro d hd; cases hd)))
def cl_51839 : CNF.NClause := [(77,true),(73,false),(86,false),(18,false),(49,false)]
theorem der_51839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51839 :=
  CNF.rup_sound cl_51839 [cl_34707,cl_34700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34707 v h) (hints_cons _ _ _ (der_34700 v h) (by intro d hd; cases hd)))
def cl_51840 : CNF.NClause := [(86,false),(69,true),(49,false),(77,true),(18,false)]
theorem der_51840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51840 :=
  CNF.rup_sound cl_51840 [cl_34708,cl_51839] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34708 v h) (hints_cons _ _ _ (der_51839 v h) (by intro d hd; cases hd)))
def cl_51843 : CNF.NClause := [(77,true),(73,false),(49,false),(18,false),(91,true)]
theorem der_51843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51843 :=
  CNF.rup_sound cl_51843 [cl_34711,cl_51839] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34711 v h) (hints_cons _ _ _ (der_51839 v h) (by intro d hd; cases hd)))
def cl_51845 : CNF.NClause := [(73,false),(86,false),(49,false),(77,true),(91,false)]
theorem der_51845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51845 :=
  CNF.rup_sound cl_51845 [cl_34715,cl_51714] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34715 v h) (hints_cons _ _ _ (der_51714 v h) (by intro d hd; cases hd)))
def cl_51847 : CNF.NClause := [(77,false),(91,false),(49,false),(69,true),(73,true)]
theorem der_51847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51847 :=
  CNF.rup_sound cl_51847 [cl_34718,cl_34714] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34718 v h) (hints_cons _ _ _ (der_34714 v h) (by intro d hd; cases hd)))
def cl_51848 : CNF.NClause := [(73,false),(69,true),(77,true),(86,false),(49,false)]
theorem der_51848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51848 :=
  CNF.rup_sound cl_51848 [cl_34723,cl_51845] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34723 v h) (hints_cons _ _ _ (der_51845 v h) (by intro d hd; cases hd)))
def cl_51849 : CNF.NClause := [(91,true),(49,false),(77,false),(73,false),(86,true)]
theorem der_51849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51849 :=
  CNF.rup_sound cl_51849 [cl_34725,cl_51728] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34725 v h) (hints_cons _ _ _ (der_51728 v h) (by intro d hd; cases hd)))
def cl_51850 : CNF.NClause := [(65,false),(91,true),(86,true),(49,false),(73,false)]
theorem der_51850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51850 :=
  CNF.rup_sound cl_51850 [cl_34727,cl_51849] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34727 v h) (hints_cons _ _ _ (der_51849 v h) (by intro d hd; cases hd)))
def cl_51851 : CNF.NClause := [(73,false),(52,false),(88,false),(85,false),(66,true)]
theorem der_51851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51851 :=
  CNF.rup_sound cl_51851 [cl_34731,cl_51649] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34731 v h) (hints_cons _ _ _ (der_51649 v h) (by intro d hd; cases hd)))
def cl_51852 : CNF.NClause := [(85,false),(66,true),(21,false),(52,false),(88,false)]
theorem der_51852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51852 :=
  CNF.rup_sound cl_51852 [cl_34732,cl_51851] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34732 v h) (hints_cons _ _ _ (der_51851 v h) (by intro d hd; cases hd)))
def cl_51854 : CNF.NClause := [(88,false),(79,false),(21,false),(66,true),(52,false)]
theorem der_51854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51854 :=
  CNF.rup_sound cl_51854 [cl_34734,cl_34730] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34734 v h) (hints_cons _ _ _ (der_34730 v h) (by intro d hd; cases hd)))
def cl_51856 : CNF.NClause := [(79,false),(66,true),(52,false),(85,false),(88,true)]
theorem der_51856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51856 :=
  CNF.rup_sound cl_51856 [cl_34738,cl_51657] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34738 v h) (hints_cons _ _ _ (der_51657 v h) (by intro d hd; cases hd)))
def cl_51857 : CNF.NClause := [(85,false),(66,true),(73,true),(52,false),(88,true)]
theorem der_51857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51857 :=
  CNF.rup_sound cl_51857 [cl_34740,cl_34443] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34740 v h) (hints_cons _ _ _ (der_34443 v h) (by intro d hd; cases hd)))
def cl_51858 : CNF.NClause := [(79,false),(52,false),(73,true),(66,true),(21,false)]
theorem der_51858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51858 :=
  CNF.rup_sound cl_51858 [cl_34742,cl_51854] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34742 v h) (hints_cons _ _ _ (der_51854 v h) (by intro d hd; cases hd)))
def cl_51861 : CNF.NClause := [(86,false),(64,false),(53,false),(75,true),(22,false)]
theorem der_51861 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51861 :=
  CNF.rup_sound cl_51861 [cl_34751,cl_34749] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34751 v h) (hints_cons _ _ _ (der_34749 v h) (by intro d hd; cases hd)))
def cl_51862 : CNF.NClause := [(78,true),(75,false),(53,false),(64,false),(22,false)]
theorem der_51862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51862 :=
  CNF.rup_sound cl_51862 [cl_34754,cl_34750] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34754 v h) (hints_cons _ _ _ (der_34750 v h) (by intro d hd; cases hd)))
def cl_51864 : CNF.NClause := [(73,false),(85,false),(88,false),(79,true),(52,false)]
theorem der_51864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51864 :=
  CNF.rup_sound cl_51864 [cl_34758,cl_51851] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34758 v h) (hints_cons _ _ _ (der_51851 v h) (by intro d hd; cases hd)))
def cl_51867 : CNF.NClause := [(79,false),(52,false),(85,false),(66,false),(67,true)]
theorem der_51867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51867 :=
  CNF.rup_sound cl_51867 [cl_34765,cl_50593] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34765 v h) (hints_cons _ _ _ (der_50593 v h) (by intro d hd; cases hd)))
def cl_51868 : CNF.NClause := [(79,true),(66,false),(52,false),(85,false),(73,false)]
theorem der_51868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51868 :=
  CNF.rup_sound cl_51868 [cl_34766,cl_51579] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34766 v h) (hints_cons _ _ _ (der_51579 v h) (by intro d hd; cases hd)))
def cl_51872 : CNF.NClause := [(86,false),(75,true),(22,true),(53,false),(64,true)]
theorem der_51872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51872 :=
  CNF.rup_sound cl_51872 [cl_34778,cl_34772] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34778 v h) (hints_cons _ _ _ (der_34772 v h) (by intro d hd; cases hd)))
def cl_51873 : CNF.NClause := [(78,false),(53,false),(64,true),(75,true),(22,true)]
theorem der_51873 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51873 :=
  CNF.rup_sound cl_51873 [cl_34780,cl_51872] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34780 v h) (hints_cons _ _ _ (der_51872 v h) (by intro d hd; cases hd)))
def cl_51874 : CNF.NClause := [(78,true),(64,true),(53,false),(75,true),(22,true)]
theorem der_51874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51874 :=
  CNF.rup_sound cl_51874 [cl_34781,cl_51872] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34781 v h) (hints_cons _ _ _ (der_51872 v h) (by intro d hd; cases hd)))
def cl_51875 : CNF.NClause := [(90,false),(75,false),(86,true),(22,true),(53,false)]
theorem der_51875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51875 :=
  CNF.rup_sound cl_51875 [cl_34787,cl_34318] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34787 v h) (hints_cons _ _ _ (der_34318 v h) (by intro d hd; cases hd)))
def cl_51876 : CNF.NClause := [(78,true),(90,false),(86,true),(22,true),(53,false)]
theorem der_51876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51876 :=
  CNF.rup_sound cl_51876 [cl_34788,cl_51875] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34788 v h) (hints_cons _ _ _ (der_51875 v h) (by intro d hd; cases hd)))
def cl_51877 : CNF.NClause := [(75,false),(22,true),(53,false),(86,false),(90,true)]
theorem der_51877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51877 :=
  CNF.rup_sound cl_51877 [cl_34791,cl_34319] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34791 v h) (hints_cons _ _ _ (der_34319 v h) (by intro d hd; cases hd)))
def cl_51878 : CNF.NClause := [(86,false),(78,true),(22,true),(53,false),(75,true)]
theorem der_51878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51878 :=
  CNF.rup_sound cl_51878 [cl_34792,cl_51872] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34792 v h) (hints_cons _ _ _ (der_51872 v h) (by intro d hd; cases hd)))
def cl_51879 : CNF.NClause := [(78,false),(64,false),(53,false),(86,true),(90,true)]
theorem der_51879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51879 :=
  CNF.rup_sound cl_51879 [cl_34794,cl_51806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34794 v h) (hints_cons _ _ _ (der_51806 v h) (by intro d hd; cases hd)))
def cl_51880 : CNF.NClause := [(86,true),(75,false),(64,false),(53,false),(90,true)]
theorem der_51880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51880 :=
  CNF.rup_sound cl_51880 [cl_34795,cl_34793] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34795 v h) (hints_cons _ _ _ (der_34793 v h) (by intro d hd; cases hd)))
def cl_51881 : CNF.NClause := [(67,true),(90,true),(64,false),(86,true),(53,false)]
theorem der_51881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51881 :=
  CNF.rup_sound cl_51881 [cl_34796,cl_51880] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34796 v h) (hints_cons _ _ _ (der_51880 v h) (by intro d hd; cases hd)))
def cl_51882 : CNF.NClause := [(70,true),(89,false),(45,false),(79,false),(86,false)]
theorem der_51882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51882 :=
  CNF.rup_sound cl_51882 [cl_34798,cl_51589] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34798 v h) (hints_cons _ _ _ (der_51589 v h) (by intro d hd; cases hd)))
def cl_51883 : CNF.NClause := [(86,false),(72,false),(79,true),(89,false),(45,false)]
theorem der_51883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51883 :=
  CNF.rup_sound cl_51883 [cl_34800,cl_34799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34800 v h) (hints_cons _ _ _ (der_34799 v h) (by intro d hd; cases hd)))
def cl_51884 : CNF.NClause := [(86,false),(89,false),(45,false),(63,true),(70,true)]
theorem der_51884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51884 :=
  CNF.rup_sound cl_51884 [cl_34801,cl_51591] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34801 v h) (hints_cons _ _ _ (der_51591 v h) (by intro d hd; cases hd)))
def cl_51885 : CNF.NClause := [(72,false),(45,false),(89,false),(86,true),(79,false)]
theorem der_51885 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51885 :=
  CNF.rup_sound cl_51885 [cl_34803,cl_51592] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34803 v h) (hints_cons _ _ _ (der_51592 v h) (by intro d hd; cases hd)))
def cl_51886 : CNF.NClause := [(70,true),(89,false),(45,false),(79,false),(72,true)]
theorem der_51886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51886 :=
  CNF.rup_sound cl_51886 [cl_34804,cl_51882] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34804 v h) (hints_cons _ _ _ (der_51882 v h) (by intro d hd; cases hd)))
def cl_51887 : CNF.NClause := [(72,false),(86,true),(89,false),(70,false),(45,false)]
theorem der_51887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51887 :=
  CNF.rup_sound cl_51887 [cl_34805,cl_51577] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34805 v h) (hints_cons _ _ _ (der_51577 v h) (by intro d hd; cases hd)))
def cl_51888 : CNF.NClause := [(70,true),(89,false),(72,false),(45,false),(79,true)]
theorem der_51888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51888 :=
  CNF.rup_sound cl_51888 [cl_34806,cl_51594] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34806 v h) (hints_cons _ _ _ (der_51594 v h) (by intro d hd; cases hd)))
def cl_51889 : CNF.NClause := [(70,true),(45,false),(89,false),(63,true),(72,true)]
theorem der_51889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51889 :=
  CNF.rup_sound cl_51889 [cl_34808,cl_51884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34808 v h) (hints_cons _ _ _ (der_51884 v h) (by intro d hd; cases hd)))
def cl_51890 : CNF.NClause := [(70,true),(45,false),(79,false),(86,false),(72,false)]
theorem der_51890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51890 :=
  CNF.rup_sound cl_51890 [cl_34809,cl_51882] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34809 v h) (hints_cons _ _ _ (der_51882 v h) (by intro d hd; cases hd)))
def cl_51891 : CNF.NClause := [(89,true),(70,true),(79,false),(86,false),(45,false)]
theorem der_51891 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51891 :=
  CNF.rup_sound cl_51891 [cl_34811,cl_51600] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34811 v h) (hints_cons _ _ _ (der_51600 v h) (by intro d hd; cases hd)))
def cl_51892 : CNF.NClause := [(70,true),(86,false),(72,false),(45,false),(63,true)]
theorem der_51892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51892 :=
  CNF.rup_sound cl_51892 [cl_34813,cl_51890] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34813 v h) (hints_cons _ _ _ (der_51890 v h) (by intro d hd; cases hd)))
def cl_51895 : CNF.NClause := [(89,true),(70,false),(45,false),(79,false),(14,false)]
theorem der_51895 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51895 :=
  CNF.rup_sound cl_51895 [cl_34818,cl_34810] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34818 v h) (hints_cons _ _ _ (der_34810 v h) (by intro d hd; cases hd)))
def cl_51896 : CNF.NClause := [(89,true),(70,true),(79,false),(63,true),(45,false)]
theorem der_51896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51896 :=
  CNF.rup_sound cl_51896 [cl_34819,cl_51891] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34819 v h) (hints_cons _ _ _ (der_51891 v h) (by intro d hd; cases hd)))
def cl_51898 : CNF.NClause := [(70,true),(45,false),(72,false),(63,true),(89,true)]
theorem der_51898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51898 :=
  CNF.rup_sound cl_51898 [cl_34821,cl_51892] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34821 v h) (hints_cons _ _ _ (der_51892 v h) (by intro d hd; cases hd)))
def cl_51901 : CNF.NClause := [(86,false),(79,false),(14,true),(45,false),(72,true)]
theorem der_51901 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51901 :=
  CNF.rup_sound cl_51901 [cl_34825,cl_49539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34825 v h) (hints_cons _ _ _ (der_49539 v h) (by intro d hd; cases hd)))
def cl_51902 : CNF.NClause := [(86,false),(45,false),(72,false),(79,true),(14,true)]
theorem der_51902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51902 :=
  CNF.rup_sound cl_51902 [cl_34826,cl_51883] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34826 v h) (hints_cons _ _ _ (der_51883 v h) (by intro d hd; cases hd)))
def cl_51903 : CNF.NClause := [(86,false),(45,false),(72,true),(79,true),(14,true)]
theorem der_51903 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51903 :=
  CNF.rup_sound cl_51903 [cl_34827,cl_51598] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34827 v h) (hints_cons _ _ _ (der_51598 v h) (by intro d hd; cases hd)))
def cl_51904 : CNF.NClause := [(89,true),(86,true),(79,false),(14,true),(45,false)]
theorem der_51904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51904 :=
  CNF.rup_sound cl_51904 [cl_34829,cl_49538] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34829 v h) (hints_cons _ _ _ (der_49538 v h) (by intro d hd; cases hd)))
def cl_51905 : CNF.NClause := [(89,true),(14,true),(45,false),(72,false),(86,true)]
theorem der_51905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51905 :=
  CNF.rup_sound cl_51905 [cl_34830,cl_51602] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34830 v h) (hints_cons _ _ _ (der_51602 v h) (by intro d hd; cases hd)))
def cl_51910 : CNF.NClause := [(120,true),(31,true),(45,false),(38,false),(47,true)]
theorem der_51910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51910 :=
  CNF.rup_sound cl_51910 [cl_25067,cl_45954] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25067 v h) (hints_cons _ _ _ (der_45954 v h) (by intro d hd; cases hd)))
def cl_51956 : CNF.NClause := [(78,true),(75,true),(86,false),(90,false),(53,false)]
theorem der_51956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51956 :=
  CNF.rup_sound cl_51956 [cl_34846,cl_34784] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34846 v h) (hints_cons _ _ _ (der_34784 v h) (by intro d hd; cases hd)))
def cl_51957 : CNF.NClause := [(90,false),(53,false),(78,false),(67,false),(75,true)]
theorem der_51957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51957 :=
  CNF.rup_sound cl_51957 [cl_34849,cl_34841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34849 v h) (hints_cons _ _ _ (der_34841 v h) (by intro d hd; cases hd)))
def cl_51958 : CNF.NClause := [(67,true),(78,false),(90,false),(64,true),(53,false)]
theorem der_51958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51958 :=
  CNF.rup_sound cl_51958 [cl_34850,cl_34842] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34850 v h) (hints_cons _ _ _ (der_34842 v h) (by intro d hd; cases hd)))
def cl_51959 : CNF.NClause := [(78,true),(90,false),(75,false),(67,false),(53,false)]
theorem der_51959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51959 :=
  CNF.rup_sound cl_51959 [cl_34851,cl_51804] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34851 v h) (hints_cons _ _ _ (der_51804 v h) (by intro d hd; cases hd)))
def cl_51960 : CNF.NClause := [(67,true),(64,true),(90,false),(53,false),(75,false)]
theorem der_51960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51960 :=
  CNF.rup_sound cl_51960 [cl_34852,cl_34844] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34852 v h) (hints_cons _ _ _ (der_34844 v h) (by intro d hd; cases hd)))
def cl_51961 : CNF.NClause := [(67,false),(78,true),(53,false),(90,false),(22,false)]
theorem der_51961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51961 :=
  CNF.rup_sound cl_51961 [cl_34853,cl_51959] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34853 v h) (hints_cons _ _ _ (der_51959 v h) (by intro d hd; cases hd)))
def cl_51962 : CNF.NClause := [(78,true),(75,true),(90,false),(53,false),(67,true)]
theorem der_51962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51962 :=
  CNF.rup_sound cl_51962 [cl_34854,cl_51956] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34854 v h) (hints_cons _ _ _ (der_51956 v h) (by intro d hd; cases hd)))
def cl_51963 : CNF.NClause := [(86,false),(75,true),(53,false),(78,false),(67,false)]
theorem der_51963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51963 :=
  CNF.rup_sound cl_51963 [cl_34857,cl_34841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34857 v h) (hints_cons _ _ _ (der_34841 v h) (by intro d hd; cases hd)))
def cl_51964 : CNF.NClause := [(78,true),(75,false),(53,false),(86,false),(67,false)]
theorem der_51964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51964 :=
  CNF.rup_sound cl_51964 [cl_34859,cl_51959] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34859 v h) (hints_cons _ _ _ (der_51959 v h) (by intro d hd; cases hd)))
def cl_51965 : CNF.NClause := [(78,true),(86,false),(53,false),(67,false),(75,true)]
theorem der_51965 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51965 :=
  CNF.rup_sound cl_51965 [cl_34861,cl_51878] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34861 v h) (hints_cons _ _ _ (der_51878 v h) (by intro d hd; cases hd)))
def cl_51966 : CNF.NClause := [(90,true),(75,false),(78,false),(67,false),(53,false)]
theorem der_51966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51966 :=
  CNF.rup_sound cl_51966 [cl_34863,cl_49558] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34863 v h) (hints_cons _ _ _ (der_49558 v h) (by intro d hd; cases hd)))
def cl_51968 : CNF.NClause := [(78,true),(75,false),(53,false),(67,false),(22,false)]
theorem der_51968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51968 :=
  CNF.rup_sound cl_51968 [cl_34867,cl_51959] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34867 v h) (hints_cons _ _ _ (der_51959 v h) (by intro d hd; cases hd)))
def cl_51970 : CNF.NClause := [(108,true),(61,true),(48,true),(46,false),(47,false)]
theorem der_51970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51970 :=
  CNF.rup_sound cl_51970 [cl_25597,cl_36297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25597 v h) (hints_cons _ _ _ (der_36297 v h) (by intro d hd; cases hd)))
def cl_51971 : CNF.NClause := [(116,true),(34,false),(36,false),(58,true),(50,false)]
theorem der_51971 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51971 :=
  CNF.rup_sound cl_51971 [cl_25616,cl_50032] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25616 v h) (hints_cons _ _ _ (der_50032 v h) (by intro d hd; cases hd)))
def cl_51982 : CNF.NClause := [(50,false),(121,true),(53,false),(31,true),(42,true)]
theorem der_51982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51982 :=
  CNF.rup_sound cl_51982 [cl_25787,cl_47827] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25787 v h) (hints_cons _ _ _ (der_47827 v h) (by intro d hd; cases hd)))
def cl_51987 : CNF.NClause := [(61,true),(50,false),(49,false),(47,true),(108,true)]
theorem der_51987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51987 :=
  CNF.rup_sound cl_51987 [cl_25833,cl_48917] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25833 v h) (hints_cons _ _ _ (der_48917 v h) (by intro d hd; cases hd)))
def cl_51990 : CNF.NClause := [(51,true),(60,false),(99,true),(43,false),(35,true)]
theorem der_51990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51990 :=
  CNF.rup_sound cl_51990 [cl_25950,cl_50510] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25950 v h) (hints_cons _ _ _ (der_50510 v h) (by intro d hd; cases hd)))
def cl_51999 : CNF.NClause := [(37,false),(44,true),(46,false),(53,true),(109,true)]
theorem der_51999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51999 :=
  CNF.rup_sound cl_51999 [cl_26012,cl_37286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26012 v h) (hints_cons _ _ _ (der_37286 v h) (by intro d hd; cases hd)))
def cl_52001 : CNF.NClause := [(118,true),(61,true),(33,false),(32,false),(31,true)]
theorem der_52001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52001 :=
  CNF.rup_sound cl_52001 [cl_26040,cl_50298] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26040 v h) (hints_cons _ _ _ (der_50298 v h) (by intro d hd; cases hd)))
def cl_52003 : CNF.NClause := [(108,true),(46,false),(49,false),(47,true),(48,true)]
theorem der_52003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52003 :=
  CNF.rup_sound cl_52003 [cl_26146,cl_50810] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26146 v h) (hints_cons _ _ _ (der_50810 v h) (by intro d hd; cases hd)))
def cl_52004 : CNF.NClause := [(108,true),(61,true),(50,true),(46,false),(47,false)]
theorem der_52004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52004 :=
  CNF.rup_sound cl_52004 [cl_26147,cl_42543] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26147 v h) (hints_cons _ _ _ (der_42543 v h) (by intro d hd; cases hd)))
def cl_52014 : CNF.NClause := [(89,true),(47,false),(68,false),(66,false),(84,false)]
theorem der_52014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52014 :=
  CNF.rup_sound cl_52014 [cl_35701,cl_40091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35701 v h) (hints_cons _ _ _ (der_40091 v h) (by intro d hd; cases hd)))
def cl_52015 : CNF.NClause := [(86,true),(5,false),(14,true),(1,true),(160,true)]
theorem der_52015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52015 :=
  CNF.rup_sound cl_52015 [cl_35392,cl_50392] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35392 v h) (hints_cons _ _ _ (der_50392 v h) (by intro d hd; cases hd)))
def cl_52017 : CNF.NClause := [(80,true),(76,false),(55,false),(84,false),(24,true)]
theorem der_52017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52017 :=
  CNF.rup_sound cl_52017 [cl_38095,cl_50882] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_38095 v h) (hints_cons _ _ _ (der_50882 v h) (by intro d hd; cases hd)))
def cl_52018 : CNF.NClause := [(89,false),(78,false),(69,false),(76,true),(58,false)]
theorem der_52018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52018 :=
  CNF.rup_sound cl_52018 [cl_36488,cl_50758] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36488 v h) (hints_cons _ _ _ (der_50758 v h) (by intro d hd; cases hd)))
def cl_52019 : CNF.NClause := [(3,true),(17,true),(28,false),(70,true),(14,false)]
theorem der_52019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52019 :=
  CNF.rup_sound cl_52019 [cl_37838,cl_49562] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_37838 v h) (hints_cons _ _ _ (der_49562 v h) (by intro d hd; cases hd)))
def cl_52020 : CNF.NClause := [(26,false),(9,false),(10,true),(22,true),(75,true)]
theorem der_52020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52020 :=
  CNF.rup_sound cl_52020 [cl_36501,cl_44586] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36501 v h) (hints_cons _ _ _ (der_44586 v h) (by intro d hd; cases hd)))
def cl_52022 : CNF.NClause := [(65,false),(18,true),(69,false),(86,false),(49,false)]
theorem der_52022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52022 :=
  CNF.rup_sound cl_52022 [cl_37277,cl_51772] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_37277 v h) (hints_cons _ _ _ (der_51772 v h) (by intro d hd; cases hd)))
def cl_52023 : CNF.NClause := [(64,true),(43,false),(72,false),(68,false),(91,false)]
theorem der_52023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52023 :=
  CNF.rup_sound cl_52023 [cl_36716,cl_51074] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36716 v h) (hints_cons _ _ _ (der_51074 v h) (by intro d hd; cases hd)))
def cl_52026 : CNF.NClause := [(87,false),(34,false),(75,false),(80,false),(65,true)]
theorem der_52026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52026 :=
  CNF.rup_sound cl_52026 [cl_35997,cl_33081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35997 v h) (hints_cons _ _ _ (der_33081 v h) (by intro d hd; cases hd)))
def cl_52028 : CNF.NClause := [(76,false),(48,false),(64,true),(83,false),(88,false)]
theorem der_52028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52028 :=
  CNF.rup_sound cl_52028 [cl_38191,cl_51007] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_38191 v h) (hints_cons _ _ _ (der_51007 v h) (by intro d hd; cases hd)))
def cl_52031 : CNF.NClause := [(916,true),(10,true),(76,true),(907,false),(8,false)]
theorem der_52031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52031 :=
  CNF.rup_sound cl_52031 [cl_36587,cl_50535] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36587 v h) (hints_cons _ _ _ (der_50535 v h) (by intro d hd; cases hd)))
def cl_52032 : CNF.NClause := [(8,false),(148,true),(10,true),(76,true),(132,false)]
theorem der_52032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52032 :=
  CNF.rup_sound cl_52032 [cl_36975,cl_50535] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36975 v h) (hints_cons _ _ _ (der_50535 v h) (by intro d hd; cases hd)))
def cl_52035 : CNF.NClause := [(77,true),(1,true),(15,false),(170,false),(171,true)]
theorem der_52035 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52035 :=
  CNF.rup_sound cl_52035 [cl_37360,cl_36157] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_37360 v h) (hints_cons _ _ _ (der_36157 v h) (by intro d hd; cases hd)))
def cl_52036 : CNF.NClause := [(7,true),(26,false),(71,true),(912,true),(925,false)]
theorem der_52036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52036 :=
  CNF.rup_sound cl_52036 [cl_36752,cl_39345] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36752 v h) (hints_cons _ _ _ (der_39345 v h) (by intro d hd; cases hd)))
def chunk048 : List CNF.NClause := [cl_51199,cl_51200,cl_51202,cl_51217,cl_51218,cl_51219,cl_51220,cl_51222,cl_51223,cl_51224,cl_51226,cl_51228,cl_51229,cl_51231,cl_51232,cl_51233,cl_51234,cl_51235,cl_51236,cl_51237,cl_51238,cl_51240,cl_51241,cl_51243,cl_51244,cl_51245,cl_51246,cl_51247,cl_51248,cl_51249,cl_51250,cl_51251,cl_51252,cl_51253,cl_51254,cl_51255,cl_51256,cl_51257,cl_51258,cl_51259,cl_51261,cl_51262,cl_51263,cl_51264,cl_51265,cl_51266,cl_51267,cl_51271,cl_51272,cl_51273,cl_51275,cl_51276,cl_51277,cl_51278,cl_51279,cl_51280,cl_51281,cl_51282,cl_51283,cl_51284,cl_51285,cl_51286,cl_51287,cl_51291,cl_51292,cl_51293,cl_51294,cl_51295,cl_51297,cl_51298,cl_51299,cl_51300,cl_51301,cl_51302,cl_51303,cl_51304,cl_51306,cl_51307,cl_51308,cl_51309,cl_51310,cl_51311,cl_51312,cl_51313,cl_51314,cl_51321,cl_51325,cl_51326,cl_51327,cl_51328,cl_51329,cl_51330,cl_51331,cl_51332,cl_51333,cl_51334,cl_51335,cl_51337,cl_51338,cl_51340,cl_51341,cl_51343,cl_51344,cl_51345,cl_51347,cl_51348,cl_51349,cl_51350,cl_51352,cl_51353,cl_51354,cl_51359,cl_51360,cl_51363,cl_51364,cl_51365,cl_51368,cl_51371,cl_51373,cl_51374,cl_51377,cl_51378,cl_51382,cl_51383,cl_51384,cl_51385,cl_51386,cl_51388,cl_51390,cl_51392,cl_51394,cl_51395,cl_51396,cl_51397,cl_51400,cl_51401,cl_51402,cl_51403,cl_51404,cl_51405,cl_51406,cl_51408,cl_51409,cl_51410,cl_51412,cl_51413,cl_51414,cl_51416,cl_51418,cl_51420,cl_51421,cl_51422,cl_51423,cl_51424,cl_51425,cl_51426,cl_51427,cl_51428,cl_51431,cl_51432,cl_51433,cl_51434,cl_51435,cl_51437,cl_51438,cl_51439,cl_51440,cl_51441,cl_51442,cl_51443,cl_51444,cl_51445,cl_51446,cl_51447,cl_51448,cl_51449,cl_51450,cl_51451,cl_51452,cl_51453,cl_51454,cl_51455,cl_51457,cl_51458,cl_51459,cl_51460,cl_51462,cl_51467,cl_51469,cl_51472,cl_51475,cl_51476,cl_51477,cl_51479,cl_51481,cl_51482,cl_51483,cl_51484,cl_51485,cl_51486,cl_51487,cl_51488,cl_51489,cl_51490,cl_51491,cl_51493,cl_51494,cl_51495,cl_51496,cl_51497,cl_51499,cl_51502,cl_51503,cl_51506,cl_51508,cl_51516,cl_51519,cl_51520,cl_51522,cl_51523,cl_51524,cl_51526,cl_51527,cl_51528,cl_51529,cl_51530,cl_51532,cl_51534,cl_51535,cl_51540,cl_51541,cl_51542,cl_51543,cl_51551,cl_51557,cl_51559,cl_51561,cl_51562,cl_51568,cl_51569,cl_51571,cl_51572,cl_51575,cl_51576,cl_51577,cl_51578,cl_51579,cl_51581,cl_51582,cl_51583,cl_51584,cl_51585,cl_51587,cl_51588,cl_51589,cl_51590,cl_51591,cl_51592,cl_51593,cl_51594,cl_51595,cl_51596,cl_51597,cl_51598,cl_51600,cl_51602,cl_51603,cl_51607,cl_51609,cl_51610,cl_51611,cl_51612,cl_51615,cl_51620,cl_51621,cl_51622,cl_51623,cl_51624,cl_51626,cl_51627,cl_51628,cl_51629,cl_51630,cl_51631,cl_51634,cl_51636,cl_51639,cl_51640,cl_51642,cl_51643,cl_51644,cl_51645,cl_51646,cl_51647,cl_51648,cl_51649,cl_51650,cl_51651,cl_51652,cl_51653,cl_51654,cl_51655,cl_51656,cl_51657,cl_51659,cl_51660,cl_51661,cl_51662,cl_51663,cl_51664,cl_51665,cl_51667,cl_51668,cl_51669,cl_51670,cl_51671,cl_51674,cl_51675,cl_51676,cl_51678,cl_51679,cl_51681,cl_51685,cl_51691,cl_51694,cl_51695,cl_51696,cl_51697,cl_51699,cl_51700,cl_51701,cl_51703,cl_51705,cl_51707,cl_51711,cl_51712,cl_51713,cl_51714,cl_51715,cl_51716,cl_51718,cl_51719,cl_51721,cl_51722,cl_51723,cl_51725,cl_51726,cl_51727,cl_51728,cl_51729,cl_51730,cl_51737,cl_51743,cl_51744,cl_51745,cl_51746,cl_51747,cl_51759,cl_51760,cl_51761,cl_51763,cl_51764,cl_51765,cl_51766,cl_51767,cl_51768,cl_51769,cl_51771,cl_51772,cl_51774,cl_51775,cl_51776,cl_51777,cl_51778,cl_51779,cl_51781,cl_51784,cl_51785,cl_51786,cl_51787,cl_51788,cl_51790,cl_51791,cl_51792,cl_51800,cl_51801,cl_51802,cl_51803,cl_51804,cl_51805,cl_51806,cl_51807,cl_51809,cl_51812,cl_51813,cl_51814,cl_51815,cl_51816,cl_51817,cl_51818,cl_51819,cl_51820,cl_51822,cl_51823,cl_51825,cl_51826,cl_51827,cl_51828,cl_51829,cl_51830,cl_51832,cl_51833,cl_51834,cl_51835,cl_51836,cl_51838,cl_51839,cl_51840,cl_51843,cl_51845,cl_51847,cl_51848,cl_51849,cl_51850,cl_51851,cl_51852,cl_51854,cl_51856,cl_51857,cl_51858,cl_51861,cl_51862,cl_51864,cl_51867,cl_51868,cl_51872,cl_51873,cl_51874,cl_51875,cl_51876,cl_51877,cl_51878,cl_51879,cl_51880,cl_51881,cl_51882,cl_51883,cl_51884,cl_51885,cl_51886,cl_51887,cl_51888,cl_51889,cl_51890,cl_51891,cl_51892,cl_51895,cl_51896,cl_51898,cl_51901,cl_51902,cl_51903,cl_51904,cl_51905,cl_51910,cl_51956,cl_51957,cl_51958,cl_51959,cl_51960,cl_51961,cl_51962,cl_51963,cl_51964,cl_51965,cl_51966,cl_51968,cl_51970,cl_51971,cl_51982,cl_51987,cl_51990,cl_51999,cl_52001,cl_52003,cl_52004,cl_52014,cl_52015,cl_52017,cl_52018,cl_52019,cl_52020,cl_52022,cl_52023,cl_52026,cl_52028,cl_52031,cl_52032,cl_52035,cl_52036]
theorem chunk_sound048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk048, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_51199 v h) (hints_cons _ _ _ (der_51200 v h) (hints_cons _ _ _ (der_51202 v h) (hints_cons _ _ _ (der_51217 v h) (hints_cons _ _ _ (der_51218 v h) (hints_cons _ _ _ (der_51219 v h) (hints_cons _ _ _ (der_51220 v h) (hints_cons _ _ _ (der_51222 v h) (hints_cons _ _ _ (der_51223 v h) (hints_cons _ _ _ (der_51224 v h) (hints_cons _ _ _ (der_51226 v h) (hints_cons _ _ _ (der_51228 v h) (hints_cons _ _ _ (der_51229 v h) (hints_cons _ _ _ (der_51231 v h) (hints_cons _ _ _ (der_51232 v h) (hints_cons _ _ _ (der_51233 v h) (hints_cons _ _ _ (der_51234 v h) (hints_cons _ _ _ (der_51235 v h) (hints_cons _ _ _ (der_51236 v h) (hints_cons _ _ _ (der_51237 v h) (hints_cons _ _ _ (der_51238 v h) (hints_cons _ _ _ (der_51240 v h) (hints_cons _ _ _ (der_51241 v h) (hints_cons _ _ _ (der_51243 v h) (hints_cons _ _ _ (der_51244 v h) (hints_cons _ _ _ (der_51245 v h) (hints_cons _ _ _ (der_51246 v h) (hints_cons _ _ _ (der_51247 v h) (hints_cons _ _ _ (der_51248 v h) (hints_cons _ _ _ (der_51249 v h) (hints_cons _ _ _ (der_51250 v h) (hints_cons _ _ _ (der_51251 v h) (hints_cons _ _ _ (der_51252 v h) (hints_cons _ _ _ (der_51253 v h) (hints_cons _ _ _ (der_51254 v h) (hints_cons _ _ _ (der_51255 v h) (hints_cons _ _ _ (der_51256 v h) (hints_cons _ _ _ (der_51257 v h) (hints_cons _ _ _ (der_51258 v h) (hints_cons _ _ _ (der_51259 v h) (hints_cons _ _ _ (der_51261 v h) (hints_cons _ _ _ (der_51262 v h) (hints_cons _ _ _ (der_51263 v h) (hints_cons _ _ _ (der_51264 v h) (hints_cons _ _ _ (der_51265 v h) (hints_cons _ _ _ (der_51266 v h) (hints_cons _ _ _ (der_51267 v h) (hints_cons _ _ _ (der_51271 v h) (hints_cons _ _ _ (der_51272 v h) (hints_cons _ _ _ (der_51273 v h) (hints_cons _ _ _ (der_51275 v h) (hints_cons _ _ _ (der_51276 v h) (hints_cons _ _ _ (der_51277 v h) (hints_cons _ _ _ (der_51278 v h) (hints_cons _ _ _ (der_51279 v h) (hints_cons _ _ _ (der_51280 v h) (hints_cons _ _ _ (der_51281 v h) (hints_cons _ _ _ (der_51282 v h) (hints_cons _ _ _ (der_51283 v h) (hints_cons _ _ _ (der_51284 v h) (hints_cons _ _ _ (der_51285 v h) (hints_cons _ _ _ (der_51286 v h) (hints_cons _ _ _ (der_51287 v h) (hints_cons _ _ _ (der_51291 v h) (hints_cons _ _ _ (der_51292 v h) (hints_cons _ _ _ (der_51293 v h) (hints_cons _ _ _ (der_51294 v h) (hints_cons _ _ _ (der_51295 v h) (hints_cons _ _ _ (der_51297 v h) (hints_cons _ _ _ (der_51298 v h) (hints_cons _ _ _ (der_51299 v h) (hints_cons _ _ _ (der_51300 v h) (hints_cons _ _ _ (der_51301 v h) (hints_cons _ _ _ (der_51302 v h) (hints_cons _ _ _ (der_51303 v h) (hints_cons _ _ _ (der_51304 v h) (hints_cons _ _ _ (der_51306 v h) (hints_cons _ _ _ (der_51307 v h) (hints_cons _ _ _ (der_51308 v h) (hints_cons _ _ _ (der_51309 v h) (hints_cons _ _ _ (der_51310 v h) (hints_cons _ _ _ (der_51311 v h) (hints_cons _ _ _ (der_51312 v h) (hints_cons _ _ _ (der_51313 v h) (hints_cons _ _ _ (der_51314 v h) (hints_cons _ _ _ (der_51321 v h) (hints_cons _ _ _ (der_51325 v h) (hints_cons _ _ _ (der_51326 v h) (hints_cons _ _ _ (der_51327 v h) (hints_cons _ _ _ (der_51328 v h) (hints_cons _ _ _ (der_51329 v h) (hints_cons _ _ _ (der_51330 v h) (hints_cons _ _ _ (der_51331 v h) (hints_cons _ _ _ (der_51332 v h) (hints_cons _ _ _ (der_51333 v h) (hints_cons _ _ _ (der_51334 v h) (hints_cons _ _ _ (der_51335 v h) (hints_cons _ _ _ (der_51337 v h) (hints_cons _ _ _ (der_51338 v h) (hints_cons _ _ _ (der_51340 v h) (hints_cons _ _ _ (der_51341 v h) (hints_cons _ _ _ (der_51343 v h) (hints_cons _ _ _ (der_51344 v h) (hints_cons _ _ _ (der_51345 v h) (hints_cons _ _ _ (der_51347 v h) (hints_cons _ _ _ (der_51348 v h) (hints_cons _ _ _ (der_51349 v h) (hints_cons _ _ _ (der_51350 v h) (hints_cons _ _ _ (der_51352 v h) (hints_cons _ _ _ (der_51353 v h) (hints_cons _ _ _ (der_51354 v h) (hints_cons _ _ _ (der_51359 v h) (hints_cons _ _ _ (der_51360 v h) (hints_cons _ _ _ (der_51363 v h) (hints_cons _ _ _ (der_51364 v h) (hints_cons _ _ _ (der_51365 v h) (hints_cons _ _ _ (der_51368 v h) (hints_cons _ _ _ (der_51371 v h) (hints_cons _ _ _ (der_51373 v h) (hints_cons _ _ _ (der_51374 v h) (hints_cons _ _ _ (der_51377 v h) (hints_cons _ _ _ (der_51378 v h) (hints_cons _ _ _ (der_51382 v h) (hints_cons _ _ _ (der_51383 v h) (hints_cons _ _ _ (der_51384 v h) (hints_cons _ _ _ (der_51385 v h) (hints_cons _ _ _ (der_51386 v h) (hints_cons _ _ _ (der_51388 v h) (hints_cons _ _ _ (der_51390 v h) (hints_cons _ _ _ (der_51392 v h) (hints_cons _ _ _ (der_51394 v h) (hints_cons _ _ _ (der_51395 v h) (hints_cons _ _ _ (der_51396 v h) (hints_cons _ _ _ (der_51397 v h) (hints_cons _ _ _ (der_51400 v h) (hints_cons _ _ _ (der_51401 v h) (hints_cons _ _ _ (der_51402 v h) (hints_cons _ _ _ (der_51403 v h) (hints_cons _ _ _ (der_51404 v h) (hints_cons _ _ _ (der_51405 v h) (hints_cons _ _ _ (der_51406 v h) (hints_cons _ _ _ (der_51408 v h) (hints_cons _ _ _ (der_51409 v h) (hints_cons _ _ _ (der_51410 v h) (hints_cons _ _ _ (der_51412 v h) (hints_cons _ _ _ (der_51413 v h) (hints_cons _ _ _ (der_51414 v h) (hints_cons _ _ _ (der_51416 v h) (hints_cons _ _ _ (der_51418 v h) (hints_cons _ _ _ (der_51420 v h) (hints_cons _ _ _ (der_51421 v h) (hints_cons _ _ _ (der_51422 v h) (hints_cons _ _ _ (der_51423 v h) (hints_cons _ _ _ (der_51424 v h) (hints_cons _ _ _ (der_51425 v h) (hints_cons _ _ _ (der_51426 v h) (hints_cons _ _ _ (der_51427 v h) (hints_cons _ _ _ (der_51428 v h) (hints_cons _ _ _ (der_51431 v h) (hints_cons _ _ _ (der_51432 v h) (hints_cons _ _ _ (der_51433 v h) (hints_cons _ _ _ (der_51434 v h) (hints_cons _ _ _ (der_51435 v h) (hints_cons _ _ _ (der_51437 v h) (hints_cons _ _ _ (der_51438 v h) (hints_cons _ _ _ (der_51439 v h) (hints_cons _ _ _ (der_51440 v h) (hints_cons _ _ _ (der_51441 v h) (hints_cons _ _ _ (der_51442 v h) (hints_cons _ _ _ (der_51443 v h) (hints_cons _ _ _ (der_51444 v h) (hints_cons _ _ _ (der_51445 v h) (hints_cons _ _ _ (der_51446 v h) (hints_cons _ _ _ (der_51447 v h) (hints_cons _ _ _ (der_51448 v h) (hints_cons _ _ _ (der_51449 v h) (hints_cons _ _ _ (der_51450 v h) (hints_cons _ _ _ (der_51451 v h) (hints_cons _ _ _ (der_51452 v h) (hints_cons _ _ _ (der_51453 v h) (hints_cons _ _ _ (der_51454 v h) (hints_cons _ _ _ (der_51455 v h) (hints_cons _ _ _ (der_51457 v h) (hints_cons _ _ _ (der_51458 v h) (hints_cons _ _ _ (der_51459 v h) (hints_cons _ _ _ (der_51460 v h) (hints_cons _ _ _ (der_51462 v h) (hints_cons _ _ _ (der_51467 v h) (hints_cons _ _ _ (der_51469 v h) (hints_cons _ _ _ (der_51472 v h) (hints_cons _ _ _ (der_51475 v h) (hints_cons _ _ _ (der_51476 v h) (hints_cons _ _ _ (der_51477 v h) (hints_cons _ _ _ (der_51479 v h) (hints_cons _ _ _ (der_51481 v h) (hints_cons _ _ _ (der_51482 v h) (hints_cons _ _ _ (der_51483 v h) (hints_cons _ _ _ (der_51484 v h) (hints_cons _ _ _ (der_51485 v h) (hints_cons _ _ _ (der_51486 v h) (hints_cons _ _ _ (der_51487 v h) (hints_cons _ _ _ (der_51488 v h) (hints_cons _ _ _ (der_51489 v h) (hints_cons _ _ _ (der_51490 v h) (hints_cons _ _ _ (der_51491 v h) (hints_cons _ _ _ (der_51493 v h) (hints_cons _ _ _ (der_51494 v h) (hints_cons _ _ _ (der_51495 v h) (hints_cons _ _ _ (der_51496 v h) (hints_cons _ _ _ (der_51497 v h) (hints_cons _ _ _ (der_51499 v h) (hints_cons _ _ _ (der_51502 v h) (hints_cons _ _ _ (der_51503 v h) (hints_cons _ _ _ (der_51506 v h) (hints_cons _ _ _ (der_51508 v h) (hints_cons _ _ _ (der_51516 v h) (hints_cons _ _ _ (der_51519 v h) (hints_cons _ _ _ (der_51520 v h) (hints_cons _ _ _ (der_51522 v h) (hints_cons _ _ _ (der_51523 v h) (hints_cons _ _ _ (der_51524 v h) (hints_cons _ _ _ (der_51526 v h) (hints_cons _ _ _ (der_51527 v h) (hints_cons _ _ _ (der_51528 v h) (hints_cons _ _ _ (der_51529 v h) (hints_cons _ _ _ (der_51530 v h) (hints_cons _ _ _ (der_51532 v h) (hints_cons _ _ _ (der_51534 v h) (hints_cons _ _ _ (der_51535 v h) (hints_cons _ _ _ (der_51540 v h) (hints_cons _ _ _ (der_51541 v h) (hints_cons _ _ _ (der_51542 v h) (hints_cons _ _ _ (der_51543 v h) (hints_cons _ _ _ (der_51551 v h) (hints_cons _ _ _ (der_51557 v h) (hints_cons _ _ _ (der_51559 v h) (hints_cons _ _ _ (der_51561 v h) (hints_cons _ _ _ (der_51562 v h) (hints_cons _ _ _ (der_51568 v h) (hints_cons _ _ _ (der_51569 v h) (hints_cons _ _ _ (der_51571 v h) (hints_cons _ _ _ (der_51572 v h) (hints_cons _ _ _ (der_51575 v h) (hints_cons _ _ _ (der_51576 v h) (hints_cons _ _ _ (der_51577 v h) (hints_cons _ _ _ (der_51578 v h) (hints_cons _ _ _ (der_51579 v h) (hints_cons _ _ _ (der_51581 v h) (hints_cons _ _ _ (der_51582 v h) (hints_cons _ _ _ (der_51583 v h) (hints_cons _ _ _ (der_51584 v h) (hints_cons _ _ _ (der_51585 v h) (hints_cons _ _ _ (der_51587 v h) (hints_cons _ _ _ (der_51588 v h) (hints_cons _ _ _ (der_51589 v h) (hints_cons _ _ _ (der_51590 v h) (hints_cons _ _ _ (der_51591 v h) (hints_cons _ _ _ (der_51592 v h) (hints_cons _ _ _ (der_51593 v h) (hints_cons _ _ _ (der_51594 v h) (hints_cons _ _ _ (der_51595 v h) (hints_cons _ _ _ (der_51596 v h) (hints_cons _ _ _ (der_51597 v h) (hints_cons _ _ _ (der_51598 v h) (hints_cons _ _ _ (der_51600 v h) (hints_cons _ _ _ (der_51602 v h) (hints_cons _ _ _ (der_51603 v h) (hints_cons _ _ _ (der_51607 v h) (hints_cons _ _ _ (der_51609 v h) (hints_cons _ _ _ (der_51610 v h) (hints_cons _ _ _ (der_51611 v h) (hints_cons _ _ _ (der_51612 v h) (hints_cons _ _ _ (der_51615 v h) (hints_cons _ _ _ (der_51620 v h) (hints_cons _ _ _ (der_51621 v h) (hints_cons _ _ _ (der_51622 v h) (hints_cons _ _ _ (der_51623 v h) (hints_cons _ _ _ (der_51624 v h) (hints_cons _ _ _ (der_51626 v h) (hints_cons _ _ _ (der_51627 v h) (hints_cons _ _ _ (der_51628 v h) (hints_cons _ _ _ (der_51629 v h) (hints_cons _ _ _ (der_51630 v h) (hints_cons _ _ _ (der_51631 v h) (hints_cons _ _ _ (der_51634 v h) (hints_cons _ _ _ (der_51636 v h) (hints_cons _ _ _ (der_51639 v h) (hints_cons _ _ _ (der_51640 v h) (hints_cons _ _ _ (der_51642 v h) (hints_cons _ _ _ (der_51643 v h) (hints_cons _ _ _ (der_51644 v h) (hints_cons _ _ _ (der_51645 v h) (hints_cons _ _ _ (der_51646 v h) (hints_cons _ _ _ (der_51647 v h) (hints_cons _ _ _ (der_51648 v h) (hints_cons _ _ _ (der_51649 v h) (hints_cons _ _ _ (der_51650 v h) (hints_cons _ _ _ (der_51651 v h) (hints_cons _ _ _ (der_51652 v h) (hints_cons _ _ _ (der_51653 v h) (hints_cons _ _ _ (der_51654 v h) (hints_cons _ _ _ (der_51655 v h) (hints_cons _ _ _ (der_51656 v h) (hints_cons _ _ _ (der_51657 v h) (hints_cons _ _ _ (der_51659 v h) (hints_cons _ _ _ (der_51660 v h) (hints_cons _ _ _ (der_51661 v h) (hints_cons _ _ _ (der_51662 v h) (hints_cons _ _ _ (der_51663 v h) (hints_cons _ _ _ (der_51664 v h) (hints_cons _ _ _ (der_51665 v h) (hints_cons _ _ _ (der_51667 v h) (hints_cons _ _ _ (der_51668 v h) (hints_cons _ _ _ (der_51669 v h) (hints_cons _ _ _ (der_51670 v h) (hints_cons _ _ _ (der_51671 v h) (hints_cons _ _ _ (der_51674 v h) (hints_cons _ _ _ (der_51675 v h) (hints_cons _ _ _ (der_51676 v h) (hints_cons _ _ _ (der_51678 v h) (hints_cons _ _ _ (der_51679 v h) (hints_cons _ _ _ (der_51681 v h) (hints_cons _ _ _ (der_51685 v h) (hints_cons _ _ _ (der_51691 v h) (hints_cons _ _ _ (der_51694 v h) (hints_cons _ _ _ (der_51695 v h) (hints_cons _ _ _ (der_51696 v h) (hints_cons _ _ _ (der_51697 v h) (hints_cons _ _ _ (der_51699 v h) (hints_cons _ _ _ (der_51700 v h) (hints_cons _ _ _ (der_51701 v h) (hints_cons _ _ _ (der_51703 v h) (hints_cons _ _ _ (der_51705 v h) (hints_cons _ _ _ (der_51707 v h) (hints_cons _ _ _ (der_51711 v h) (hints_cons _ _ _ (der_51712 v h) (hints_cons _ _ _ (der_51713 v h) (hints_cons _ _ _ (der_51714 v h) (hints_cons _ _ _ (der_51715 v h) (hints_cons _ _ _ (der_51716 v h) (hints_cons _ _ _ (der_51718 v h) (hints_cons _ _ _ (der_51719 v h) (hints_cons _ _ _ (der_51721 v h) (hints_cons _ _ _ (der_51722 v h) (hints_cons _ _ _ (der_51723 v h) (hints_cons _ _ _ (der_51725 v h) (hints_cons _ _ _ (der_51726 v h) (hints_cons _ _ _ (der_51727 v h) (hints_cons _ _ _ (der_51728 v h) (hints_cons _ _ _ (der_51729 v h) (hints_cons _ _ _ (der_51730 v h) (hints_cons _ _ _ (der_51737 v h) (hints_cons _ _ _ (der_51743 v h) (hints_cons _ _ _ (der_51744 v h) (hints_cons _ _ _ (der_51745 v h) (hints_cons _ _ _ (der_51746 v h) (hints_cons _ _ _ (der_51747 v h) (hints_cons _ _ _ (der_51759 v h) (hints_cons _ _ _ (der_51760 v h) (hints_cons _ _ _ (der_51761 v h) (hints_cons _ _ _ (der_51763 v h) (hints_cons _ _ _ (der_51764 v h) (hints_cons _ _ _ (der_51765 v h) (hints_cons _ _ _ (der_51766 v h) (hints_cons _ _ _ (der_51767 v h) (hints_cons _ _ _ (der_51768 v h) (hints_cons _ _ _ (der_51769 v h) (hints_cons _ _ _ (der_51771 v h) (hints_cons _ _ _ (der_51772 v h) (hints_cons _ _ _ (der_51774 v h) (hints_cons _ _ _ (der_51775 v h) (hints_cons _ _ _ (der_51776 v h) (hints_cons _ _ _ (der_51777 v h) (hints_cons _ _ _ (der_51778 v h) (hints_cons _ _ _ (der_51779 v h) (hints_cons _ _ _ (der_51781 v h) (hints_cons _ _ _ (der_51784 v h) (hints_cons _ _ _ (der_51785 v h) (hints_cons _ _ _ (der_51786 v h) (hints_cons _ _ _ (der_51787 v h) (hints_cons _ _ _ (der_51788 v h) (hints_cons _ _ _ (der_51790 v h) (hints_cons _ _ _ (der_51791 v h) (hints_cons _ _ _ (der_51792 v h) (hints_cons _ _ _ (der_51800 v h) (hints_cons _ _ _ (der_51801 v h) (hints_cons _ _ _ (der_51802 v h) (hints_cons _ _ _ (der_51803 v h) (hints_cons _ _ _ (der_51804 v h) (hints_cons _ _ _ (der_51805 v h) (hints_cons _ _ _ (der_51806 v h) (hints_cons _ _ _ (der_51807 v h) (hints_cons _ _ _ (der_51809 v h) (hints_cons _ _ _ (der_51812 v h) (hints_cons _ _ _ (der_51813 v h) (hints_cons _ _ _ (der_51814 v h) (hints_cons _ _ _ (der_51815 v h) (hints_cons _ _ _ (der_51816 v h) (hints_cons _ _ _ (der_51817 v h) (hints_cons _ _ _ (der_51818 v h) (hints_cons _ _ _ (der_51819 v h) (hints_cons _ _ _ (der_51820 v h) (hints_cons _ _ _ (der_51822 v h) (hints_cons _ _ _ (der_51823 v h) (hints_cons _ _ _ (der_51825 v h) (hints_cons _ _ _ (der_51826 v h) (hints_cons _ _ _ (der_51827 v h) (hints_cons _ _ _ (der_51828 v h) (hints_cons _ _ _ (der_51829 v h) (hints_cons _ _ _ (der_51830 v h) (hints_cons _ _ _ (der_51832 v h) (hints_cons _ _ _ (der_51833 v h) (hints_cons _ _ _ (der_51834 v h) (hints_cons _ _ _ (der_51835 v h) (hints_cons _ _ _ (der_51836 v h) (hints_cons _ _ _ (der_51838 v h) (hints_cons _ _ _ (der_51839 v h) (hints_cons _ _ _ (der_51840 v h) (hints_cons _ _ _ (der_51843 v h) (hints_cons _ _ _ (der_51845 v h) (hints_cons _ _ _ (der_51847 v h) (hints_cons _ _ _ (der_51848 v h) (hints_cons _ _ _ (der_51849 v h) (hints_cons _ _ _ (der_51850 v h) (hints_cons _ _ _ (der_51851 v h) (hints_cons _ _ _ (der_51852 v h) (hints_cons _ _ _ (der_51854 v h) (hints_cons _ _ _ (der_51856 v h) (hints_cons _ _ _ (der_51857 v h) (hints_cons _ _ _ (der_51858 v h) (hints_cons _ _ _ (der_51861 v h) (hints_cons _ _ _ (der_51862 v h) (hints_cons _ _ _ (der_51864 v h) (hints_cons _ _ _ (der_51867 v h) (hints_cons _ _ _ (der_51868 v h) (hints_cons _ _ _ (der_51872 v h) (hints_cons _ _ _ (der_51873 v h) (hints_cons _ _ _ (der_51874 v h) (hints_cons _ _ _ (der_51875 v h) (hints_cons _ _ _ (der_51876 v h) (hints_cons _ _ _ (der_51877 v h) (hints_cons _ _ _ (der_51878 v h) (hints_cons _ _ _ (der_51879 v h) (hints_cons _ _ _ (der_51880 v h) (hints_cons _ _ _ (der_51881 v h) (hints_cons _ _ _ (der_51882 v h) (hints_cons _ _ _ (der_51883 v h) (hints_cons _ _ _ (der_51884 v h) (hints_cons _ _ _ (der_51885 v h) (hints_cons _ _ _ (der_51886 v h) (hints_cons _ _ _ (der_51887 v h) (hints_cons _ _ _ (der_51888 v h) (hints_cons _ _ _ (der_51889 v h) (hints_cons _ _ _ (der_51890 v h) (hints_cons _ _ _ (der_51891 v h) (hints_cons _ _ _ (der_51892 v h) (hints_cons _ _ _ (der_51895 v h) (hints_cons _ _ _ (der_51896 v h) (hints_cons _ _ _ (der_51898 v h) (hints_cons _ _ _ (der_51901 v h) (hints_cons _ _ _ (der_51902 v h) (hints_cons _ _ _ (der_51903 v h) (hints_cons _ _ _ (der_51904 v h) (hints_cons _ _ _ (der_51905 v h) (hints_cons _ _ _ (der_51910 v h) (hints_cons _ _ _ (der_51956 v h) (hints_cons _ _ _ (der_51957 v h) (hints_cons _ _ _ (der_51958 v h) (hints_cons _ _ _ (der_51959 v h) (hints_cons _ _ _ (der_51960 v h) (hints_cons _ _ _ (der_51961 v h) (hints_cons _ _ _ (der_51962 v h) (hints_cons _ _ _ (der_51963 v h) (hints_cons _ _ _ (der_51964 v h) (hints_cons _ _ _ (der_51965 v h) (hints_cons _ _ _ (der_51966 v h) (hints_cons _ _ _ (der_51968 v h) (hints_cons _ _ _ (der_51970 v h) (hints_cons _ _ _ (der_51971 v h) (hints_cons _ _ _ (der_51982 v h) (hints_cons _ _ _ (der_51987 v h) (hints_cons _ _ _ (der_51990 v h) (hints_cons _ _ _ (der_51999 v h) (hints_cons _ _ _ (der_52001 v h) (hints_cons _ _ _ (der_52003 v h) (hints_cons _ _ _ (der_52004 v h) (hints_cons _ _ _ (der_52014 v h) (hints_cons _ _ _ (der_52015 v h) (hints_cons _ _ _ (der_52017 v h) (hints_cons _ _ _ (der_52018 v h) (hints_cons _ _ _ (der_52019 v h) (hints_cons _ _ _ (der_52020 v h) (hints_cons _ _ _ (der_52022 v h) (hints_cons _ _ _ (der_52023 v h) (hints_cons _ _ _ (der_52026 v h) (hints_cons _ _ _ (der_52028 v h) (hints_cons _ _ _ (der_52031 v h) (hints_cons _ _ _ (der_52032 v h) (hints_cons _ _ _ (der_52035 v h) (hints_cons _ _ _ (der_52036 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix048 := prefix047 ++ chunk048
theorem prefix_sound048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix048, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound047 v h c hc
  · exact chunk_sound048 v h c hc
end Percolation.NReplay
